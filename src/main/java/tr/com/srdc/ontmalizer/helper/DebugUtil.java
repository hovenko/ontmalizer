package tr.com.srdc.ontmalizer.helper;

import org.apache.commons.lang3.builder.ReflectionToStringBuilder;
import org.apache.commons.lang3.builder.ToStringStyle;

public class DebugUtil {
	public static String toS(Object in) {
		return "\n" + ReflectionToStringBuilder.toString(in, ToStringStyle.MULTI_LINE_STYLE, true);
	}
}

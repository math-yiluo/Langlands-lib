# Compact right smoothing of continuous moderate cuspidal functions

`adelicModerateCuspidalSmoothing` works with the actual adelic convolution and its Haar measure. For a continuous, rationally invariant, moderate function with all proper constant terms zero, a compact smooth test kernel gives a smooth finite-level function with the same rational invariance and zero proper constant terms.

Differentiation moves each real orbit derivative to a derivative of the kernel. Successive applications of the differentiation theorem represent each word by convolution with one compact test kernel. If the original function is bounded by \(CH(x)^r\), submultiplicativity bounds \(H(xa)^r\) by \(H(x)^r B^r\) on the support of the differentiated kernel. The derivative-dependent constant includes its integral norm. The exponent \(r\) is common to all words and comes from the original function bound.

For the constant-term comparison, the iterated integrand descends continuously to the rational radical quotient in its radical variable. Its support is contained in the product of the compact radical quotient and the compact support of the test kernel. Fubini gives the equality of the two orders of averaging with their original measures. This proves preservation of cuspidality without any assumptions on derivatives of the input function.

This is a derived implementation of the smooth-convolution step of Mœglin–Waldspurger I.3.4, pp. 45–46, using the published adelic right-convolution differentiation theorem.

- `moeglin-waldspurger-1995-cuspidal-components`, `ce20e97e0e7b5008124763a26598dd024c66c926069ca07e92aa24afe91999f1`, 05.3_pp_40_48_Cuspidal_components.pdf, I.3.4, pp. 45–46, compact right smoothing.

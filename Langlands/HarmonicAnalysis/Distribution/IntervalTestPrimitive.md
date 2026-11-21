# Compactly supported primitives in one product coordinate

Integrating a smooth test on \(U\times(a,b)\) in its real interval
coordinate gives a smooth test on \(U\). Its support lies in the
projection of the original compact support to \(U\). Both constructors
use Mathlib's oriented interval integral, which is identically zero
when the test's coefficient space is incomplete.

If this integral is zero, integration from \(a\) to the interval
coordinate gives a compactly supported smooth test on the
same product. The projection of the test support to the interval
lies in a strictly smaller closed interval. The integral is zero
to its left because the integrand vanishes there, and zero to its
right because the total integral is zero. Joint smoothness follows
from smoothness of parameter-dependent interval integration.
When the coefficient space is complete, differentiating this
integral in the interval direction recovers the original test.

For tests with a complete coefficient space, a continuous linear functional
that annihilates interval derivatives factors through the slice integral.
Choose a scalar interval test of integral
one. Subtract the product of this scalar test and the integrated
parameter test from the original test. The difference has zero
interval integral, so it is a derivative and the functional
annihilates it. This internal result is the
one-coordinate step for passing to orbit density.

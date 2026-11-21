# Integration over the orbit coordinate of a product test

Use the coordinate order `((orbit, slice), normal)` for a chart test. A scalar orbit test can multiply a test in the slice and normal coordinates. Inserting it gives a continuous linear map of test spaces. The induced slice distribution inherits an upper bound on transverse order from the original product distribution, since transverse differentiation acts only on the slice test.

Reordering the product makes the orbit the last coordinate for the existing fiber integral on test functions. The transverse derivative of an integrated test equals the orbit integral of that derivative. An orbit test of integral one makes integration a left inverse of insertion. These formulas use Mathlib's Bochner integral on the specified locally finite measure.

The factorization assumes that the orbit open is the image under a continuous real-linear equivalence \(b\) of the product \((a,c)^d\), where every coordinate uses the same interval and \(a<c\). If the distribution kills all constant derivatives in the orbit direction, pulling back to this product gives the box factorization. The Haar measure on the orbit space is the pushforward under \(b\) of Lebesgue measure on all of \(\mathbb{R}^d\). The slice distribution may be defined by inserting any orbit test of integral one for that measure.

This internal factorization connects the chart derivative and the leading transverse coefficient calculations.

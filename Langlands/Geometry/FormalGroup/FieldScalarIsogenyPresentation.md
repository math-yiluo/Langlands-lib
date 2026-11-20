# Integral numerators of tensor quasi-isogenies over a field

Drinfeld 1976, §2 A, printed p. 109 (PDF p. 3), defines quasi-isogenies as
invertible elements in the tensor Hom. Harris 1997, Appendix, printed p. 112
(PDF p. 38), takes sections of the rational Hom sheaf that become isogenies
after multiplication by a power of the rational prime \(p\) locally. In the
mixed-characteristic local-field setting \(p=u\pi^r\) with \(u\) a unit and \(r\)
the ramification index, so a denominator given by a power of \(\pi\) can also
be cleared using a power of \(p\).

The global numerator construction here is a derived result for a DVR \(O\)
with uniformizer \(\pi\) and fraction field \(F\), an \(O\)-algebra field \(k\),
and two formal \(O\)-modules over \(k\) that satisfy `IsPiDivisible π`. This
divisibility supplies fppf local lifts and represented kernels for the scalar
powers on each module.

The tensor Hom is the localization of the integral Hom at the nonzero elements
of the discrete valuation ring. A unit times a uniformizer power describes each
denominator, and multiplying by the inverse unit gives an integral numerator
with a uniformizer-power denominator. The equality criterion for localization
reduces injectivity to cancellation of an integral scalar-power map by fppf
local lifting on the source's nilpotent points.

For an invertible tensor, clear denominators on its actual inverse as well.
Bilinearity of composition and integral injectivity identify both integral
composites with scalar powers. The target composite gives fppf local lifts
through the numerator. The source composite embeds its actual kernel in the
represented scalar-power kernel. `KernelQuotient` corepresents the subkernel
by imposing the numerator's coordinate equations on that kernel algebra.
The quotient is finite and is projective over the coefficient field.

`QuasiIsogeny.isIsogeny_of_clearsDenominator` applies to any integral numerator
of the invertible tensor. `QuasiIsogeny.scalarIsogenyPresentation` supplies
such a numerator with its isogeny proof and its exact tensor equality.

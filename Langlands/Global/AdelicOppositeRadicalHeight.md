# Regular parameter decay on an opposite adelic radical

In `exists_oppositeRationalHeightBound`, the opposite radical maps by an
open immersion into the flag quotient. Embed the quotient in projective
space using a Chevalley line whose stabilizer is the parabolic. The
projective section charts for the open immersion recover the opposite
radical point from the homogeneous coordinates. Polynomial height
bounds for the matrix and inverse matrix entries on finitely many
charts give one bound for the adelic matrix height of each principal
opposite point. The height on the right is the projective height of
its rational parabolic coset, which uses the inverse orbit vector.

`IsIwasawaCompact.exists_decay_on_oppositeRadical` uses the Library's
regular parameter decay on rational parabolic cosets with an exponent
large enough for this polynomial bound. A compact fundamental set
for the opposite unipotent group lets each adelic opposite point be
written as a principal opposite point times an element of a fixed
compact set. Compact right translation bounds the change of the
height power. Submultiplicativity bounds the resulting adelic matrix
height by a fixed multiple of the matrix height at the principal
point. Thus sufficiently regular height powers decay faster than
any prescribed power of the matrix height on the opposite radical.

The argument is internal. It uses the polynomial height method of
`AdelicEisensteinParameterDecay` and the regular region of Mœglin and
Waldspurger, *Spectral decomposition and Eisenstein series*, II.1.5,
p. 85, registered as `moeglin-waldspurger-1995-spectral-decomposition`,
`06.1_pp_78_100_Definitions.pdf`, SHA-256
`948dbfd356c2f068c1dc793a52e4c700334eb5236b740f1c775da535b747111c`.

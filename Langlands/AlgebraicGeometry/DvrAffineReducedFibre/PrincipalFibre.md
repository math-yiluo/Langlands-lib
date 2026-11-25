# Reducedness of principal fibres with normal local rings

Conrad's appendix to Prasad–Yu, *On quasi-reductive group schemes*,
author preprint, Remark A.7 (p. 30), uses Serre's criteria to pass
from generic smoothness to geometrically reduced fibres for flat
normal models over a DVR. The affine lemma here addresses the
underlying reducedness of a quotient by a regular element.

The definition `localizationAtPrimeQuotientEquiv` compares the
localization of a quotient at a prime with the quotient of the local
ring at its inverse image. This is an auxiliary algebra equivalence.
The quotient of the local ring is a localization of the original
quotient at the image of the denominator monoid. Surjectivity of the
quotient map identifies that image with the complement of the given
prime, so uniqueness of localization gives the equivalence.

If the quotient has a nonzero nilpotent, its annihilator lies in
an associated prime of the quotient. Localizing at that prime, the
maximal ideal is the annihilator of an element of the local quotient.
For a quotient by a regular element `a`, this identifies the maximal
ideal with the elements `r` for which `r * b / a` is in the local ring,
where `b` lifts an element with maximal annihilator. Multiplication
by `b / a` cannot preserve the maximal ideal, since the determinant
trick would make `b / a` integral and hence in the integrally closed
local domain. Some `r` in the maximal ideal therefore has `r * b / a`
a unit. After scaling `r` this product is `1`, so `r` generates the
maximal ideal.

The local ring is a PID by the Noetherian local domain criterion.
Its only nonzero prime is its maximal ideal, so the chosen associated
prime is minimal over `(a)` in the original ring. The nilpotent
maps to zero in the reduced quotient at that prime. Clearing a
denominator then puts an element outside the associated prime in
the original annihilator, a contradiction.

The minimal primes of the principal quotient correspond to the primes
minimal over `(a)` in the original ring. The equivalence identifies
the local rings used in the two formulations of the reducedness test.

The registered source is `prasad-yu-2006-quasi-reductive-author-preprint`,
SHA-256 `138d931a21fa522d97449c77acf429918826b1ef649be940d4721d616a1fc73b`.

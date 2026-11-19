# The toral marginal of the complex unipotent quotient measure

`ComplexIwasawaToralMeasureStatement` gives the pushforward of `D.measure`
under the logarithmic Iwasawa coordinate `alphaQ`, for every
`D : ComplexQuotientMeasureData t`. On measurable nonnegative functions
of the toral coordinate it evaluates the integral against
\(\kappa \exp(L(y))\,dy\), where \(\kappa\) is a finite nonnegative constant
and \(L\) is a continuous real linear form.

The proof lifts compactly supported toral and unipotent test functions
through the ordered Iwasawa homeomorphism. Their product on the group has
compact support because the unitary factor is compact. The Weil formula
expresses its integral as the toral test integral against the quotient
measure times the unipotent test integral. Left multiplication by a
positive diagonal translates the toral coordinate and conjugates the
unipotent coordinate. Left invariance of the group Haar measure then
shows that each toral translate scales the pushforward by a positive
factor. Positivity comes from choosing a nonnegative unipotent bump
with value one at the identity, which is fixed by conjugation.

Compact preimages under `alphaQ` give finiteness on compact sets. The
quotient measure and its toral pushforward are nonzero. The real
logarithm-space lemmas in `RealIwasawaMeasure` identify the positive
translation factor with the exponential of a linear form and recover the
Lebesgue density. The resulting formula uses the exact quotient measure
specified by `D`.

The result formalizes the toral integration step of Jacquet 2009, §3.1,
p. 14, in the proof of Lemma 3.5, as used in §5.1, p. 32. The proposition
supplies the marginal after integration over the unitary factor.
Its linear form is existential and suffices for polynomial height
majorants in the local convergence proof.

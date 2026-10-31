# Rank-one determinant-twist transport of full gamma certificates

Author: Worker 458.

The theorem `Langlands.RankinSelberg.rankOneGammaTwist.{uF,uV}` proves the
unchanged Library proposition `Langlands.RankinSelberg.RankOneGammaTwistStatement`.
It equates the full p-adic symmetric gamma-factor relations for the pairs
`(π ⊗ χ∘det, 1)` and `(π, χ)`, using the same additive character, supplied
additive Haar measure, and rational function `G`. Candidate rank is `n+1`
and test rank is one, including `n=0`. No smoothness, continuity of `χ`,
irreducibility, central character on the original carrier, self-dual measure,
or analytic existence premise is added.

## Implemented proof

The paired helper modules contain the following internal derivations.

`RankOneGammaTwistAlgebra` proves a determinant recurrence for the actual long
Weyl matrix by expanding its first row. With the determinant of the actual
block Weyl matrix and inverse transpose, this gives

`det(w_(n+1) · (g · blockWeylAt 0 n)^ι) = (-1)^n · det(g)⁻¹`.

The same underlying linear functional is a Whittaker functional on `π` and
its twist, using the published `twistFunctional`/`untwistFunctional` API.
Every complex linear form on the rank-one test carrier is an inverse
Whittaker functional, since its upper-unipotent group is trivial. Computing
actual coefficient functions gives minus-one scalars `1` and `χ(-1)` for
the two tests. These calculations do not require nonzero functionals.

`RankOneGammaTwistIntegrals` compares coefficient products at matrices with
the same determinant. The published determinant identity for the unequal-rank
block matrix then identifies every forward integral, for every rectangular
block and measure. For the actual dual integral it includes the right
translation by `blockWeylAt 0 n` after `firstDualFunction`, and the rank-one
`secondDualFunction`. The dual integral on the twisted side is `χ(-1)^n`
times the dual integral on the original side. The scalar passes through
both total Bochner integrals without an integrability premise. When both
ranks are one, the long Weyl element is one and both forward and dual
integrals agree for every Schwartz--Bruhat test.

`RankOneGammaTwistEquations` uses surjectivity of the coefficient maps to
cover every model vector. Equality of the forward rational-value families
retains every nonzero-continuation witness. Multiplication of a continuation
by a constant multiplies its rational function by the same constant.
The published `GammaFunctionalEquation.negOne_swap` transports the equation
on its full denominator domain, using `χ(-1)^2=1`. The square identity also
recovers the original dual integral in the reverse direction. For a nonzero
test functional, uniqueness identifies the minus-one scalar of any supplied
unequal-rank equation with the one computed above. In the rank-one equal-rank
case the exponent is zero; the same Fourier partner and the same two rational
continuations serve on both sides, with the unchanged supplied `ψ` and `ν`.

The entry module lifts these fixed-functional equivalences to the full
relations. It retains the compatible-measure existence clause verbatim,
transports nonzero functionals while retaining their underlying linear maps,
and applies the equation equivalence to every compatible quotient measure
and every pair of nonzero functionals. Splitting on `0<n` covers both branches
of `IsPairGammaFactor`; substituting `n=0` accounts for its equality cast.
Finally the proof installs the canonical p-adic topology and measurable
structures and unfolds the symmetric relation, whose rank-order test is
always `0≤n`.

## Provenance and limits

This is an internal derivation from the JPSS integral definitions, not a
numbered theorem asserting gamma existence. The original source is
H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, American Journal of Mathematics 105 (1983), 367–464,
registered as `jpss-1983-rankin-selberg`. Relevant passages are (0.3),
printed p.376 (PDF 11); (2.1), pp.385–386 (PDF 20–21); (2.4), p.387
(PDF 22); and Theorem (2.7)(iii), p.391 (PDF 26). These give the Weyl,
inverse-transpose, dual-function, block-translation and central-sign
conventions used in the Library. The statement companion supplies the
source file and its fingerprint. No project errata file for this source
was present. No Section 7 or later multiplicativity result is used.

The result transports a supplied certificate in either direction. It does
not assert that a certificate exists and defines no new gamma factor.

# Pair factors of spherical representations

Author: Worker 4891.

This module computes the Rankin–Selberg pair L-polynomial and pair epsilon factor of
two spherical (unramified) irreducible representations of `GL_(r+1)(F)` and
`GL_(t+1)(F)` over a `p`-adic field `F`. The factors are the Library's
classification-defined ones: `RankinSelberg.IsLanglandsPairLPolynomial`, which
quantifies over tempered Langlands data, and `RankinSelberg.IsLanglandsPairEpsilonFactor`,
which quantifies over essentially square-integrable Langlands data (Henniart 2002,
Section 2.8). The results are the unramified computation of Cogdell 2004,
Theorem 3.3 (printed page 215): if the spherical representations have Satake
parameters `z_1, …, z_(r+1)` and `z'_1, …, z'_(t+1)`, then
`L(s, π × π') = ∏_(i,j) (1 - z_i z'_j q^(-s))^(-1)`, and, for an additive character
of conductor zero and the self-dual measure, `ε(s, π × π', ψ) = 1`.

Throughout, `F.Carrier` and `GL_n(F)` carry the canonical topology of the `p`-adic
field, as in the Library's other local modules.

## Rank-one unramified blocks

- `unramifiedBlock F z` is the rank-one representation `GL_1(F) → ℂˣ`,
  `g ↦ χ_z(det g)`, of the unramified character `χ_z` with `χ_z(ϖ) = z`
  (`Unramified.character F z`). It is the object of the Library's
  `rankOneSupercuspidalObject`, so it is irreducible and supercuspidal.
- `unramifiedBlock_isEssentiallySquareIntegrable`: by the published
  `RankinSelberg.supercuspidal_isEssentiallySquareIntegrable`.
- `norm_eq_rpow_unitaryExponent`: every unitary exponent `α` of the block
  (`UnitaryExponentData` for `|det|`) satisfies `‖z‖ = |ϖ|^α`. The uniformizer
  `ϖ ∈ GL_1(F)` acts by the scalar `z`, and the published
  `unitaryExponentScalarNorm` gives `‖z‖ = |det ϖ|^α`.
- `character_mul`, `multiplicativeConductor_character`, `lPolynomial_character`:
  `χ_w χ_(w') = χ_(w w')`, an unramified character has conductor zero, and Tate's
  L-polynomial `LocalFactor.PadicAbelian.lPolynomial` of `χ_w` is `1 - w X`.
- `unramifiedBlock_lPolynomial_eq`: the pair L-polynomial of the blocks of `w` and
  `w'` is `1 - w w' X`. The published `isPadicPairLPolynomial_of_rankOneCharacterEquiv`
  identifies the JPSS polynomial of two rank-one characters with Tate's polynomial
  of their product; uniqueness of the polynomial does the rest.
- `unramifiedBlock_epsilonFactor_eq`: if `ψ` has additive conductor zero and `ν` is
  self-dual, the pair epsilon factor of the two blocks is `(1, 0)`, that is
  coefficient `1` and exponent `0`. The published
  `isPadicPairEpsilonFactor_rankOneCharacterEquiv_gauss` gives the epsilon factor
  as Tate's coefficient and exponent of `χ_w χ_(w')`. The exponent is the sum of the
  two conductors, `0 + 0`. The coefficient is Tate's epsilon at `s = 0`, which is `1`
  by the published `HeckeFunctionalEquation.epsilon_eq_one_of_conductors_eq_zero`.

## The square-integrable datum of a spherical representation

- `unramifiedDatum F z hz`, for `z : Fin (r + 1) → ℂˣ` with weakly increasing norms,
  is the essentially square-integrable Langlands datum on the Borel shape
  `borelShape r` with blocks `unramifiedBlock F (z i)`. The unitary exponents are
  chosen by the published `nonempty_unitaryExponentData`. They are weakly
  decreasing because `‖z_i‖ = |ϖ|^(α_i)` with `0 < |ϖ| < 1`.
- `unramifiedDatumInducedEquiv`: its induced representation is the normalized
  principal series `Unramified.principalSeriesOfTuple F z`. Block by block, the
  character line on `ULift ℂ` is equivalent to the character on `ℂ`.
- `exists_unramifiedDatum_isLanglandsQuotient`: if the object `A` has spherical
  spectrum `s` and `J` is equivalent to `A`, then for some ordering `z` of `s` with
  weakly increasing norms, `J` is a Langlands quotient of `unramifiedDatum F z`. The
  published `sphericalTemperedStandardModule` gives a tempered datum whose
  standard module is equivalent to the principal series of such a `z` and has `J`
  as irreducible quotient. Composing with `unramifiedDatumInducedEquiv` gives the
  quotient map from the induced representation of `unramifiedDatum F z`.

## Pair factors

- `unramifiedDatum_lPolynomial_eq`: if `J` and `J'` are Langlands quotients of
  `unramifiedDatum F z` and `unramifiedDatum F z'`, then their pair L-polynomial for
  a self-dual measure is `∏ i, ∏ j, (1 - z_i z'_j X)`. The published
  `RankinSelberg.squareIntegrableDataLFactor` (JPSS 1983, Theorem (9.5), in
  Henniart's product form) writes the L-polynomial as the double product of the
  block-pair polynomials. Each of these is `1 - z_i z'_j X` by
  `unramifiedBlock_lPolynomial_eq`, and uniqueness identifies the given polynomial.
- `unramifiedDatum_epsilonFactor_eq`: under the same hypotheses, with `ψ` of
  additive conductor zero, the pair epsilon factor is `(1, 0)`. By definition, the
  epsilon factor equals the epsilon product of the block pairs of every pair of
  presenting data, in particular of `unramifiedDatum F z` and `unramifiedDatum F z'`.
  Every block factor is `(1, 0)` by `unramifiedBlock_epsilonFactor_eq`, so the
  product is `(1, 0)`.

No hypothesis on unitarity, genericity or the central character is used, and the
universes `uF` (field) and `uA` (block carriers) are arbitrary.

## References

- J. W. Cogdell, *Analytic theory of L-functions for `GL_n`*, in J. Bernstein and
  S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
  197-228 (Library source `cogdell-2004-analytic-theory-gln`), Theorem 3.3, printed
  page 215.
- H. Jacquet, I. I. Piatetski-Shapiro, J. A. Shalika, *Rankin–Selberg convolutions*,
  Amer. J. Math. 105 (1983), 367-464 (`jpss-1983-rankin-selberg`), Theorem (9.5).
- G. Henniart, *Une caractérisation de la correspondance de Langlands locale pour
  GL(n)*, Bull. Soc. Math. France 130 (2002), 587-602
  (`henniart-2002-characterization`), Section 2.8.

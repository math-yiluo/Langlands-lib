# The functional-equation exponent is the conductor

## Setting

`K` is a `p`-adic field with its canonical topology, valuation and measurable structure (local
instances as in the related proof modules). `ψ` is a `UnitaryAdditiveCharacter K.Carrier`
and `ν` an `AdditiveHaarMeasure K.Carrier`. `Conductor.HasIntegerConductor ψ` (Library) says
that `ψ` has conductor `𝔬_K`. `IsSelfDual ψ ν` (Library) says that `ν` is self-dual for `ψ`.
`GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData K ψ ν σ P PDual c a` is the
Library's Godement–Jacquet functional equation for a representation `σ` of `GL_{n+1}(K)` with
Euler polynomials `P`, `PDual`, unit `c` and exponent `a`.
`RankinSelberg.rationalGammaExpression δ c a P PDual` is the Library's rational function
`c X^a · P(X) / PDual(δ / X)` in the variable `X = q^{-s}` (here `δ` is the residue reflection
`LocalFactor.residueReflection K`),
and `RankinSelberg.IsPadicSymmetricGammaFactor K ψ ν σ τ γ` says that `γ` is the Rankin–Selberg
gamma factor `γ(s, σ × τ, ψ)`. `GeneralLinear.SupercuspidalRep (n := n + 1)` is the Library's
bundled irreducible supercuspidal representation of `GL_{n+1}(K)` and
`GeneralLinear.SupercuspidalClass.firstFixedLevel` the least level `m` with nonzero vectors
fixed by the Library's level subgroup `K_1(𝔭^m)` (value in `WithTop ℕ`). The conductor
`Henniart.Numerical.conductor` of the target statement T2 is this first fixed level.

## Declarations

- `exponent_eq_of_rationalGammaExpression_eq`: if
  `rationalGammaExpression δ c a 1 1 = rationalGammaExpression δ c' m 1 1`, then `a = m`.
- `isPadicSymmetricGammaFactor_of_matrixFunctionalEquationData`: if `ν` is self-dual for `ψ`,
  `σ` is a representation of `GL_{n+1}(K)` of Whittaker type for the standard character of
  `ψ`, and `σ` has Godement–Jacquet functional-equation data `(P, PDual, c, a)`, then
  `rationalGammaExpression δ c a P PDual` is the Rankin–Selberg gamma factor of `σ` against the
  trivial character of `GL_1(K)`.
- `exists_exponent_eq_firstFixedLevel`: let `ψ` have conductor `𝔬_K`, `ν` be
  self-dual for `ψ`, `n ≥ 1`, and `A` an irreducible supercuspidal representation of
  `GL_{n+1}(K)` whose Godement–Jacquet functional equation has both Euler polynomials `1`, unit
  `c` and exponent `a`. Then there is a natural number `m` with `a = m` and
  `firstFixedLevel A.isoClass = m`.

## Provenance

Jacquet–Piatetski-Shapiro–Shalika (1981), §(5.1), printed p. 211
(`jpss-1981-conductor`), identifies the epsilon exponent at additive conductor zero with the
newvector level. Its supercuspidal case is available as
`Conductor.supercuspidalPadicConductorExponent`. The declarations here are internal to T2.
They combine that result with the normalized Godement–Jacquet to Rankin–Selberg comparison
and the trivial L-polynomials for a supercuspidal of rank `N ≥ 2` paired with rank one.

## Proof

`exponent_eq_of_rationalGammaExpression_eq`: with trivial polynomials both sides are monomials
`c X^a` and `c' X^m` (`RankinSelberg.eval_rationalEpsilonMonomial`, Library). Evaluating at
`X = 1` gives `c = c'`; evaluating at `X = 2` then gives `2^a = 2^m` in `ℂ`, hence in `ℝ`, and
`a = m` by injectivity of `k ↦ 2^k`.

The proof of `isPadicSymmetricGammaFactor_of_matrixFunctionalEquationData` applies
`RankinSelberg.Padic.gammaData_rankOne_of_matrix` from
`Langlands.Representation.RankinSelberg.AdjacentRankGammaData`. That lemma chooses a nonzero
Whittaker functional `ℓ`. The Whittaker model map, restricted to
the top subrepresentation, is a surjective intertwining map onto the Whittaker model, so the
Library theorem `GodementJacquet.Padic.subquotientCoefficientInclusion` puts the matrix
coefficients of the Whittaker model among those of `σ`. The Library comparison
`RankinSelberg.rankOneAmbientMatrixFunctionalEquationComparison` then turns the functional
equation of `σ` into the stated gamma factor. Here the ambient representation `ρ` in the
comparison is `σ` itself. The comparison applies the normalized matrix functional equation
to the very same coefficient function using the same `ψ` and `ν`. Its compact realization
on the original and complementary dual blocks cancels a common nonzero scalar. This
produces the full symmetric gamma certificate, with the complex unit and the exponent
from the matrix data. The comparison `GodementJacquet.whittakerModelComparison` cited in
the T2 statement documentation gives equality of rational-continuation spaces. The
normalized ambient comparison supplies the factor identity needed here.

`exists_exponent_eq_firstFixedLevel`:

1. `A` is generic (`SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal`, Library),
   hence of Whittaker type; so is the trivial character `1` of `GL_1(K)`.
2. The matrix comparison gives `γ(s, A × 1, ψ) = rationalGammaExpression δ c a 1 1`.
3. The Library theorem `Conductor.genericConductor_isNewvectorConductor_of_supercuspidalPadic`
   (with `Conductor.supercuspidalPadicConductorExponent`) gives `m : ℕ` with generic conductor
   `m` and `m` the newvector conductor of `A`. `Conductor.exists_isPadicPairEpsilonFactor_genericConductor`
   gives `c'` with `ε(s, A × 1, ψ) = c' X^{m + N·d(ψ)}`, and `d(ψ) = 0` because `ψ` has
   conductor `𝔬_K` (`additiveConductor_eq_zero_of_hasIntegerConductor`).
4. `L(s, A × 1) = 1` and `L(s, Ã × 1) = 1` for the inverse-transpose pullbacks with `ψ(-·)` and
   the negated self-dual measure: both are instances of `supercuspidalUnequalRankLFactor`
   (ranks `n + 1 > 1`), using that the inverse-transpose pullback of `A` is again irreducible and
   supercuspidal (`isSupercuspidal_comp_inverseTranspose`,
   `isIrreducible_comp_continuousMulEquiv_iff`) and that the pullback of `1` is of Whittaker type
   for `ψ(-·)`.
5. The Library theorem `symmetricGammaExpression`, with the epsilon factor of step 3 and the
   trivial L-polynomials of step 4, says that a rational function is the gamma factor of
   `A × 1` if and only if it equals `rationalGammaExpression δ c' m 1 1`. Step 2 and
   `exponent_eq_of_rationalGammaExpression_eq` give `a = m`.
6. `firstFixedLevel A.isoClass` is the first fixed level of `A`
   (`SupercuspidalClass.firstFixedLevel_isoClass`), which is the newvector conductor `m`
   (`Conductor.firstFixedLevel_of_hasNewvectorLevel`, `Conductor.newvectorConductor_eq_iff`).

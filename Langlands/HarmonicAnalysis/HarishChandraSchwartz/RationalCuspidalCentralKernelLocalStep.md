# The local kernel step of VIII.4.1 from central and `L²` weights

Source: J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, proof of Proposition VIII.4.1, printed pp. 328–330 (PDF pp. 94–96).
Registered source `waldspurger-2003-plancherel`.

This module is the third follow-up to focused unit 2 of Task 7439
(revision 2). It imports `RationalCuspidalCentralKernelPairing` (unit 2c),
which imports units 2b and 2. Its provenance is **derived**. It states one new
proposition, `RationalCuspidalLevelKernelFiniteStatement`, and proves it from
three Library statements. It does not construct `°e`, does not prove VIII.3.2,
and does not prove the closed target
`RationalCuspidalCentralProjectionFiniteStatement`.

## What changes compared with unit 2

Unit 2's `IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan` assumes
`ConvolutionWeights muG K' Ξ σ` (the estimate of Lemma III.6.1). It uses that
hypothesis only to make the triple integral of the proof absolutely
convergent. The Library obtains `ConvolutionWeights` from Lemma II.1.5
(`RationalXiSquareIntegrableStatement.convolutionWeights`) only when the
Iwasawa subgroup `K` satisfies `K ≤ rationalHeightSubgroup ρ`, that is
`ρ(K) ⊆ GL_n(𝒪)`. The target quantifies over every `K` and every `ρ`, and no
task supplies that inclusion for every structural choice. This module proves the same
absolute convergence from the central weights and the `L²` weights alone, by
the Cauchy–Schwarz inequality on `A_G \ G`. The resulting local step has no
convolution-weight hypothesis.

## The source step

On printed p. 328 the source writes, for `ϕ ∈ °C_H` with `f = p_χ ϕ`,
`(α_χ(·, g), f) = mes(H)⁻² ∫_G ∫_{A_G} ∫_H °e(g'⁻¹ h a g) χ⁻¹(a) ϕ(g') dh da dg'`,
and states "Cette expression est absolument convergente" without further
argument. This module supplies an argument. The rest of the step (the
reproducing formula (1), the orthonormal basis and the diagonal integral made
finite by VIII.3.2, printed p. 329) is the content of units 2, 2b and 2c,
which this module combines.

## Generic results (section `SquareBound`)

Let `G` be a locally compact, second countable, Hausdorff group with Borel
σ-algebra, `A` a closed subgroup with a right-invariant, s-finite measure
`μ_A` that is finite on compact sets, `μ_G` a measure on `G` that is finite on
compact sets, and `ν` a quotient measure on `A \ G`
compatible with them (`IsCompatible`). `Φ_f(g) = ∫_A |f(a g)| dμ_A(a)` is the
Library's `centralAbsIntegral μA f g`.

- `ennreal_mul_le_sq_add_sq`: `a b ≤ a² + b²` in `ℝ≥0∞`.
- `continuous_centralAbsIntegral`: if `f` lies in the level `C_H` of a compact
  open subgroup `H`, then `Φ_f` is continuous, because it is right
  `H`-invariant and hence locally constant.
- `measurable_centralAbsIntegral`: `Φ_f` is measurable for measurable `f`
  (Tonelli, `Measurable.lintegral_prod_right'`).
- `lintegral_centralAbsIntegral_out_sq_lt_top`: assume `CentralWeights μA Ξ σ`
  and `L2Weights μG Ξ σ`. For measurable `f` with every `ν_r(f)` finite,
  `∫_{A\G} Φ_f(q̇)² dν(q) < ∞`. The proof follows the Library's
  `lintegral_enorm_centralProjection_out_sq_lt_top`. The Weil formula
  (`lintegral_lintegral_out_eq`) gives `∫_{A\G} Φ_f² = ∫_G |f| Φ_f`. Pointwise,
  `|f(g)| ≤ ν_{s+d}(f) Ξ(g) (1 + σ(g))^{-(s+d)}` (`norm_le_of_nu`) and
  `Φ_f(g) ≤ ν_s(f) Ξ(g) (1 + σ(g))^s I` (`CentralWeights.lintegral_enorm_le`),
  with `s` and the finite `I = ∫_A (1 + σ)^{-s}` from the central weights.
  The product is at most a constant times `Ξ(g)² (1 + σ(g))^{-d}`, whose
  integral is finite by the `L²` weights.
- `lintegral_enorm_mul_centralAbsIntegral_lt_top` (**Cauchy–Schwarz on
  `A \ G`**): for `φ` and `f` in the Schwartz space,
  `∫_G |φ(x)| Φ_f(x) dμ_G(x) < ∞`. By the Weil formula the integral equals
  `∫_{A\G} Φ_φ(q̇) Φ_f(q̇) dν(q)`. This is at most
  `∫_{A\G} Φ_φ² + ∫_{A\G} Φ_f²` by `ennreal_mul_le_sq_add_sq`, and both terms
  are finite by the previous lemma. Measurability of `q ↦ Φ_φ(q̇)²` comes from
  the continuity of `Φ_φ`, its left `A`-invariance and the Library's
  `continuous_out_of_invariant`.
- `integrable_kernelTriple_of_l2Weights`: assume in addition that `μ_A` is
  inversion invariant, `μ_G` is left invariant and s-finite, and `μ_H` is a
  finite measure on a subgroup `H`. Let `E` and `φ` lie in the Schwartz
  space, with `E(x⁻¹) = E(x)` and `φ` left `H`-invariant. Let `g ∈ G` be such
  that the left translate `f = (x ↦ E(g⁻¹ x))` lies in the Schwartz space.
  Then `(g', a, h) ↦ E(g'⁻¹ h a g) φ(g')` is integrable on `G × A × H`. Proof:
  by Tonelli the `G`-integral comes first. The substitution `g' ↦ h g'`
  (`lintegral_mul_left_eq_self`) and the left `H`-invariance of `φ` remove
  `h`. The identity `E(g'⁻¹ a g) = E(g⁻¹ a⁻¹ g') = f(a⁻¹ g')` uses
  `E(x⁻¹) = E(x)`. Inversion invariance of `μ_A` (`lintegral_inv_eq_self`)
  then turns the `A`-integral into `Φ_f(g')`. The total is
  `μ_H(H) ∫_G |φ| Φ_f`, which is finite by the Cauchy–Schwarz lemma.

## Rational results (section `Rational`)

The setting is that of units 2–2c: `F` a nonarchimedean local field, `G`
with `K`, `hKc`, `hPK`, `ρ`, `Ξ = rationalXi hKc hPK` and
`σ = rationalHeight ρ`; `s` with `hs : IsSplitComponent s`, a Haar measure
`muA` on `A_G(F) = (rationalPoints.map s).range`, and a unitary character `χ`.

- `IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_l2Weights`:
  assume a Haar measure `muG` on `G(F)` with `[muG.IsMulRightInvariant]`, a
  compact open `H`, `E` with `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E`,
  `CentralWeights muA Ξ σ`, `L2Weights muG Ξ σ` and
  `RationalLevelKernelDiagonalIntegrable hKc hPK ρ muA χ muG H E`. Then
  `rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H` is finite dimensional.
  The proof is that of unit 2's `IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan`
  with one change: the triple integrability input of
  `finiteDimensional_schwartzCentralIntegralSpan_of_kernel` comes from
  `integrable_kernelTriple_of_l2Weights`. The left translate `x ↦ E(g⁻¹ x)`
  lies in the Schwartz space because it is `Space.translate hTW 1 g E`
  (`rationalTranslationWeights`).
- `IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_conjugationIntegrable`:
  assume `hG : IsConnectedReductive G`, a Haar measure `muG`, a compact open
  `H`, `E` with `IsRationalCuspidalLevelKernel`, the central and `L²` weights,
  and `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E`
  (unit 2c: the VIII.3.2 integrability form at `f₁ = E`). Then the actual
  central level span of `H` is finite dimensional. There is **no** hypothesis
  on `χ`. If some `b ∈ A_G(F) ∩ H` has `χ(b) ≠ 1`, unit 1's
  `rationalCuspidalCentralLevel_finite_of_ne_one` shows the span is zero.
  Otherwise `χ` is trivial on `A_G(F) ∩ H`. Right invariance of `muG` comes
  from unit 2's `rationalHaar_isMulRightInvariant`. The diagonal input comes
  from unit 2b's `IsRationalCuspidalLevelKernel.diagonalIntegrable` applied to
  unit 2c's `RationalLevelKernelPairingIntegrable.of_leftConjugationPairing`.
  The previous theorem then applies.

## The new statement

`RationalCuspidalLevelKernelFiniteStatement` (universe `u`) is the closed
proposition below. Take any `F : Type u` with
`[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`
and any `G` with `[IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]` and
`IsConnectedReductive G`. Take the structural choices of
`RationalCuspidalCentralProjectionFiniteStatement`:

- a maximal split torus `i : S → G` (`IsMaximalSplitTorus i`) and a generic
  cocharacter `ν`;
- a compact open `K` with `hPK : IsIwasawaPair (standardParabolicPoints i ν ∅) K`;
- a matrix representation `ρ` with `IsClosedSubgroup ρ`;
- a split component `s` (`hs`), a Haar measure `muA` on `A_G(F)` and a
  unitary character `χ`.

Then for every compact open `H`, every Haar measure `muG` on `G(F)` and every
`E : RationalSchwartzSpace hKc hPK ρ` such that
`IsRationalCuspidalLevelKernel hKc hPK ρ muG H E` and
`RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E` hold,
`FiniteDimensional ℂ (rationalCuspidalCentralLevelSpan hKc hPK ρ muA χ H)`.

It is the source's local step for one `H`, with the properties of `°e` and
the VIII.3.2 conclusion at `°e` as explicit premises. The central weights
and the `L²` weights are not premises: the next theorem derives them.

`RationalCuspidalLevelKernelFiniteStatement.of_statements` proves it from
three Library statements:

- `RationalSplitCenterHeightStatement`, through the Library's
  `RationalSplitCenterHeightStatement.centralWeights`, gives
  `CentralWeights muA Ξ σ` (this uses `IsClosedSubgroup ρ`);
- `CuspidalSupport.RationalSpecialVertexCompactInputsStatement` gives a
  special compact `K0` with `SpecialCompactProperties`,
  `SimultaneousStandardBasisAt i ν K0` and `FiniteCartanCovering F i ν K0`;
- `RationalXiSquareIntegrableStatement` (Lemma II.1.5), through the
  Library's `RationalXiSquareIntegrableStatement.l2Weights` with that `K0`,
  gives `L2Weights muG Ξ σ`.

It then applies
`IsRationalCuspidalLevelKernel.finiteDimensional_levelSpan_of_conjugationIntegrable`.

## Open hypotheses and their owners

None of the hypotheses below is same-rank finiteness, same-rank
reconstruction, the closed target or a dimension bound.

- `RationalSplitCenterHeightStatement`: owned by Task 5480
  (`c3846e17-dfda-44c2-a37e-cd9054cb3b0f`).
- `RationalXiSquareIntegrableStatement`: the Library proves it from
  `RationalXiUpperBoundStatement` (the upper bound of Lemma II.1.1) by
  `rationalXiSquareIntegrable_of_upperBound`. That upper bound is owned by
  Task 5326 (`d27429ee-ab4e-47b4-8486-8cdd92ff4d34`).
- `CuspidalSupport.RationalSpecialVertexCompactInputsStatement`: the Library
  proves it from `JointSpecialCompactBasisExistenceStatement` by
  `CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`. That
  statement is owned by Task 4169 (`8c39faa0-2a70-4fc4-a027-914987aba924`).
- The premise `IsRationalCuspidalLevelKernel hKc hPK ρ muG H E` of the
  statement, for `E = °e`: Worker 827's unit 3 of Task 7439 (Library module
  `RationalCuspidalUnit`) derives the five properties from six laws of a
  linear projection. Task 7277 (`eaceb96b-aaaf-4068-9a11-46292b5334e6`) owns
  those laws for the actual degree-zero projection. The bridge from unit 3's
  interface to `IsRationalCuspidalLevelKernel` stays inside Task 7439
  (Worker 827's module `RationalCuspidalUnitKernel`, not yet staged).
- The premise `RationalLevelKernelConjugationIntegrable hKc hPK ρ hs muA muG E`
  of the statement, for `E = °e`: it is the second conjunct of the Library
  statement `RationalCuspidalConjugationIntegrabilityStatement` (VIII.3.2)
  at `f₁ = °e`. The proof of that statement is owned by Task 7500
  (`6c7dbd12-f209-43e5-8e07-60460134dc82`). The adapter from the Library
  statement to this premise, which needs `°e` to be cuspidal and a compact
  `K0` with `SimultaneousStandardBasisAt`, stays inside Task 7439 (Worker
  827's module `RationalCuspidalUnitKernel`, together with Task 4169 for the
  basis).

Unimodularity of `G(F)` is not open: unit 2's `rationalHaar_isMulRightInvariant`
derives it for connected reductive `G`.

## Dependencies

This module depends on the Task 7439 units published at Library commit
`371b9c350ae74d42665a9e7e0ec32e4c66f56619`: unit 2 (`2eeb2a9b-6ac4-4307-b89b-ea12a7030a50`, module
`RationalCuspidalCentralKernelStep`), unit 2b
(`55f19aeb-32e1-4508-ab80-f107d3d09672`, module
`RationalCuspidalCentralKernelDiagonal`) and unit 2c
(`ec802636-4330-40a4-a352-47c3939d9071`, module
`RationalCuspidalCentralKernelPairing`). It also imports the Library modules
`RationalCuspidalCentralFiniteReduction` (unit 1),
`RationalCentralProjection` and
`CuspidalSupport.RationalCuspidalInertiaDecompositionReduction`.

# Discrete-series isotypic projectors in tempered Levi representations (proof)

`Langlands.glTemperedDiscreteSeriesIsotypic` proves the Library proposition
`Langlands.GLTemperedDiscreteSeriesIsotypicStatement.{uF,uV,uW}` of
[TemperedDiscreteSeriesIsotypicStatement](TemperedDiscreteSeriesIsotypicStatement.md),
with independent universes `uF`, `uV` and `uW`.

## Statement proved

Let `F` be a `p`-adic field with topological data `T`, `n > 0`, `B` a standard
block shape, `M = B.Levi F.Carrier` with `T.leviTopologicalGroup B`, and
`Q = M ⧸ Subgroup.center M` the quotient by the full center of `M`. Fix any
Borel measurable structure on `Q` and any Haar measure `μ` on it. Let `ρ` be a
representation of `M` on a space `V` in universe `uV` that is
`IsTemperedModCenter ρ μ`. Let `σ` be a representation on a space `W` in
universe `uW` that is irreducible and `IsSquareIntegrableModCenter σ μ`.
Suppose the supplied unitary central characters `cρ`, `cσ` satisfy
`cρ.character = cσ.character`. Then there is an intertwiner `P : ρ → ρ` with
`P ∘ P = P`, whose range is the isotypic subrepresentation
`⨆ f : σ.IntertwiningMap ρ, f.range`, and such that no subrepresentation of
`ker P` has a surjective intertwiner onto `σ`.

The representation `ρ` is not assumed irreducible, semisimple, unitarizable,
finitely generated or of finite length. No compact-support condition on `σ`,
chosen projector, coefficient-algebra action or splitting witness is assumed.

## Lean proof

The theorem is the term

`glTemperedDiscreteSeriesIsotypicReduction glProductLeviSquareIntegrableLp`.

- `Langlands.glTemperedDiscreteSeriesIsotypicReduction`
  ([TemperedDiscreteSeriesIsotypicReductionProof](TemperedDiscreteSeriesIsotypicReductionProof.md))
  proves `GLTemperedDiscreteSeriesIsotypicReductionStatement.{uF,uV,uW}`. This
  is the implication from `GLProductLeviSquareIntegrableLpStatement.{uF,uW}` to
  `GLTemperedDiscreteSeriesIsotypicStatement.{uF,uV,uW}`.
- `Langlands.glProductLeviSquareIntegrableLp`
  ([ProductLeviSquareIntegrableLpProof](ProductLeviSquareIntegrableLpProof.md))
  proves `GLProductLeviSquareIntegrableLpStatement.{uF,uW}` with no hypothesis.

The two theorems are applied at the target's universes `uF`, `uV` and `uW`. No
universe is fixed or identified with another. The sections below summarize the
composed argument; each step is proved in the module named.

## From the analytic predicates to the estimates used

The proof uses the Library predicates only through the following estimates.

- `IsSquareIntegrableModCenter σ μ` means that `σ` is admissible and that, for
  some unitary central-character datum `c`, every smooth coefficient norm
  `c.coefficientNorm ℓ w` lies in `L²(μ)`. `UnitaryCentralCharacter.coefficientNorm_eq`
  shows that these norms on `Q` do not depend on the datum: both are
  `q ↦ ‖ℓ(σ(g)w)‖` for any representative `g` of `q`. So the bounds hold for
  the supplied `cσ`.
- `glProductLeviSquareIntegrableLp` turns admissibility and the `L²` bounds
  into a stronger estimate. For `cσ` and each smooth `ℓ`, `w`, it gives `r`
  with `1 < r < 2` and `MemLp (cσ.coefficientNorm ℓ w) (ENNReal.ofReal r) μ`.
  Its route has three steps. First, the `L²` condition makes every
  generalized Jacquet eigencharacter strictly smaller than one on the
  fundamental coweights (`ProductLeviSquareIntegrableExponent`). Second, this
  gives a strict Cartan chamber bound by `δ^(1/2 + ε)`
  (`ProductLeviStrictChamberBound`). Third, the published Cartan-cell volume
  bound `measure_cellQ_le` and a geometric lattice sum give integrability with
  exponent `2 (1 + ε) / (1 + 2 ε)`.
- `IsTemperedModCenter ρ μ` means that `ρ` is admissible and that, for some
  datum `c`, every smooth coefficient norm lies in `L^(2+ε)(μ)` for every
  `ε > 0`. In `pairingIntegrable_of_lt_two` the conjugate exponent
  `r' = r/(r-1)` satisfies `r' > 2` because `r < 2`. Temperedness with
  `ε = r' - 2` puts `c.coefficientNorm η v` in `L^(r')(μ)`, and
  `coefficientNorm_eq` rewrites this for `cρ`.
- `integrable_pairingKernel`
  ([TemperedCoefficientPairing](TemperedCoefficientPairing.md)) applies Hölder's
  inequality for the conjugate pair `r`, `r'`. It uses inversion invariance of
  `μ` to move the `σ`-bound from `q` to `q⁻¹`. Hence every coefficient product
  with smooth entries is absolutely integrable over `Q` (`PairingIntegrable`).
- The `L²` bounds for `σ` also define the invariant positive form
  `b = cσ.coefficientProductForm` on `σ` (`Unitary/SquareIntegrableProof`). They
  make `∫ |b(u, σ(g)u)|² dμ` finite, and
  `eq_zero_of_integral_coefficientNorm_sq_eq_zero` makes it nonzero for
  `u ≠ 0`.

Admissibility of `ρ` gives smoothness and finite-dimensional `Hom(σ, ρ)`. The
`L^r` and `L²` estimates above are the only analytic inputs.

## Exact scalar-character cancellation on the full central quotient

For `ℓ : Module.Dual ℂ W`, `w : W`, `η : Module.Dual ℂ V` and `v : V`, the
pairing kernel is

`g ↦ ℓ(σ(g⁻¹) w) · η(ρ(g) v)`.

Let `z` be in `Subgroup.center M`, and write `χ = cσ.character = cρ.character`.
Because `z` is central, `(g z)⁻¹ = g⁻¹ z⁻¹`. The Library law
`UnitaryCentralCharacter.matrixCoefficient_mul_center` multiplies the first
factor by `χ(z)⁻¹` and the second by `χ(z)`. The two characters are equal as
homomorphisms to `ℂˣ`, so the product of the scalars is exactly
`χ(z)⁻¹ χ(z) = 1`, not merely of absolute value one. This is
`pairingKernel_mul_center` in
[TemperedCoefficientPairing](TemperedCoefficientPairing.md). Therefore the
kernel is constant on the cosets of the whole center and descends by
`Quotient.lift` to `pairingKernel cσ hχ ℓ w η v : Q → ℂ`. It is not defined on
a quotient by a smaller central subgroup. Its norm at `q` is
`cσ.coefficientNorm ℓ w q⁻¹ * cρ.coefficientNorm η v q`
(`norm_pairingKernel`). This is the product estimated by Hölder above. The
integrated pairing `coefficientPairing` is the Bochner integral of this kernel
over `Q` with respect to `μ`.

## Measure and universe scope

The measure `μ` is the arbitrary Haar measure of the target, on `Q` with the
arbitrary Borel measurable structure of the target. The same `μ` appears in
both analytic hypotheses. It is not normalized or replaced. Left invariance
and positivity on nonempty open sets come with `IsHaarMeasure`.
`PadicField.TopologicalData.leviCentralQuotientHaar_unimodular T B μ`
([LeviCentralQuotientMeasure](../../Group/GL/LeviCentralQuotientMeasure.md))
proves that this `μ` is also right invariant and invariant under inversion.
Every positive character of the full central quotient of the block Levi is
trivial, so `μ` is right invariant. Regular Haar uniqueness then gives
inversion invariance. Right invariance and left invariance give the
translation laws of `coefficientPairing`, and inversion invariance gives the
Hölder step.

The field universe `uF` and the carrier universes `uV` of `ρ` and `uW` of `σ`
remain independent. The analytic input is used at `uF` and `uW`. Compact open
subgroups of `M` are cofinal among open subgroups, by
`UnitaryDualJacquetSupport.levi_compactOpen_cofinal T B`.

## The projector and its kernel

The generic theorem `temperedDiscreteSeriesIsotypic_of_lt_two` of the
reduction module builds `P` as follows.

1. `Hom(σ, ρ)` is finite-dimensional (`finite_intertwiningMap_of_finiteType`),
   since an irreducible smooth `σ` is finitely generated and `ρ` is admissible.
2. Weak-integral intertwiners
   ([WeakIntertwiner](../Smooth/Contragredient/WeakIntertwiner.md)) turn
   `coefficientPairing` into intertwiners `ρ → σ` and `σ → ρ`. Extending smooth
   functionals along injective intertwiners (`Smooth/Contragredient/ExactProof`)
   and positivity show that the functional `m = b(u, -)` detects every nonzero
   intertwiner `f : σ → ρ` through some `ρ → σ` intertwiner.
3. A dual-basis construction on `Hom(σ, ρ)` with Schur's lemma
   ([IsotypicProjector](../Smooth/IsotypicProjector.md)) gives `P` fixing every
   intertwiner `σ → ρ` with values in the isotypic subrepresentation. Hence
   `P ∘ P = P` and the range is the isotypic subrepresentation.
4. If a subrepresentation `K` of `ker P` maps onto `σ`, the pairing yields an
   intertwiner `R : σ → ρ` that is killed by `P`. Since `P` fixes `R`, `R = 0`.
   But positivity makes a value of `R` nonzero, a contradiction.

No Schur orthogonality relation or formal degree is used.

## Acyclic dependency route

The module imports exactly the two modules above. Its project import closure
was computed from the import lines at Library commit
`355c05239d7704a3ed5d72bad864cb1d542b647a`. It has 404 `Langlands` modules,
including this one. It contains none of the following:

- `DiscreteSeriesJacquetStatement` or `TemperedDiscreteSeriesJacquetQuotientProof`
  (the discrete-series opposite Jacquet quotient criterion, task `0c21305f`);
- `TemperedDiscreteSeriesSummandProof` (the parent tempered summand proof,
  task `28328284`);
- any `RegularLanglands*` module (the regular Langlands head theorem, and
  regular exhaustion, task `bf433f0a`);
- `MultisegmentClassificationStatement`,
  `SquareIntegrableLanglandsClassificationProof` or
  `SquareIntegrableLanglandsExhaustionProof` (tasks `1cb45da2` and `cd8ab97c`);
- any module under `Langlands.Representation.CompactCoefficient`.

In this closure, only three modules import
`TemperedDiscreteSeriesIsotypicStatement`: the reduction statement, its proof
and this module. So no support, summand or exhaustion result built on this
projector is used. Statement modules such as `TemperedSupportStatement` occur
in the closure only as sources of definitions and propositions, never as proofs.

The analytic branch, `glProductLeviSquareIntegrableLp`, rests on these Library
results: the product-Levi chamber bound, tempered sufficiency and necessity
helpers; the Cartan decomposition and cell count; and the countable-cell `L^p`
criterion. Its Markdown records the same independence. The algebraic branch,
the reduction, rests on the coefficient pairing, the weak-intertwiner lemma, the
isotypic-projector lemmas and the quotient-measure laws above, together with
Library smooth-dual and unitary results.
`CompactCoefficient.ProjectorProof` is not used, so its compact-coefficient
premise is neither needed nor assumed.

## Provenance

The target is extracted from Silberger 1979, Theorem 4.5.18 and the proof of
Theorem 3.3.1, as recorded in the statement Markdown. Silberger decomposes a
module with exact scalar central character by its coefficient convolution
algebra. The Lean route is the internal argument above and differs from his.
The sub-two integrability follows the derivation from Waldspurger 2003,
Proposition III.1.1 and the proof of Corollary III.1.2, recorded in
[ProductLeviSquareIntegrableLpStatement](ProductLeviSquareIntegrableLpStatement.md).

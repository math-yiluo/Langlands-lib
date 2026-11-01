# Nonzero derivatives of subrepresentations of left mixed products

Author: Worker 1129. Module
`Langlands.Representation.Derivative.LeftMixedProductPhiHatIterate`, namespace
`Langlands.Derivative.Mirabolic`. Main theorem:
`hasNonzeroDerivative_leftMixed_subrepresentation`. The module's only
definition is `leftMixedProductMap` (section `Map`); the record names it as its
declaration.

This module proves the lower half of Zelevinsky's Proposition 5.3. Let `ρ` be
a smooth representation of `GL_k` and `τ` one of the mirabolic group
`P_(r+1)`, both with carriers in a universe `uV`. Let `0 < l ≤ r + 1`, let `θ`
be a smooth representation of `GL_(r+1-l)`, and let

```
β : τ ↪ Y_l(θ) = (Φ̂⁺)^(l-1) Ψ⁺(θ)
```

be an injective intertwiner. Then every nonzero subrepresentation `W` of the
left mixed product `ρ × τ` has a nonzero derivative of order `l`:
`HasNonzeroDerivative T ψ W l`, that is `W^(l) ≠ 0`.

The module states no exactness, 4.14(a), level-equality or homogeneity result
and assumes none. No theorem here has a proposition definition as a hypothesis.
The only hypotheses of the main theorem are the order bounds `hl`, the
injective intertwiner `β` (with `hβ`) and `U ≠ ⊥`. The upper half of 5.3
(`λ(W) ≤ l`) and the final assembly are not part of this module.

## Sources

Zelevinsky, *Induced representations of reductive p-adic groups II* (1980),
source ID `zelevinsky-1980-induced-ii`, SHA256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`
(printed page = PDF page + 163):

- §5.1, printed p.187 (PDF p.24): for `σ ∈ Alg P`,
  `(★) Hom(σ, (Φ̂⁺)^(l-1) ∘ Ψ⁺(θ)) = Hom(σ^(l), θ)`, from `Φ⁻ ⊣ Φ̂⁺` used
  `l - 1` times and `Ψ⁻ ⊣ Ψ⁺` once. In the proof of (3) ⇒ (1), a nonzero
  `σ ⊂ τ ↪ (Φ̂⁺)^(l-1) Ψ⁺(τ^(l))` has `σ^(l) ≠ 0`.
- §5.3, printed pp.187–188 (PDF pp.24–25): `ρ × τ ↪ ρ × (Φ̂⁺)^(l-1) Ψ⁺(τ^(l))`,
  the embedding `ρ × Φ̂⁺(σ) ↪ Φ̂⁺(ρ × σ)` applied `l - 1` times, a comparison of
  `ρ × Ψ⁺(θ)` with `Ψ⁺(ρ × θ)`, and §5.1 (3) ⇒ (1).

Bernstein–Zelevinsky, *Induced representations of reductive p-adic groups I*
(1977), source ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092` (printed
page = PDF page + 439): §3.2, printed pp.450–451 (`Φ⁻`, `Ψ⁻`, `Ψ⁺`,
`Φ̂⁺ = I_(V,θ)`; (c) `Φ⁻` is left adjoint to `Φ̂⁺`; `V` acts trivially on
`Ψ⁺(θ)`), and §4.12, case (II), printed pp.456–458 (the product `ρ × τ` for
`ρ ∈ Alg G_k`, `τ ∈ Alg P_m`).

Provenance is derived. The source concludes through an embedding
`ρ × τ ↪ (Φ̂⁺)^(l-1) Ψ⁺((ρ × τ)^(l))`, which needs the `Ψ⁺` comparison and
BZ77 4.14(a). This module only needs a nonzero intertwiner out of `W`, so it
stops one step earlier. It peels the `Φ̂⁺` factors off the target one at a
time, using the published embedding and adjunction, until the target is
`ρ' × Ψ⁺(θ)`. There `V` acts trivially, so the map factors through `Ψ⁻`. This
replaces the `Ψ⁺(ρ × θ)` comparison and the identification of the derivative
`(ρ × τ)^(l)`. The auxiliary lemmas below are derived statements about the
published objects.

## Published inputs and conventions

All objects are published Library objects, used unchanged.

- `T.leftMixedProductFunctor k r` (`Mirabolic.MixedProducts`): `ρ × τ` on
  `P_(k+r+1)`, case (II). Its vectors are determined by their values
  `T.leftMixedEval (ρ, τ) f x ∈ ρ ⊗ τ` (`leftMixedEval_injective`). They are
  covariant under `leftSubgroup k r` with blocks `(a, p) = leftProjection h`
  and the character `χ_L` (`leftMixedEval_covariant`, `leftLeviCharacter_apply`).
  The group acts by right translation (`leftMixedProductFunctor_action`). The
  product is the compact induction (`Induction.compactInducedMap` on maps) of
  the `χ_L`-twisted pullback along `leftProjection` of the external tensor
  product.
- `phiHatPlus`, `phiHatPlusAdjunction`
  (`Hom(A, Φ̂⁺σ) ≃ₗ[ℂ] Hom(Φ⁻A, σ)`), `phiHatPlusIterate T ψ n j`
  (`(Φ̂⁺)^j : P_(n+1) → P_(n+j+1)`; for `j + 1` it is `(Φ̂⁺)^j` followed by
  `Φ̂⁺` at rank `n + j`) and `mirabolicDerivativeOfOrderRightAdjoint T ψ N l hl`
  (Worker 749, `MirabolicSmoothPhiPlus`, `…Adjunction`, `…Iterate`). The last
  is `Y_l(θ)`: `Ψ⁺ θ`, lifted to the carrier universe `max uF uV`
  (`MixedProductTensor.liftFunctor`), then `(Φ̂⁺)^(l-1)`, then the rank cast
  `mirabolicRankCast` along `(N+1-l) + (l-1) = N`.
- `leftPhiHatEmbedding T ψ ρ σ : ρ × Φ̂⁺(σ) → Φ̂⁺(ρ × σ)` and
  `leftPhiHatEmbedding_injective` (`MirabolicSmoothPhiPlusProduct`, Worker
  1129); `leftPhiHatSource T ψ ρ σ` is `ρ × Φ̂⁺(σ)`.
- From `Mirabolic.LeftMixedProductSuccessor` (Worker 1129): `leftRadical`
  (a radical element of `P_(k+n+1)` as an element of `leftSubgroup k n`),
  `leftProjection_leftRadical_fst` (its `GL_k` block is `1`),
  `leftProjection_leftRadical_snd_mem` (its mirabolic block lies in the radical
  of `P_(n+1)`) and `T.determinantNorm_radical'` (`ν = 1` on the radical).
- `psiMinus`, `psiMinusQuotient`, `psiPlus`, `psiPlus_radical`
  (`MirabolicMinus`, `MirabolicPlus`): `Ψ⁻ A` is the coinvariant quotient
  `Jacquet.Localization` of `A` for the radical `V` with the trivial
  character, and `V` acts trivially on `Ψ⁺ θ`.
- `mirabolicDerivative T ψ n j = Ψ⁻ ∘ (Φ⁻)^j : P_(n+j+1) → GL_n`,
  `mirabolicDerivativeOfOrder`, `mirabolicRankCast` and `HasNonzeroDerivative`
  (`Derivative.Iteration`, `Derivative.Homogeneity`).
  `HasNonzeroDerivative T ψ A l` means `0 < l ≤ N + 1` and the order-`l`
  derivative of `A` (on `P_(N+1)`) is nontrivial.
- From `Derivative.LevelCalculus`: `mirabolicDerivative_succ_cast_obj`
  (`Ψ⁻(Φ⁻)^(j+1)` of a cast of `A` equals `Ψ⁻(Φ⁻)^j` of a cast of `Φ⁻ A`),
  `nontrivial_mirabolicDerivative_cast_congr` (nontriviality is independent of
  the rank-equality proof and of equal indices) and
  `subrepresentation_nontrivial` (`U ≠ ⊥` gives a nontrivial carrier). These
  three lemmas have no exactness hypothesis.
- Mathlib: `TensorProduct.map_injective_of_flat_flat` (every `ℂ`-module is
  flat, `Mathlib.RingTheory.Flat.Basic`).

## The radical acts trivially on `ρ × σ`

Section `Radical`.

- `leftLeviCharacter_leftRadical_eq_one`: `χ_L` is `1` on `leftRadical u`, since
  the `GL_k` block is `1` and the mirabolic block has `ν = 1`.
- `leftMixedProduct_radical_eq_self`: if the radical `V_(n+1)` of `P_(n+1)`
  acts trivially on `σ`, then the radical `V_(k+n+1)` acts trivially on
  `ρ × σ`. Proof: for `u ∈ V_(k+n+1)` and `x ∈ P_(k+n+1)`, `w = x u x⁻¹` is in
  the normal subgroup `V_(k+n+1)` and `x u = w x`. As an element of
  `leftSubgroup k n`, `w` has blocks `(1, p_w)` with `p_w ∈ V_(n+1)`. So
  covariance gives `f(x u) = χ_L(1, p_w) (1 ⊗ σ(p_w)) f(x) = f(x)`.

## Detecting `Ψ⁻` by a map into a representation with trivial radical action

Section `Psi`. `nontrivial_psiMinus_of_ne_zero`: let `B` be a representation
of `P_(m+1)` on which `V_(m+1)` acts trivially, and let `Φ : A → B` be a
nonzero intertwiner. Then `Ψ⁻ A` is nontrivial. Proof: `Φ` satisfies
`Φ(u v) = Φ(v)`, so it factors as `Φ = lift ∘ q` through the coinvariant
quotient `q = psiMinusQuotient` (`Jacquet.Localization.lift_mk`). If `Ψ⁻ A` were
subsingleton, every `q v` would be `0`, so `Φ = 0`.

## Peeling `Φ̂⁺` off a left mixed product

Section `Iterate`. Here `ρ` and `X` have carriers in `max uF uV`, and `A` has
an arbitrary carrier universe `uA`. Each lemma takes its target as a separate
object `B` with an object equation `hB : B = …`. At the use sites the
equation is closed by `rfl`, and the lemma substitutes it. This avoids
converting intertwiner types between objects that agree only after
definitional unfolding, which is expensive in the elaborator. The section also
makes `phiHatPlus` locally irreducible, for the same reason.

- `nontrivial_mirabolicDerivative_of_leftPhiHatIterate_zero` (base case): if
  `V` acts trivially on `Y`, a nonzero intertwiner `A → ρ × Y` gives a
  nontrivial `Ψ⁻ A` (after the trivial rank cast). Proof: combine the two
  sections above.
- `nontrivial_mirabolicDerivative_of_leftPhiHatIterate_succ` (inductive step):
  let `Z = (Φ̂⁺)^j X` and let `Φ : A → ρ × (Φ̂⁺)^(j+1) X = ρ × Φ̂⁺(Z)` be
  nonzero. Composing with the injective `leftPhiHatEmbedding` gives a nonzero
  `E ∘ Φ : A → Φ̂⁺(ρ × Z)`. The adjunction equivalence turns it into a nonzero
  `Φ⁻ A → ρ × Z`, and the induction hypothesis applies to `Φ⁻ A`. Finally
  `mirabolicDerivative_succ_cast_obj` identifies `Ψ⁻(Φ⁻)^(j+1) A` with
  `Ψ⁻(Φ⁻)^j (Φ⁻ A)`.
- `nontrivial_mirabolicDerivative_of_leftPhiHatIterate`: by induction on `j`,
  if `V_(n+1)` acts trivially on `X` and `Φ : A → ρ × (Φ̂⁺)^j X` is nonzero,
  where `A` is on `P_(k+n+j+1)`, then `Ψ⁻(Φ⁻)^j A ≠ 0`. That is,
  `(mirabolicDerivative T ψ (k+n) j).obj A` (after the rank cast `h`) is
  nontrivial.
- `nontrivial_mirabolicDerivative_of_leftPhiHatIterate_cast`: the same with
  the target `ρ × (cast_e (Φ̂⁺)^j X)` transported along a rank equality
  `e : n + j = r` (by `subst e`).

## Left mixed products of intertwiners across carrier universes

Section `Map`.

- `leftMixedProductMap T α β : ρ₁ × τ₁ → ρ₂ × τ₂`, for intertwiners
  `α : ρ₁ → ρ₂` and `β : τ₁ → τ₂`, where `ρ₁, τ₁` have carriers in `uV₁` and
  `ρ₂, τ₂` in `uV₂`. It is `Induction.compactInducedMap` of the `χ_L`-twisted
  (`twistIntertwining`) pullback along `leftProjection`
  (`MixedProductTensor.pullbackMap`) of `MixedProductTensor.externalMap α β`.
  The published functor's `map` only handles a single carrier universe, which
  is why this definition is needed.
- `leftMixedEval_leftMixedProductMap` (`rfl`): its values are
  `x ↦ (α ⊗ β)(f(x))`.
- `leftMixedProductMap_injective`: if `α` and `β` are injective, so is
  `α ⊗ β` (over `ℂ`, all modules are flat), hence so is the product map
  (`leftMixedEval_injective`).

## Nonzero subrepresentations under injective intertwiners

Section `Subtype`. `comp_subtype_ne_zero`: for a nonzero subrepresentation
`U` of a smooth representation `A` of any topological group and an injective
intertwiner `M` out of `A`, the restriction `M ∘ (U ↪ A)` is nonzero. Proof:
`U` has a nonzero vector (`subrepresentation_nontrivial`), and `M` and the
inclusion are injective.

## Zelevinsky 5.3, lower half

Section `Lower`.

- `liftObj_psiPlus_radical`: `V_(n+1)` acts trivially on the lift of `Ψ⁺(θ)`
  to the carrier `ULift` (from `psiPlus_radical`).
- `hasNonzeroDerivative_leftMixed_subrepresentation`: the theorem stated at
  the top. Proof:
  1. Let `ρ' = liftObj ρ` (`MixedProductTensor.liftObj.{uF, uV, uF}`, carrier
     `ULift`), and let `α : ρ → ρ'` be `ULift.up`, an injective intertwiner.
  2. `M = leftMixedProductMap T α β : ρ × τ → ρ' × Y_l(θ)` is injective. The
     lifted factor `ρ₂ := ρ'` is supplied explicitly. Inferring it from `α`'s
     type would unify `?ρ₂.representation` with `lift ρ.representation`, and
     that unification is expensive.
  3. `Φ = M ∘ (W ↪ ρ × τ)` is nonzero (`comp_subtype_ne_zero`).
  4. `Y_l(θ)` is the cast of `(Φ̂⁺)^(l-1) X` along
     `(r+1-l) + (l-1) = r` (`mirabolic_rank_eq_of_order`), with `X` the lift
     of `Ψ⁺(θ)`, on which `V` acts trivially. So the `_cast` lemma (with
     `hB` by `rfl`) gives `Ψ⁻(Φ⁻)^(l-1) W ≠ 0`, computed at the indices
     `(k + (r+1-l), l-1)`.
  5. `HasNonzeroDerivative T ψ W l` holds with `0 < l ≤ k + r + 1`. The order-`l`
     derivative of `W` is `Ψ⁻(Φ⁻)^(l-1)` at the indices `(k+r+1-l, l-1)`,
     equal to the previous indices by `omega`
     (`nontrivial_mirabolicDerivative_cast_congr`).

## Import inventory and exclusion audit

Direct imports: `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusProduct`
(the embedding `leftPhiHatEmbedding`; it brings in Worker 749's `Φ̂⁺` and its
adjunction), `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`
(`phiHatPlusIterate`, `mirabolicDerivativeOfOrderRightAdjoint`),
`Langlands.Representation.Derivative.LevelCalculus` (the three cast and
nontriviality lemmas listed above) and `Mathlib.RingTheory.Flat.Basic`. No
existing Library file is changed.

The transitive project import closure at Library commit
`8f53f05bb76983088fd64f190658c6ac4c3edc1b` has 128 modules besides this one
(all prefixed by `Langlands.`):

`Analysis.Local.QuotientMeasure`. `Group.GL`: `Basic`, `BlockModulus`,
`Blocks`, `Mirabolic`, `MirabolicMixedProductSubgroups`,
`MirabolicModulusProof`, `MirabolicModulusStatement`,
`MirabolicOppositeIntersection`, `MirabolicProjection`, `MirabolicRadical`,
`Nonarchimedean`, `NonarchimedeanStatement`, `NormalizedCharacter`,
`OppositeBlocks`, `Padic`, `PadicBlocks`, `RankMaps`, `RankReindex`,
`TriangularParabolic`, `UpperUnipotent`. `Group.HaarModulus`.
`HarmonicAnalysis`: `Basic`, `Conductor`, `PadicAdditiveConductorProof`,
`PadicHaarScalingStatement`, `PadicLatticeTopology`,
`PadicRectangularHaarScalingProof`, `PadicScalarHaarScalingProof`.
`LocalFactor.Harmonic.Statement`. `LocalField`: `Canonical`, `Definitions`,
`Normalization.Definitions`, `Normalization.Proof`, `Normalization.Statement`,
`Topology`. `Representation`: `Category.Abelian`, `Category.Basic`,
`Category.Subquotients`, `Category.Twist`, `Compact.Definitions`,
`Compact.FiniteMean`, `Compact.OrbitMeanTranslation`,
`Compact.ProjectionProof`, `Compact.ProjectionStatement`,
`Conductor.Congruence`, `Derivative.Homogeneity`, `Derivative.Iteration`,
`Derivative.LevelCalculus`, `Derivative.MinusVanishing`,
`Derivative.MirabolicCharacter`, `Derivative.MirabolicDerivativeDetectionProof`,
`Derivative.MirabolicDerivativeDetectionStatement`,
`Derivative.MirabolicDerivativeVanishing`, `Derivative.MirabolicLatticeBox`,
`Derivative.MirabolicMinus`, `Derivative.MirabolicMinusExactnessStatement`,
`Derivative.MirabolicMinusNormalization`, `Derivative.MirabolicPlus`,
`Derivative.MirabolicPlusNormalization`, `Derivative.MirabolicSmoothPhiPlus`,
`Derivative.MirabolicSmoothPhiPlusAdjunction`,
`Derivative.MirabolicSmoothPhiPlusIterate`,
`Derivative.MirabolicSmoothPhiPlusProduct`, `Derivative.ShortExactFunctorLaws`,
`Dual.Definitions`, `Filtration.Definitions`, `Filtration.IsoTransport`,
`Geometric.ClosedSubgroupDefinitions`, `Geometric.CompactSmoothComparison`,
`Geometric.SmoothSupportFiltration`, `Induction.BinaryProduct`,
`Induction.BlockFactors`, `Induction.CompactQuotientProof`,
`Induction.Definitions`, `Induction.Equivalences`, `Induction.Parabolic`,
`Induction.StructuralStatement`, `Jacquet.CharacterAveraging`,
`Jacquet.Coinvariants`, `Jacquet.Localization`, `Jacquet.PositiveCharacter`,
`Jacquet.SmoothTwist`, `MatrixCoefficient.Definitions`,
`MatrixCoefficient.LawsProof`, `MatrixCoefficient.LawsStatement`,
`Mirabolic.LeftMixedProductSuccessor`, `Mirabolic.MixedProducts`,
`Parabolic.GeometricPrerequisitesStatement`, `Parabolic.QuotientCompactProof`,
`RankinSelberg.LastRowCompactOrbitProof`,
`RankinSelberg.LastRowCompactOrbitStatement`, `RankinSelberg.QuotientIntegrals`,
`RankinSelberg.ZeroRowLastRowCutoffProof`,
`RankinSelberg.ZeroRowLastRowCutoffStatement`,
`Smooth.Admissibility.CofinalProof`, `Smooth.Admissibility.CofinalStatement`,
`Smooth.Definitions`, `Smooth.SmoothPart.BasicProof`,
`Smooth.SmoothPart.BasicStatement`, `Smooth.SmoothPart.Definitions`,
`Smooth.Transfer.PullbackProof`, `Smooth.Transfer.PullbackStatement`,
`Smooth.Transfer.SubquotientProof`, `Smooth.Transfer.SubquotientStatement`,
`Tensor.Finite`, `Tensor.OneFactor`, `Twist.AdmissibilityProof`,
`Twist.AdmissibilityStatement`, `Twist.AlgebraProof`,
`Twist.AlgebraStatement`, `Twist.ContinuousCharacterProof`,
`Twist.ContinuousCharacterStatement`, `Twist.Definitions`, `Twist.RealPower`,
`Twist.SmoothProof`, `Twist.SmoothStatement`, `Twist.SubquotientDefinitions`,
`Twist.SubquotientProof`, `Twist.SubquotientStatement`, `Whittaker.Algebraic`,
`Whittaker.GeneralLinear`, `Whittaker.Iwasawa`. `Topology`:
`CompactNormCharacter`, `CompactOpen.ConjugationStabilizer`,
`CompactOpen.NeighborhoodBasis`, `CompactOpen.NeighborhoodBasisStatement`,
`Nonarchimedean.Subgroup`.

These are foundational modules: groups, Haar moduli and local fields; smooth
representations, induction, twists and Jacquet coinvariants; the published
`Ψ⁻`, `Φ⁻`, `Ψ⁺`, `Φ⁺`, `Φ̂⁺` and the `Φ⁻ ⊣ Φ̂⁺` adjunctions; the
derivative, level and homogeneity definitions (`Iteration`, `Homogeneity`);
the published derivative detection proof
`Langlands.Derivative.mirabolicDerivativeDetection` with its lattice-box and
Rankin–Selberg compact-orbit geometric lemmas; and Whittaker characters and
the Iwasawa decomposition.

Audit against the exclusions of task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4`,
condition by condition:

- Inherited exclusion set of `b711af72` (ordered-socle existence and socle
  exhaustion, segment classification, segment-socle and special-head product
  criteria and exhaustions, `AdjacentUnlinkedSegmentSocleSwap`,
  `TwoSegmentSocleCommutation`, quotient coverage, tempered uniqueness,
  `SquareIntegrableLanglandsClassification`, square-integrable and regular
  exhaustion, `GenericSegmentProductUniqueness`, ordered conversion and forward
  special square-integrability): no module of the closure states, proves or
  imports any of these. The closure contains no segment, socle, head,
  classification, exhaustion or square-integrability module.
- Detection-unit restrictions: no Ze80 §5.4 reduction or
  strong-indecomposability conclusion, and no two-supercuspidal product
  conclusion (`ab61f565`, `3c9849a4`). The published detection proof in the
  closure is the general BZ77 one that the objective permits.
- Nonadjacent-consumer and BZ77-only restrictions: no segment Jacquet formula
  (`SegmentFullJacquetFormula`, `SegmentHeadJacquetFormula`,
  `SegmentSocleJacquetFormula`, `SegmentSpecialJacquetExponentNormFormula`),
  no Ze80 §3.5 or §9.6 derivative formula, no Ze80 4.2, 9.3 or 9.7 result,
  no individual special-head, segment-socle or adjacent-commutation result.
- Shared upstream restrictions of `3238f371` revision 2 and `2e5183b1`
  revision 2: the closure has no `Langlands.Whittaker` finiteness module, no
  result of `62de5903`, and none of the listed segment-socle, linked or
  juxtaposed product structure results.
- Whittaker-finiteness independence: the closure contains none of
  `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`,
  `IrreducibleCoinvariantFinitenessStatement` or
  `LeviCuspidalCoinvariantFinitenessStatement`, and no mirabolic finite-length
  result.
- Permitted-input conditions: the closure contains no derivative exactness
  proof, no 4.14(a), highest-layer, Leibniz or `RestrictedProductLevel` result.
  `MirabolicMinusExactnessStatement` is present only as a proposition
  definition imported by `LevelCalculus`. It is a target, not a proved input,
  and no lemma used here takes it as a hypothesis. Minus exactness task
  `b65bc667` is neither used nor resumed.

The `lean_check` inspection of `hasNonzeroDerivative_leftMixed_subrepresentation`
(Lake build) reports only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

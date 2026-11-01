# Homogeneity and the unit of the mirabolic derivative adjunction

Author: Worker 749.

Module `Langlands.Representation.Derivative.MirabolicDerivativeUnitInjective`,
namespace `Langlands.Derivative`.

This module proves Zelevinsky's homogeneity criterion, Proposition 5.1,
(1) ⇔ (3), of Ze80 below. It is stated for the published order-indexed
derivative `mirabolicDerivativeOfOrder T ψ N l hl` on `P_(N+1)` and the
published right adjoint `Y = mirabolicDerivativeOfOrderRightAdjoint T ψ N l hl`.
Write `A^(l)` for `(mirabolicDerivativeOfOrder T ψ N l hl).obj A`. Write
`η_A : A → Y(A^(l))` for the published unit
`mirabolicDerivativeOfOrderUnit T ψ N l hl A`. The module proves:

- derivatives of order `l` carry injective intertwiners to injective
  intertwiners, and level is monotone along injective intertwiners;
- the kernel of `η_A` is defined as a subrepresentation of `A`
  (`mirabolicDerivativeOfOrderUnitKer`, the source's `Ker A`), and its
  derivative of order `l` is zero;
- (1) ⇒ (3): if `A` is homogeneous of level `l > 0`, then `η_A` is injective;
- (3) ⇒ (1): if `A` has an injective intertwiner into some `Y θ` and has
  level at most `l`, then `A` is homogeneous, and its level is `l` when `A`
  is nonzero;
- for `A` of level `l > 0`: `A` is homogeneous if and only if `η_A` is
  injective.

Exactness of the derivative is used. It enters only through the published
theorem `Langlands.Derivative.Mirabolic.minusExactness`, which proves the
published proposition `Mirabolic.MinusExactnessStatement F T`. No theorem
here takes a proposition definition as a hypothesis.

The direct imports are:

- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`: the
  right adjoint `Y`, the order-indexed adjunction, its nonvanishing corollary
  and the unit with its laws;
- `Langlands.Representation.Derivative.LevelCalculus`: level lemmas, some
  with exactness as an explicit hypothesis;
- `Langlands.Representation.Derivative.MirabolicMinusExactnessProof`: the
  exactness theorem.

No existing Library file is changed.

## Source

Two registered originals are used.

- Zelevinsky, *Induced representations of reductive p-adic groups II. On
  irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), source
  `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`. The
  printed page is the PDF page plus 163. §5.1, printed p.187/PDF24:
  - Definition: "A representation `τ ∈ Alg P` is called homogeneous if
    `λ(σ) = λ(τ)` for each non-zero submodule `σ ⊂ τ` (see 4.3)."
  - Proposition: "Let `τ ∈ Alg P`, `λ(τ) = k`. The following conditions are
    equivalent: (1) `τ` is homogeneous. (2) … (3) `τ` may be embedded into
    `(Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))`." Condition (2) is not formalized here.
  - Proof of (1) ⇔ (3): "(*) `Hom(σ, (Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))) = Hom(σ^(k),
    τ^(k))` for any `σ ∈ Alg P`. If (3) holds and `0 ≠ σ ⊂ τ` then the left
    part of (*) is non-zero hence `σ^(k) ≠ 0`; this proves (1). Now consider
    the morphism `A : τ → (Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))` corresponding by (*) to the
    identical morphism `τ^(k) → τ^(k)`. It follows from [I], 3.2 (f) that the
    functor `τ ↦ τ^(k)` carries `A` into the identical morphism. Therefore
    `(Ker A)^(k) = 0`. If (1) holds it follows that `Ker A = 0` i.e. `A` is
    an embedding; this proves (3)." Here [I] is BZ77.
- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ENS (4) 10 (1977), source
  `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The
  PDF page is the printed page minus 439. §3.2, printed p.451/PDF12,
  Proposition (a): "All the functors `Ψ⁻, Ψ⁺, Φ⁻, Φ⁺, Φ̂⁺` are exact." The
  Library proves this for `Φ⁻` and `Ψ⁻` as `minusExactness`. Parts (b) and
  (c) are the adjunctions behind (*), which the published
  `mirabolicDerivativeOfOrderAdjunction` iterates. Part (f) is not used; see
  below.

No errata entry for either source is registered in the literature index, and
the Library has no errata note for them.

### Conventions

The published `mirabolic N` is the source's `P_(N+1)`. For `0 < l ≤ N + 1`,
`A^(l)` is a representation of `GL_(N+1-l)`, and `Y` goes from `GL_(N+1-l)`
to `P_(N+1)`. As documented in `MirabolicSmoothPhiPlusIterate`, `Y` is the
source's `(Φ̂⁺)^(l-1) ∘ Ψ⁺`, up to the carrier-universe lift and the published
rank transport. The unit `η_A` is the source's morphism `A`.

The published definitions in `Langlands.Representation.Derivative.Homogeneity`
are used unchanged:

- `HasNonzeroDerivative T ψ A k`: `∃ hk : 0 < k ∧ k ≤ N + 1`,
  `Nontrivial (A^(k))`;
- `level T ψ A`: `Nat.findGreatest (HasNonzeroDerivative T ψ A) (N + 1)`, the
  greatest order in `1, …, N + 1` with nonzero derivative, defaulting to `0`.
  This is the source's `λ` of Ze80 §4.3;
- `IsHomogeneous T ψ A`: every invariant subspace `U ≠ ⊥` of `A` has
  `level (U) = level A`. This is the source's definition, with submodules
  read as invariant subspaces.

## The proofs

### Derivatives preserve injections

- `mirabolicDerivativeOfOrder_map_injective`: if `f : A ⟶ B` is injective,
  so is `f^(l)`. This is the published
  `LevelCalculus.map_injective_of_exact`, applied to
  `LevelCalculus.mapsShortExact_mirabolicDerivativeOfOrder T ψ
  (minusExactness F T) N l hl`. That lemma completes an injective `f` to the
  short exact sequence `0 → A → B → B/A → 0` and applies exactness.
- `level_mono_of_injective`: an injective `f : A ⟶ B` gives
  `level A ≤ level B`. This is the published `LevelCalculus.level_le_of_injective`
  with the same exactness theorem.

### (1) ⇒ (3): injectivity of the unit

- `mirabolicDerivativeOfOrderUnitKer T ψ N l hl A` is the definition
  `SmoothRep.subrepresentation A (η_A).ker`: the kernel of `η_A`, as a smooth
  subrepresentation of `A`. This is the source's `Ker A`.
- `subsingleton_mirabolicDerivativeOfOrder_unit_ker`: let
  `K = mirabolicDerivativeOfOrderUnitKer T ψ N l hl A` and `ι : K → A` its
  inclusion (`SmoothRep.subtype`). Then `K^(l)` is zero (a subsingleton). Indeed
  `η_A ∘ ι = 0` by the definition of the kernel. The published
  `mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp` then gives
  `ι^(l) = 0`: the adjunct of `η_A ∘ ι` is `ι^(l)`, by naturality of the
  adjunction. On the other hand `ι^(l)` is injective by the previous section.
  An injective zero map has a zero source.
- `mirabolicDerivativeOfOrderUnit_injective_of_forall`: if every invariant
  subspace `U ≠ ⊥` of `A` has `HasNonzeroDerivative T ψ U l`, then `η_A` is
  injective. Otherwise `K ≠ ⊥`, so `K^(l)` would be nonzero, contradicting
  the previous item.
- `mirabolicDerivativeOfOrderUnit_injective`: if `A` is homogeneous and
  `level A = l`, then `η_A` is injective. Every `U ≠ ⊥` has
  `level U = level A = l ≠ 0`. The published
  `LevelCalculus.hasNonzeroDerivative_level` then gives a nonzero derivative
  of order `level U = l`, and the previous item applies. This is the source's
  (1) ⇒ (3).

This route differs from the source. The source applies [I] 3.2(f) to show
that the derivative carries `A` to the identity of `τ^(k)`, and deduces
`(Ker A)^(k) = 0`. Here the adjunction identity for composites with the unit
is used instead, together with injectivity of `ι^(l)`. Neither BZ77 3.2(f)
nor the statement that the derivative of `η_A` is the identity is stated or
used.

- `hasNonzeroDerivative_of_isHomogeneous`: let `X` be homogeneous with
  `level X = l > 0`, and let `f : W ⟶ X` be injective with `W` nontrivial.
  Then `W` has a nonzero derivative of order `l` and none of higher order.
  The published `LevelCalculus.level_eq_of_isHomogeneous` gives
  `level W = level X`; then `LevelCalculus.hasNonzeroDerivative_level` and
  `le_level_of_hasNonzeroDerivative` apply. This restatement is for
  consumers and is not in the source. It uses no exactness.

### (3) ⇒ (1): homogeneity from an embedding into `Y`

In this section `A` has an arbitrary carrier universe `uA`. `θ` is an
arbitrary representation of `GL_(N+1-l)` in universe `uV`, and
`Φ : A → Y θ` is an injective intertwiner.

- `hasNonzeroDerivative_of_injective_rightAdjoint`: for every injective
  `f : W ⟶ A` with `W` nontrivial, `W` has a nonzero derivative of order `l`.
  Pick `x ≠ 0` in `W`. Then `Φ (f x) ≠ 0`, so `Φ ∘ f ≠ 0`. The published
  nonvanishing corollary `hasNonzeroDerivative_of_ne_zero` of the adjunction
  gives the claim. This is the source's "the left part of (*) is non-zero
  hence `σ^(k) ≠ 0`". It uses no exactness.
- `le_level_of_injective_rightAdjoint`: for nontrivial `A`, `l ≤ level A`.
  This is the previous item with `f` the identity, and
  `le_level_of_hasNonzeroDerivative`. It uses no exactness.
- `isHomogeneous_of_injective_rightAdjoint`: if `level A ≤ l`, then `A` is
  homogeneous. For every injective `f : W ⟶ A` with `W` nontrivial,
  `level W ≤ level A ≤ l` by `level_mono_of_injective`, and `l ≤ level W` by
  the first item. So `level W = l`. The published
  `LevelCalculus.isHomogeneous_of_forall_injective`, with constant `l`, gives
  homogeneity. This is the source's (3) ⇒ (1). The source leaves the
  inequality `λ(σ) ≤ λ(τ)` implicit; here it is `level_mono_of_injective`,
  which uses exactness.
- `level_eq_of_injective_rightAdjoint`: under the same hypotheses, a
  nontrivial `A` has `level A = l`.

These statements are more general than the source's (3) ⇒ (1): `θ` is
arbitrary rather than `τ^(k)`, the universe of `A` is arbitrary, and only
`level A ≤ l` is assumed.

### (1) ⇔ (3)

`isHomogeneous_iff_unit_injective`: for `A` in universe `uV` with
`level A = l` (and `0 < l ≤ N + 1`), `A` is homogeneous if and only if
`η_A` is injective. The forward direction is
`mirabolicDerivativeOfOrderUnit_injective`. The backward direction is
`isHomogeneous_of_injective_rightAdjoint` with `θ = A^(l)` and `Φ = η_A`.
The source's (3) asks for some embedding. The forward direction produces the
specific embedding `η_A`, and the backward direction holds for any embedding
by `isHomogeneous_of_injective_rightAdjoint`. So both readings of (3) are
covered. The source allows `λ(τ) = k = 0`, that is `τ = 0`, where both
conditions are trivial; here `0 < l` is required, as the unit is only
defined for valid orders.

## Parameters, topology and universes

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
`T : F.TopologicalData` is an arbitrary supplied topological realization, and
every topological statement installs `letI := T.topology`. The additive
character is
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`; its
nontriviality is not used. All `N : ℕ` are allowed, and every order `l` with
`0 < l ≤ N + 1` (`hl : 0 < l ∧ l ≤ N + 1`) is allowed. There is no case
split on ranks.

Representations are smooth complex representations
`SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier)`. The unit statements need
`θ = A^(l)`, so there `A` has universe `uV`. In the (3) ⇒ (1) section, `A` and
`W` have universe `uA` and `θ` has universe `uV`. The exactness theorem is
`Mirabolic.minusExactness`, instantiated at the carrier universe in use.

The inspected level parameters are `uV, uF` for
`mirabolicDerivativeOfOrderUnitKer` and `isHomogeneous_iff_unit_injective`,
and `uA, uV, uF` for `isHomogeneous_of_injective_rightAdjoint`. No universe is
resized.

These three inspected declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The main statements are Ze80 §5.1, Proposition, (1) ⇔ (3), in the iff form
`isHomogeneous_iff_unit_injective` and in the generalized directions above.
The Lean proofs are internal. The (3) ⇒ (1) direction follows the source.
The (1) ⇒ (3) direction replaces the source's appeal to BZ77 3.2(f) by the
adjunction identity of the published unit and exactness. The definition
`mirabolicDerivativeOfOrderUnitKer` is the source's `Ker A`, formed with the
published `SmoothRep.subrepresentation` and Mathlib's kernel. The remaining
lemmas (injectivity of derivative maps, monotonicity of level, the kernel of
the unit, the variant with arbitrary hypotheses on subspaces,
`hasNonzeroDerivative_of_isHomogeneous` and the level corollaries) are
routine derived statements, which the source uses without stating them. No
other original-literature theorem is asserted.

## Import and dependency audit

### Complete import inventory

The recursive `Langlands` import closure of this module was computed by
following every `import` line, starting from this module, through the Library
at base `8f53f05bb76983088fd64f190658c6ac4c3edc1b`. It consists of exactly 133
modules: this module and the following 132 published, paired Library
modules. The 26 entries marked "(statement)" contain Prop-valued statement
definitions.

- `Langlands.Analysis.Local.QuotientMeasure`
- `Langlands.Group.GL.Basic`
- `Langlands.Group.GL.BlockModulus`
- `Langlands.Group.GL.Blocks`
- `Langlands.Group.GL.Mirabolic`
- `Langlands.Group.GL.MirabolicMixedProductSubgroups`
- `Langlands.Group.GL.MirabolicModulusProof`
- `Langlands.Group.GL.MirabolicModulusStatement` (statement)
- `Langlands.Group.GL.MirabolicOppositeIntersection`
- `Langlands.Group.GL.MirabolicProjection`
- `Langlands.Group.GL.MirabolicRadical`
- `Langlands.Group.GL.Nonarchimedean`
- `Langlands.Group.GL.NonarchimedeanStatement` (statement)
- `Langlands.Group.GL.NormalizedCharacter`
- `Langlands.Group.GL.OppositeBlocks`
- `Langlands.Group.GL.Padic`
- `Langlands.Group.GL.PadicBlocks`
- `Langlands.Group.GL.RankMaps`
- `Langlands.Group.GL.RankReindex`
- `Langlands.Group.GL.UpperUnipotent`
- `Langlands.Group.GL.UpperUnipotentCompactContainmentProof`
- `Langlands.Group.GL.UpperUnipotentCompactContainmentStatement` (statement)
- `Langlands.Group.HaarModulus`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.HarmonicAnalysis.Conductor`
- `Langlands.HarmonicAnalysis.PadicAdditiveConductorProof`
- `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` (statement)
- `Langlands.HarmonicAnalysis.PadicLatticeTopology`
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
- `Langlands.LocalFactor.Harmonic.Statement` (statement)
- `Langlands.LocalField.Canonical`
- `Langlands.LocalField.Definitions`
- `Langlands.LocalField.Normalization.Definitions`
- `Langlands.LocalField.Normalization.Proof`
- `Langlands.LocalField.Normalization.Statement` (statement)
- `Langlands.LocalField.Topology`
- `Langlands.Representation.Category.Abelian`
- `Langlands.Representation.Category.Basic`
- `Langlands.Representation.Category.Subquotients`
- `Langlands.Representation.Category.Twist`
- `Langlands.Representation.Compact.Definitions`
- `Langlands.Representation.Compact.FiniteMean`
- `Langlands.Representation.Compact.OrbitMeanTranslation`
- `Langlands.Representation.Compact.ProjectionProof`
- `Langlands.Representation.Compact.ProjectionStatement` (statement)
- `Langlands.Representation.Conductor.Congruence`
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.LevelCalculus`
- `Langlands.Representation.Derivative.MinusVanishing`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionProof`
- `Langlands.Representation.Derivative.MirabolicDerivativeDetectionStatement` (statement)
- `Langlands.Representation.Derivative.MirabolicDerivativeVanishing`
- `Langlands.Representation.Derivative.MirabolicLatticeBox`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessProof`
- `Langlands.Representation.Derivative.MirabolicMinusExactnessStatement` (statement)
- `Langlands.Representation.Derivative.MirabolicMinusNormalization`
- `Langlands.Representation.Derivative.MirabolicPlus`
- `Langlands.Representation.Derivative.MirabolicPlusNormalization`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`
- `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`
- `Langlands.Representation.Derivative.ShortExactFunctorLaws`
- `Langlands.Representation.Dual.Definitions`
- `Langlands.Representation.Filtration.Definitions`
- `Langlands.Representation.Filtration.IsoTransport`
- `Langlands.Representation.Geometric.ClosedSubgroupDefinitions`
- `Langlands.Representation.Geometric.CompactSmoothComparison`
- `Langlands.Representation.Geometric.SmoothSupportFiltration`
- `Langlands.Representation.Induction.BinaryProduct`
- `Langlands.Representation.Induction.BlockFactors`
- `Langlands.Representation.Induction.CompactQuotientProof`
- `Langlands.Representation.Induction.Definitions`
- `Langlands.Representation.Induction.Equivalences`
- `Langlands.Representation.Induction.Parabolic`
- `Langlands.Representation.Induction.StructuralStatement` (statement)
- `Langlands.Representation.Jacquet.CharacterAveraging`
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.ExactProof`
- `Langlands.Representation.Jacquet.ExactStatement` (statement)
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.LocalizationExactnessProof`
- `Langlands.Representation.Jacquet.LocalizationExactnessStatement` (statement)
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement` (statement)
- `Langlands.Representation.Mirabolic.MixedProducts`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitProof`
- `Langlands.Representation.RankinSelberg.LastRowCompactOrbitStatement` (statement)
- `Langlands.Representation.RankinSelberg.Measures`
- `Langlands.Representation.RankinSelberg.QuotientIntegrals`
- `Langlands.Representation.RankinSelberg.UnimodularityStatement` (statement)
- `Langlands.Representation.RankinSelberg.UnipotentUnimodularity`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffProof`
- `Langlands.Representation.RankinSelberg.ZeroRowLastRowCutoffStatement` (statement)
- `Langlands.Representation.Smooth.Admissibility.CofinalProof`
- `Langlands.Representation.Smooth.Admissibility.CofinalStatement` (statement)
- `Langlands.Representation.Smooth.Definitions`
- `Langlands.Representation.Smooth.SmoothPart.BasicProof`
- `Langlands.Representation.Smooth.SmoothPart.BasicStatement` (statement)
- `Langlands.Representation.Smooth.SmoothPart.Definitions`
- `Langlands.Representation.Smooth.Transfer.PullbackProof`
- `Langlands.Representation.Smooth.Transfer.PullbackStatement` (statement)
- `Langlands.Representation.Smooth.Transfer.SubquotientProof`
- `Langlands.Representation.Smooth.Transfer.SubquotientStatement` (statement)
- `Langlands.Representation.Tensor.Finite`
- `Langlands.Representation.Tensor.OneFactor`
- `Langlands.Representation.Twist.AdmissibilityProof`
- `Langlands.Representation.Twist.AdmissibilityStatement` (statement)
- `Langlands.Representation.Twist.AlgebraProof`
- `Langlands.Representation.Twist.AlgebraStatement` (statement)
- `Langlands.Representation.Twist.ContinuousCharacterProof`
- `Langlands.Representation.Twist.ContinuousCharacterStatement` (statement)
- `Langlands.Representation.Twist.Definitions`
- `Langlands.Representation.Twist.RealPower`
- `Langlands.Representation.Twist.SmoothProof`
- `Langlands.Representation.Twist.SmoothStatement` (statement)
- `Langlands.Representation.Twist.SubquotientDefinitions`
- `Langlands.Representation.Twist.SubquotientProof`
- `Langlands.Representation.Twist.SubquotientStatement` (statement)
- `Langlands.Representation.Whittaker.Algebraic`
- `Langlands.Representation.Whittaker.GeneralLinear`
- `Langlands.Topology.CompactNormCharacter`
- `Langlands.Topology.CompactOpen.ConjugationStabilizer`
- `Langlands.Topology.CompactOpen.NeighborhoodBasis`
- `Langlands.Topology.CompactOpen.NeighborhoodBasisStatement` (statement)
- `Langlands.Topology.Nonarchimedean.Subgroup`

The closure contains no other project module. Everything else imported is
Mathlib.

### New modules compared with the right-adjoint module

The closure of the published `MirabolicSmoothPhiPlusIterate` has 97
modules, all in the list above. The 36 new modules are this module, the
direct imports `Derivative.LevelCalculus` and
`Derivative.MirabolicMinusExactnessProof`, and these 33 Library modules,
grouped by how they enter.

Reached through `MirabolicMinusExactnessProof` (the published exactness
proof and its own closure; the starred ones are also reached through
`LevelCalculus`):

- `Derivative.MirabolicMinusExactnessStatement`* (statement): the exactness
  proposition `MinusExactnessStatement` and `MapsShortExactIntertwiners`;
- `Jacquet.ExactStatement` (statement), `Jacquet.ExactProof`: compact
  detection and exactness of smooth complex coinvariants;
- `Jacquet.LocalizationExactnessStatement` (statement),
  `Jacquet.LocalizationExactnessProof`: exactness of character-localized
  coinvariants;
- `Group.GL.UpperUnipotentCompactContainmentStatement` (statement),
  `Group.GL.UpperUnipotentCompactContainmentProof`: compact subsets of the
  upper-unipotent group lie in compact open subgroups;
- `Compact.Definitions`*, `Compact.FiniteMean`*,
  `Compact.OrbitMeanTranslation`*, `Compact.ProjectionStatement`*
  (statement), `Compact.ProjectionProof`*: compact-subgroup averaging and
  its projection laws;
- `Conductor.Congruence`: congruence subgroups of `GL_(n+1)`;
- `RankinSelberg.Measures`, `RankinSelberg.UnimodularityStatement`
  (statement), `RankinSelberg.UnipotentUnimodularity`: concrete Haar
  measures and right invariance of the upper-unipotent Haar measure.

Reached only through `LevelCalculus`:

- `Derivative.ShortExactFunctorLaws`: identity and composition of exact
  functors;
- `Derivative.MirabolicDerivativeDetectionStatement` (statement),
  `Derivative.MirabolicDerivativeDetectionProof`,
  `Derivative.MirabolicDerivativeVanishing`, `Derivative.MinusVanishing`,
  `Derivative.MirabolicLatticeBox`: the published positive-order derivative
  detection theorem `mirabolicDerivativeDetection` and its lemmas;
- `Jacquet.CharacterAveraging`: character-twisted averaging over compact
  open subgroups;
- `RankinSelberg.LastRowCompactOrbitStatement` (statement),
  `RankinSelberg.LastRowCompactOrbitProof`,
  `RankinSelberg.ZeroRowLastRowCutoffStatement` (statement),
  `RankinSelberg.ZeroRowLastRowCutoffProof`, `RankinSelberg.QuotientIntegrals`,
  `Analysis.Local.QuotientMeasure`: the compact open last-row orbit, the
  compact last-row cutoff for zero-row coefficient functions, integration on
  coset spaces and the JPSS quotient integrals;
- `HarmonicAnalysis.Conductor`, `HarmonicAnalysis.PadicAdditiveConductorProof`,
  `HarmonicAnalysis.PadicLatticeTopology`, `LocalFactor.Harmonic.Statement`
  (statement): character conductors, compactness of lattices, and local
  Fourier inversion and Haar normalization statements.

### Statement definitions and proved inputs

The 26 statement modules supply Prop-valued definitions, which are targets,
not proved inputs. No theorem of this module takes any of them, or any other
Prop-valued statement, as a hypothesis. The only statement used as a proved
input is `Mirabolic.MinusExactnessStatement F T`, through its published proof
`Mirabolic.minusExactness`. That proof is a complete Lean proof, so every
statement it relies on is itself proved there or in its own closure.
`LevelCalculus` takes `MinusExactnessStatement` as an explicit hypothesis
`hE` in some lemmas; this module always supplies `hE` as `minusExactness`.
The target statement module
`Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`
is not in the closure.

### Actual proof dependencies

The proofs use only these imported declarations, together with Mathlib
(`Representation.IntertwiningMap` and its kernel
`Representation.IntertwiningMap.ker`, submodules and basic category
theory):

- `Derivative.MirabolicMinusExactnessProof`: `Mirabolic.minusExactness`;
- `Derivative.LevelCalculus`: `map_injective_of_exact`,
  `mapsShortExact_mirabolicDerivativeOfOrder`, `level_le_of_injective`,
  `hasNonzeroDerivative_level`, `level_eq_of_isHomogeneous` and
  `isHomogeneous_of_forall_injective`;
- `Derivative.Homogeneity`: `mirabolicDerivativeOfOrder`,
  `HasNonzeroDerivative`, `level`, `IsHomogeneous` and
  `le_level_of_hasNonzeroDerivative`;
- `Derivative.MirabolicSmoothPhiPlusIterate`:
  `mirabolicDerivativeOfOrderRightAdjoint`, `mirabolicDerivativeOfOrderUnit`,
  `mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp` and
  `hasNonzeroDerivative_of_ne_zero`;
- `Category.Subquotients`: `SmoothRep.subrepresentation`, `SmoothRep.subtype`
  and `SmoothRep.subtype_injective`.

None of the `LevelCalculus` lemmas used relies on the detection theorem.
In `LevelCalculus`, detection is used only by `level_pos` and by later lemmas
built on it (`level_ne_zero_iff`, `nontrivial_phiMinus_iff`), none of which
is used here or by the lemmas used here. The remaining modules of the inventory
enter only through the imports of these modules.

### Condition-by-condition exclusion audit

The conditions are those of the complete inherited exclusion set in the
context of task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` revision 2, from
"Complete inherited exclusion set" to the end. A module can depend only on
declarations in its import closure. So it suffices to check two things: no
excluded statement, proof or consequence lies in the 133 modules above, and
no excluded conclusion is assumed.

1. **Exclusion list of `b711af72` (objective).** Ordered-socle existence
   `23189526`, socle exhaustion `f3a69bc8`, analytic segment classification
   `aca8805b`, segment-socle product irreducibility `23e98d90`, the final
   criterion `2ae5cbe5`, `AdjacentUnlinkedSegmentSocleSwap`,
   `TwoSegmentSocleCommutation`, the special-head criterion `8364e73f`,
   special-head exhaustion `3bfb61fa`, ordered special-head existence
   `ebea9a8a`, quotient coverage `20e4e1c6`, tempered block uniqueness
   `52e97845`, `SquareIntegrableLanglandsClassification` / `1cb45da2`,
   square-integrable exhaustion `cd8ab97c`, regular exhaustion `bf433f0a`,
   `GenericSegmentProductUniqueness` / `30341ae4`, ordered conversion
   `8252833d` and forward special-segment square-integrability `5eece9e8`:
   satisfied. The inventory contains no `Classification`, segment,
   multisegment, socle, head, tempered, square-integrability or exhaustion
   module, and no such conclusion is assumed. A case-insensitive text search
   of the 133 Lean sources for "segment", "socle", "classification",
   "exhaustion", "supercuspidal", "leibniz", "strongindecompos", "finiteness"
   and "finitelength" finds only two files. `Jacquet.CharacterAveraging` has
   a section `Exhaustion`, about an increasing exhaustion of a unipotent group
   by compact open subgroups. `Category.Basic` defines `HasFiniteLength`
   (item 7).
2. **Operator-paused minus exactness `b65bc667`.** Satisfied. That task is
   done: its accepted proof `d307cd07` published `Mirabolic.minusExactness`
   in `Derivative.MirabolicMinusExactnessProof` (author Worker 127). This
   module imports that published theorem. It does not resume, replace or
   bypass the task, and Worker 127 was not contacted.
3. **Detection-unit restrictions.** The combined Ze80 §5.4 reduction, its
   strong-indecomposability conclusion (`ff4738d8`), the nonadjacent
   product `3c9849a4` and the full product structure `ab61f565`: satisfied.
   None of these is in the closure or assumed; in particular
   `Derivative.MirabolicStrongIndecomposabilityStatement` is absent. The
   published detection modules listed above are in the closure through
   `LevelCalculus`. Their own closure lies inside the inventory, so it
   contains none of these consumers either. This module uses no detection
   result.
4. **Additional nonadjacent-consumer list.** `67279e36`, `4ca79bbd`,
   `aca8805b`, `SegmentSpecialEssentialSquareIntegrability` / `5eece9e8`,
   `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `8252833d`, `52e97845`, `1cb45da2`,
   `cd8ab97c`, `bf433f0a`, `8364e73f`, `30341ae4`,
   `OrderedMultisegmentSocleExistence` / `23189526`,
   `MultisegmentSocleExhaustion` / `f3a69bc8`,
   `SegmentSocleProductIrreducibility` / `2ae5cbe5`, adjacent socle
   commutation `e3634665`, `SegmentFullJacquetFormula` / `ed48ae06` and its
   proof, `SegmentHeadJacquetFormula` / `55ad1e10`,
   `SegmentSocleJacquetFormula` / `b95105c6` and
   `SegmentSpecialJacquetExponentNormFormula` / `92aea10f`: satisfied. The
   Jacquet modules in the closure are `Jacquet.Coinvariants`,
   `Jacquet.Localization`, `Jacquet.PositiveCharacter`,
   `Jacquet.SmoothTwist`, `Jacquet.CharacterAveraging`, `Jacquet.ExactStatement`,
   `Jacquet.ExactProof`, `Jacquet.LocalizationExactnessStatement` and
   `Jacquet.LocalizationExactnessProof`. They contain general coinvariant,
   localization, averaging and exactness results and character twists, not
   segment Jacquet formulas.
5. **Full-formula consumer restrictions.** No Ze80 §3.5 or §9.6 segment
   derivative formula, no segment product criterion (Ze80 4.2, 9.7), no
   analytic or square-integrability result (Ze80 9.3) and no classification
   or exhaustion theorem: satisfied. From Zelevinsky 1980 only Proposition
   5.1, (1) ⇔ (3), is formalized, by the internal proofs above. No Ze80
   theorem is assumed. The derivative results used are the exactness of
   `Φ⁻` and `Ψ⁻` (BZ77 3.2(a)), proved and published as `minusExactness`,
   and the published adjunction and unit of `MirabolicSmoothPhiPlusIterate`
   and level lemmas of `LevelCalculus`, all with complete Lean proofs. The
   `LevelCalculus` Markdown names Zelevinsky's Theorem 6.2 as an intended
   consumer only; that module proves general level lemmas, imports no
   segment module and uses no segment result. No Leibniz filtration,
   mixed-product derivative or product-restriction module is in the
   closure; in particular the Library's `Derivative.LeibnizRestrictionExact`
   is absent. The segment-socle part of task `8e5b4563` is not used.
6. **Shared upstream scope of `3238f371` revision 2.** Satisfied.
   `Langlands.Whittaker.SupercuspidalCoinvariantFinitenessStatement`, the
   all-character single-block conclusion `62de5903` and their consequences
   are not in the closure or assumed. No missing proof is replaced by a
   consumer assumption. Worker 127 was not contacted. The parent list
   (`30341ae4`, `3bfb61fa`, `ebea9a8a`, `20e4e1c6`, `8252833d`, `52e97845`,
   `1cb45da2`, `cd8ab97c`, `bf433f0a`) is covered by items 1 and 4.
7. **Independence section of `2e5183b1` revision 2.**
   `UnlinkedSegmentSocleProductIrreducible`,
   `LinkedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSoclePairReducible` (`23e98d90`, `a55c4267`, `8fa9f68b`),
   `JuxtaposedSegmentSocleReverseProductStructure`,
   `LinkedSegmentSocleReverseProductQuotientHom` (`7ff2a1e9`),
   `SegmentSocleProductIrreducibility` (`2ae5cbe5`),
   `AdjacentUnlinkedSegmentSocleSwap` (`e3634665`, `cded83f3`),
   `TwoSegmentSocleCommutation` (`426911b4`, `66e3b87c`),
   `LinkedSegmentSocleGluing` (`c84cd52c`, `6780b79c`), the remaining tasks
   of that list (covered by items 1 and 4) and `SegmentHeadProductIrreducibility`
   (`8364e73f`): satisfied, none in the closure. Of the shared lower inputs
   named there, the derivative functors (`Φ⁻`, `Ψ⁻`, `Ψ⁺`, the iterated
   derivative and its rank transport) and exactness are used. Their
   independence is checked by this inventory, since their modules and
   closures lie in it. No Leibniz filtration, geometric lemma,
   cuspidal-support or finite-length theorem module is in the closure.
   `Geometric.ClosedSubgroupDefinitions`, `Geometric.SmoothSupportFiltration`
   and `Geometric.CompactSmoothComparison` are support-filtration definitions
   and the compact-to-smooth inclusion, not the BZ77 geometric lemma.
   `Category.Basic` defines the predicate `HasFiniteLength`, a definition
   that is not used here. The product modules `Induction.BinaryProduct`,
   `Induction.BlockFactors` and `Mirabolic.MixedProducts` define product
   functors only. They contain no product structure, irreducibility or
   reducibility theorem, and no product functor is used here.
8. **BZ77-only upstream restrictions.** No segment derivative formula,
   segment-socle or head existence, Jacquet formula or segment
   classification; no part (b), (d), (e), (f) of the parent six-statement
   contribution; no `TwoSupercuspidalNonadjacentProductIrreducible`
   (`3c9849a4`) or `TwoSupercuspidalProductStructure` (`ab61f565`):
   satisfied, none in the closure or assumed. Its additional consumer list
   is the list of item 4.
9. **Whittaker-finiteness independence.**
   `Langlands.Whittaker.IrreducibleCoinvariantFinitenessStatement` and parent
   `5ab445dc`, `LeviCuspidalCoinvariantFinitenessStatement` and proof task
   `3ff5c8fb`, their consequences, and the mirabolic finite-length route of
   task `5428fe2c`: satisfied. No finiteness or finite-length theorem module
   is in the closure. The closure contains two Whittaker modules.
   `Whittaker.Algebraic` defines left-equivariant functions, equivariant
   functionals and coefficient models with their elementary laws.
   `Whittaker.GeneralLinear` defines the standard character
   `ψ(Σ u_(i,i+1))`, its inverse and scaled variants, GL coefficient
   models and the predicate `IsGeneric`. They enter the closure through
   three importers: `Derivative.MirabolicCharacter` (which identifies the
   mirabolic character `θ` with a restriction of the standard character),
   `Jacquet.CharacterAveraging` (imports `Whittaker.Algebraic`) and
   `RankinSelberg.QuotientIntegrals` (imports `Whittaker.GeneralLinear`).
   They contain no coinvariant finiteness statement or theorem, and none of
   their declarations is used directly here.

The proofs use no `sorry`, `admit` or new axiom. This inventory and audit
are an author audit, not independent acceptance evidence.

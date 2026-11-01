# The right adjoint of the mirabolic derivative

Author: Worker 749.

This module builds the right adjoint of the published mirabolic derivative,
`Y = (Φ̂⁺)^k ∘ Ψ⁺`, where `Ψ⁻ ∘ (Φ⁻)^k` is the derivative being adjoined. It
proves the adjunction as an explicit complex-linear equivalence of intertwiner
spaces, natural in both arguments. It also proves the same for the
order-indexed derivative `mirabolicDerivativeOfOrder`, through its published
rank transport. It adds a nonvanishing corollary and the unit `τ → Y(τ^(l))`
with its laws.

All functors are the actual published or companion functors:

- `Φ⁻`, `Ψ⁻` from `Langlands.Representation.Derivative.MirabolicMinus`;
- `phiMinusIterate` and `mirabolicDerivative` from
  `Langlands.Representation.Derivative.Iteration`;
- `mirabolicRankCast`, `mirabolicDerivativeOfOrder` and
  `HasNonzeroDerivative` from `Langlands.Representation.Derivative.Homogeneity`;
- the normalized `Ψ⁺` from
  `Langlands.Representation.Derivative.MirabolicPlusNormalization`;
- `Φ̂⁺` and the adjunctions `Φ⁻ ⊣ Φ̂⁺`, `Ψ⁻ ⊣ Ψ⁺` from the two companion
  modules `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus` and
  `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`;
- the carrier lift `MixedProductTensor.liftFunctor` from
  `Langlands.Representation.Mirabolic.MixedProducts`.

`Hom` below is the space `Representation.IntertwiningMap` of complex-linear
intertwiners. Exactness is neither used nor stated, and neither is injectivity
of the unit. The module does not prove BZ77 §3.2(d), (e) or (f).

The direct imports are
`Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`,
`Langlands.Representation.Derivative.Homogeneity` and
`Langlands.Representation.Mirabolic.MixedProducts`. No existing Library file
is changed.

## Source

Two registered originals are used.

- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups I*, Ann. Sci. ENS (4) 10 (1977), source
  `bernstein-zelevinsky-1977-induced-i`, SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`. The PDF
  page is the printed page minus 439.
  - §3.2, printed p.451/PDF12. Proposition (b): "`Ψ⁻` is left adjoint to
    `Ψ⁺` …"; (c): "`Φ⁻` is left adjoint to `Φ̂⁺`". These are the two
    adjunctions of the companion module, which this module iterates.
  - §3.5, printed p.452/PDF13: the derivative of `τ ∈ Alg P_n` is
    `τ^(k) = Ψ⁻ (Φ⁻)^(k-1) (τ)`, a representation of `G_(n-k)`. The published
    `mirabolicDerivativeOfOrder` formalizes it.
- Zelevinsky, *Induced representations of reductive p-adic groups II. On
  irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), source
  `zelevinsky-1980-induced-ii`, SHA-256
  `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`.
  - §5.1, printed p.187/PDF24, proof of the homogeneity criterion. For
    `τ ∈ Alg P_n`, the source writes "(*)
    `Hom(σ, (Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))) = Hom(σ^(k), τ^(k))` by [I] 3.2(b) and
    (c)". It then takes "the morphism `A : τ → (Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))`
    corresponding by (*) to the identity". Here [I] is BZ77.

No errata entry for either source is registered in the literature index, and
the Library has no errata note for them.

### Index conventions

The published `mirabolic n` is the source's `P_(n+1)`. The companion
`phiHatPlus T ψ n` goes from `P_(n+1)` to `P_(n+2)`, and the published
`phiMinus T ψ n` goes back. `psiPlus T n` goes from `GL_n` to `P_(n+1)`, and
`psiMinus T n` goes back. The published `phiMinusIterate T ψ n k` goes from
`P_(n+k+1)` to `P_(n+1)`, with
`phiMinusIterate n (k + 1) = phiMinus (n + k) ⋙ phiMinusIterate n k`.
`mirabolicDerivative T ψ n k = phiMinusIterate n k ⋙ psiMinus n` goes from
`P_(n+k+1)` to `GL_n`. For `0 < l ≤ N + 1`, `mirabolicDerivativeOfOrder T ψ N l`
is the rank transport along `N = (N + 1 - l) + (l - 1)` followed by
`mirabolicDerivative (N + 1 - l) (l - 1)`. It is the source's derivative
`τ ↦ τ^(l)` of order `l` on `P_(N+1)`.

## The construction

### Intertwiners into a carrier lift

The companion `Φ̂⁺` raises the carrier universe from `uV` to `max uF uV`, while
`Ψ⁺ θ` stays in `uV`. So `Ψ⁺ θ` is first lifted by the published
`MixedProductTensor.liftFunctor.{uF, uV, uF}`, whose carrier is `ULift V` with
`g • up v = up (g • v)`. `liftHomEquiv A B` is the linear equivalence
`Hom(A, lift B) ≃ Hom(A, B)` given by composition with `ULift.down`, with
inverse composition with `ULift.up`. `liftHomEquiv_apply` and
`liftHomEquiv_symm_apply` record the formulas. `liftHomEquiv_comp_left` and
`liftHomEquiv_comp_right` are naturality in `A` and in `B`. All four hold by
definition.

### Iterated `Φ̂⁺`

`phiHatPlusIterate T ψ n k` is the functor `(Φ̂⁺)^k` from `P_(n+1)` to `P_(n+k+1)`
in the carrier universe `max uF uV`. It is defined by recursion on `k`:
`phiHatPlusIterate n 0 = 𝟭` and
`phiHatPlusIterate n (k + 1) = phiHatPlusIterate n k ⋙ phiHatPlus (n + k)`.
This mirrors the published `phiMinusIterate`. The step is the companion
`Mirabolic.phiHatPlus.{max uF uV}`, which keeps the universe `max uF uV`.
`phiHatPlusIterate_zero` and `phiHatPlusIterate_succ` record the recursion.
`phiHatPlusIterate_map_injective` shows that `(Φ̂⁺)^k` sends injective
intertwiners to injective intertwiners, by induction from the companion
`phiHatPlus_map_injective`.

`phiHatPlusIterateAdjunction T ψ n k A X` is the iterated adjunction
`Hom(A, (Φ̂⁺)^k X) ≃ₗ[ℂ] Hom((Φ⁻)^k A, X)`. For `k = 0` it is the identity.
For `k + 1` it is the companion `phiHatPlusAdjunction T ψ (n + k)`, which turns
`Hom(A, Φ̂⁺((Φ̂⁺)^k X))` into `Hom(Φ⁻ A, (Φ̂⁺)^k X)`, followed by the
equivalence for `k` applied to `Φ⁻ A`. The result lands in
`Hom((Φ⁻)^k (Φ⁻ A), X)`, which is definitionally
`Hom(phiMinusIterate n (k + 1) A, X)`. `phiHatPlusIterateAdjunction_zero` and
`phiHatPlusIterateAdjunction_succ` record the recursion. Naturality
`phiHatPlusIterateAdjunction_comp_left` (in `A`, against
`phiMinusIterate.map`) and `phiHatPlusIterateAdjunction_comp_right` (in `X`,
against `phiHatPlusIterate.map`) is proved by induction on `k`. The step uses
the companion naturality lemmas `phiHatPlusAdjunction_comp_left` and
`phiHatPlusAdjunction_comp_right`.

### The right adjoint `Y_(n,k)`

`mirabolicDerivativeRightAdjoint T ψ n k` is
`psiPlus n ⋙ liftFunctor.{uF, uV, uF} ⋙ phiHatPlusIterate n k`. It goes from
`SmoothRep.{0, uF, uV} ℂ (GL_n)` to `SmoothRep.{0, uF, max uF uV} ℂ (P_(n+k+1))`.
This is the source's `(Φ̂⁺)^k ∘ Ψ⁺`, up to the universe lift
(`mirabolicDerivativeRightAdjoint_eq`). `mirabolicDerivativeRightAdjoint_map_injective`:
`Y` preserves injective intertwiners. On carriers, the lift of `Ψ⁺ g` is
`ULift.up ∘ g ∘ ULift.down`, so it is injective when `g` is. Then
`phiHatPlusIterate_map_injective` applies.

`mirabolicDerivativeAdjunction T ψ n k A θ` is
`Hom(A, Y_(n,k) θ) ≃ₗ[ℂ] Hom(mirabolicDerivative n k A, θ)`, for
`A : SmoothRep.{0, uF, uA} ℂ (P_(n+k+1))` and
`θ : SmoothRep.{0, uF, uV} ℂ (GL_n)`. It is the composite of three
equivalences:

1. the iterated adjunction with `X = lift (Ψ⁺ θ)`;
2. `liftHomEquiv`;
3. the companion `psiPlusAdjunction T n ((Φ⁻)^k A) θ`.

`mirabolicDerivativeAdjunction_apply` records the composite.
`mirabolicDerivativeAdjunction_comp_left` and
`mirabolicDerivativeAdjunction_comp_right` are naturality in `A` (against
`mirabolicDerivative.map`) and in `θ` (against `Y.map`). They chain the
naturality lemmas of the three pieces.

### Rank transport

`mirabolicRankCastHomEquiv T h A B`, for `h : a = b`, is
`Hom(A, mirabolicRankCast h B) ≃ₗ[ℂ] Hom(mirabolicRankCast h.symm A, B)`.
It is defined by `subst h` as the identity. `mirabolicRankCastHomEquiv_refl`
(identity on `rfl`), `mirabolicRankCastHomEquiv_comp_left` and
`mirabolicRankCastHomEquiv_comp_right` (naturality against
`mirabolicRankCast.map`) are proved by `subst`. This is the general form for
an arbitrary equality `h`, so it covers the published equality
`mirabolic_rank_eq_of_order hl` and its inverse.

### The order-indexed adjunction

For `0 < l ≤ N + 1` (`hl : 0 < l ∧ l ≤ N + 1`):

- `mirabolicDerivativeOfOrderRightAdjoint T ψ N l hl` is
  `mirabolicDerivativeRightAdjoint (N + 1 - l) (l - 1) ⋙
  mirabolicRankCast (mirabolic_rank_eq_of_order hl).symm`. It goes from
  `GL_(N+1-l)` to `P_(N+1)` (`mirabolicDerivativeOfOrderRightAdjoint_eq`).
- `mirabolicDerivativeOfOrderAdjunction T ψ N l hl A θ` is
  `Hom(A, Y θ) ≃ₗ[ℂ] Hom(mirabolicDerivativeOfOrder N l hl A, θ)`. It is
  `mirabolicRankCastHomEquiv` for the inverse rank equality, followed by
  `mirabolicDerivativeAdjunction (N + 1 - l) (l - 1)` applied to the
  transported `A`. Its target is definitionally
  `Hom(mirabolicDerivativeOfOrder N l hl A, θ)`.
  `mirabolicDerivativeOfOrderAdjunction_apply` records the composite.
- `mirabolicDerivativeOfOrderAdjunction_comp_left` and
  `mirabolicDerivativeOfOrderAdjunction_comp_right` are naturality in `A`
  (against `mirabolicDerivativeOfOrder.map`) and in `θ` (against the right
  adjoint's `map`).

This is the source's (*), stated for an arbitrary `θ` in place of `τ^(k)`
and natural in both arguments.

### Nonvanishing

`nontrivial_mirabolicDerivativeOfOrder_of_ne_zero`: if
`Φ : Hom(A, Y θ)` is nonzero, then `mirabolicDerivativeOfOrder N l hl A` is
`Nontrivial`. If the derivative were a subsingleton, the adjunct of `Φ` would
be the zero intertwiner, and injectivity of the equivalence would give
`Φ = 0`. `hasNonzeroDerivative_of_ne_zero` restates the conclusion as the
published predicate `HasNonzeroDerivative T ψ A l`.

### The unit

For `A : SmoothRep.{0, uF, uV} ℂ (P_(N+1))`, write `A^(l)` for
`mirabolicDerivativeOfOrder N l hl A`.

- `mirabolicDerivativeOfOrderUnit T ψ N l hl A : Hom(A, Y(A^(l)))` is the
  inverse image of the identity of `A^(l)` under the order-indexed
  adjunction. This is the source's morphism `A : τ → (Φ̂⁺)^(k-1) ∘ Ψ⁺(τ^(k))`.
- `mirabolicDerivativeOfOrderAdjunction_unit`: the adjunct of the unit is the
  identity.
- `mirabolicDerivativeOfOrderAdjunction_unit_comp`: for `f : A' ⟶ A`, the
  adjunct of `η_A ∘ f` is `f^(l)`, that is,
  `SmoothRep.hom ((mirabolicDerivativeOfOrder T ψ N l hl).map f)`. It follows
  from left naturality and the previous item.
- `mirabolicDerivativeOfOrderUnit_naturality`:
  `Y(f^(l)) ∘ η_(A') = η_A ∘ f`. Both sides have adjunct `f^(l)`, by right
  naturality and the previous items.
- `mirabolicDerivativeOfOrder_map_eq_zero_of_unit_comp`: if `η_A ∘ f = 0`,
  then `f^(l) = 0`.

The source then uses [I] 3.2(f) to show that the derivative carries its `A` to
the identity, so that `(Ker A)^(k) = 0`, and deduces that `A` is injective
when `τ` is homogeneous. This module states neither of these facts and
proves neither. `mirabolicDerivativeOfOrderAdjunction_unit_comp` is only the
adjunction identity for composites with the unit.

## Parameters, topology and universes

Throughout, `p : ℕ` is prime (`[Fact p.Prime]`), `F : PadicField.{uF} p`,
`T : F.TopologicalData` is an arbitrary supplied topological realization, and
every topological statement installs `letI := T.topology`. The additive
character is
`ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology`; its
nontriviality is not used. All `n, k : ℕ` are allowed, and every order `l`
with `0 < l ≤ N + 1` is allowed. There is no case split on ranks.

The universe of the source representation `A` (`uA`) and of `θ` (`uV`) are
independent in the adjunctions. The unit needs `θ = A^(l)`, so there `A` has
universe `uV`. The inspected level parameters of
`mirabolicDerivativeOfOrderAdjunction` are `uA, uV, uF`. Its type is:

```lean
mirabolicDerivativeOfOrderAdjunction.{uA, uV, uF} : {p : ℕ} → [Fact p.Prime] →
  {F : PadicField.{uF} p} → (T : F.TopologicalData) →
  (ψ : UnitaryAdditiveCharacter F.Carrier) → (N l : ℕ) → (hl : 0 < l ∧ l ≤ N + 1) →
  (A : SmoothRep.{0, uF, uA} ℂ (mirabolic N F.Carrier)) →
  (θ : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (N + 1 - l) F.Carrier)) →
  A.representation.IntertwiningMap
      ((mirabolicDerivativeOfOrderRightAdjoint T ψ N l hl).obj θ).representation ≃ₗ[ℂ]
    ((mirabolicDerivativeOfOrder T ψ N l hl).obj A).representation.IntertwiningMap
      θ.representation
```

Here the right adjoint lands in `SmoothRep.{0, uF, max uF uV}`. As in the
companion module, the derivative keeps the universe of `A`, while the right
adjoint raises `uV` to `max uF uV`. So the adjunction is stated as a natural
linear equivalence of intertwiner spaces across universes, not as a Mathlib
`CategoryTheory.Adjunction`. No universe is resized.

All main declarations depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.

## Provenance

The equivalences are the source's (*) of Ze80 §5.1, obtained, as the source
says, by iterating BZ77 §3.2(b) (first part) and (c). The unit is the
source's morphism `A` of Ze80 §5.1. The Lean proofs are internal: they compose
the two companion adjunctions, the published carrier lift and the published
rank transport. The formula lemmas, naturality, the nonvanishing corollary
and the unit laws are routine consequences of the equivalences, which the
source uses without stating them separately. No other original-literature
theorem is asserted.

## Import and dependency audit

### Complete import inventory

The recursive `Langlands` import closure of this module was computed by
following every `import` line, starting from this module, through the two
companion modules and the Library at base
`b22e185743f7c318f709e14e422801f4360105d5`. It consists of exactly 97
modules:

1. this module, `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusIterate`;
2. the companion module `Langlands.Representation.Derivative.MirabolicSmoothPhiPlus`,
   submitted as candidate `2546568e-f4b1-45e8-8b17-05a43ca7d49b`;
3. the companion module
   `Langlands.Representation.Derivative.MirabolicSmoothPhiPlusAdjunction`,
   submitted as candidate `567eec05-3143-4ba3-8f59-48f3224c079c`. Both
   companions are approved and not yet in the Library at this base;
4. the following 94 published, paired Library modules at this base. The 16
   entries marked "(statement)" contain Prop-valued statement definitions.

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
- `Langlands.Group.HaarModulus`
- `Langlands.HarmonicAnalysis.Basic`
- `Langlands.HarmonicAnalysis.PadicHaarScalingStatement` (statement)
- `Langlands.HarmonicAnalysis.PadicRectangularHaarScalingProof`
- `Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof`
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
- `Langlands.Representation.Derivative.Homogeneity`
- `Langlands.Representation.Derivative.Iteration`
- `Langlands.Representation.Derivative.MirabolicCharacter`
- `Langlands.Representation.Derivative.MirabolicMinus`
- `Langlands.Representation.Derivative.MirabolicMinusNormalization`
- `Langlands.Representation.Derivative.MirabolicPlus`
- `Langlands.Representation.Derivative.MirabolicPlusNormalization`
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
- `Langlands.Representation.Jacquet.Coinvariants`
- `Langlands.Representation.Jacquet.Localization`
- `Langlands.Representation.Jacquet.PositiveCharacter`
- `Langlands.Representation.Jacquet.SmoothTwist`
- `Langlands.Representation.MatrixCoefficient.Definitions`
- `Langlands.Representation.MatrixCoefficient.LawsProof`
- `Langlands.Representation.MatrixCoefficient.LawsStatement` (statement)
- `Langlands.Representation.Mirabolic.MixedProducts`
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
Mathlib. Compared with the 84-module closure of the adjunction companion,
the 13 new modules are this module and these 12 Library modules:

- `Group.GL.MirabolicMixedProductSubgroups`: the two mixed mirabolic inducing
  subgroups of BZ77 §4.12;
- `Group.GL.MirabolicOppositeIntersection`: the binary opposite-parabolic
  intersection inside the mirabolic group;
- `Group.GL.OppositeBlocks`: the Levi decomposition of the opposite block
  parabolic;
- `Group.GL.RankReindex`: reindexing `GL` along an equality of ranks;
- `Category.Subquotients`: actual subrepresentations and quotients in the
  smooth category, and the predicates `IsQuotient`, `IsSubrepresentation`
  and `IsSubquotient`;
- `Derivative.Iteration`: `phiMinusIterate`, `mirabolicDerivative`, the
  general linear restriction and derivative functors, and their rank casts;
- `Derivative.Homogeneity`: `mirabolicRankCast`, `mirabolicDerivativeOfOrder`,
  the natural-number `level`, and the predicates `HasNonzeroDerivative`,
  `IsHomogeneous` and `IsGeneralLinearHomogeneous`;
- `Induction.BinaryProduct`: the binary normalized product functor in all
  ranks, with pullbacks and carrier lifts;
- `Induction.BlockFactors`: normalized induction of block factors;
- `Mirabolic.MixedProducts`: the mixed mirabolic product functors of BZ77
  §4.12(II), (III), with the carrier lift `MixedProductTensor.liftFunctor`;
- `Tensor.Finite`: finite tensor actions and external tensor products;
- `Tensor.OneFactor`: tensor representations with one acting factor.

None of these 12 is a statement module. The definitions there include
`Prop`-valued predicates on representations (the subquotient and homogeneity
predicates). These are definitions, not statement targets, and no declaration
here takes any of them as a hypothesis. `HasNonzeroDerivative` occurs only
as the conclusion of `hasNonzeroDerivative_of_ne_zero`.

### Statement definitions and proved inputs

The 16 statement modules supply Prop-valued definitions, which are targets,
not proved inputs. They are the same 16 as in the adjunction companion's
closure. No declaration of this module or of the companions takes any of
them, or any other Prop-valued statement, as a hypothesis. In particular,
`Induction.StructuralStatement` defines Frobenius-reciprocity,
induction-exactness and open-subgroup-adjunction clauses as propositions.
This module neither assumes nor uses them: all adjunctions are constructed
directly. The target statement module
`Langlands.Representation.Derivative.LeftMixedProductHomogeneityStatement`
is not in the closure. The Library results used are published theorems and
definitions with complete Lean proofs.

### Actual proof dependencies

The proofs use only these imported declarations, together with Mathlib
(`Representation.IntertwiningMap`, linear equivalences, `ULift`, basic
category theory):

- companion `MirabolicSmoothPhiPlus`: `Mirabolic.phiHatPlus` and
  `Mirabolic.phiHatPlus_map_injective`;
- companion `MirabolicSmoothPhiPlusAdjunction`:
  `Mirabolic.phiHatPlusAdjunction`, `Mirabolic.psiPlusAdjunction` and their
  `_comp_left` and `_comp_right` naturality lemmas;
- `Derivative.MirabolicMinus`: the functors `Mirabolic.phiMinus` and
  `Mirabolic.psiMinus`, through the derivative;
- `Derivative.MirabolicPlusNormalization`: the functor `Mirabolic.psiPlus`;
- `Derivative.Iteration`: `phiMinusIterate` and `mirabolicDerivative`;
- `Derivative.Homogeneity`: `mirabolicRankCast`,
  `mirabolic_rank_eq_of_order`, `mirabolicDerivativeOfOrder` and
  `HasNonzeroDerivative`;
- `Mirabolic.MixedProducts`: `MixedProductTensor.liftFunctor` and
  `MixedProductTensor.liftEquiv`. These are abbreviations of the
  `Induction.BinaryProduct` carrier lift. No product functor is used.

The remaining modules of the inventory enter only through the imports of
these modules.

### Condition-by-condition exclusion audit

The conditions are those of the complete inherited exclusion set in the
context of task `6bb62ea4-c7e1-4325-9eb6-b8bbee1f65c4` revision 2, from
"Complete inherited exclusion set" to the end. A module can depend only on
declarations in its import closure. So it suffices to check two things: no
excluded statement, proof or consequence lies in the 97 modules above, and
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
   module, and no such conclusion is assumed.
2. **Operator-paused minus exactness `b65bc667`.** Satisfied. The statement
   module `Derivative.MirabolicMinusExactnessStatement` is not in the
   closure, and neither is `Derivative.GeneralLinearDerivativeExactnessStatement`.
   Exactness of `Φ⁻`, `Ψ⁻` or the derivative is neither proved nor assumed,
   and the task is not resumed or bypassed. The adjunctions and the unit laws
   need no exactness. The module does not state the injectivity of the
   unit, whose source proof passes through `(Ker A)^(k) = 0`.
3. **Detection-unit restrictions.** The combined Ze80 §5.4 reduction, its
   strong-indecomposability conclusion (`ff4738d8`), the nonadjacent
   product `3c9849a4` and the full product structure `ab61f565`: satisfied.
   No such module is in the closure, and none of these is assumed. In
   particular `Derivative.MirabolicStrongIndecomposabilityStatement` and all
   detection statement and proof modules are absent.
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
   only Jacquet modules in the closure are `Jacquet.Coinvariants`,
   `Jacquet.Localization`, `Jacquet.PositiveCharacter` and
   `Jacquet.SmoothTwist`. They contain general coinvariant and localization
   constructions and character twists, not segment Jacquet formulas.
5. **Full-formula consumer restrictions.** No Ze80 §3.5 or §9.6 segment
   derivative formula, no segment product criterion (Ze80 4.2, 9.7), no
   analytic or square-integrability result (Ze80 9.3) and no classification
   or exhaustion theorem: satisfied. From Zelevinsky 1980 only the
   adjunction formula (*) and the morphism `A` of §5.1 are formalized, by
   the internal proofs above. No Ze80 theorem is assumed. No derivative
   result of BZ77 or anyone else is assumed. The derivative inputs are the
   published functor definitions `phiMinusIterate`, `mirabolicDerivative`,
   `mirabolicDerivativeOfOrder` and the companion adjunctions, all with
   complete Lean proofs. No Leibniz filtration, mixed-product derivative,
   product-restriction or level-calculus module is in the closure. The
   segment-socle part of task `8e5b4563` is not used.
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
   named there, only the derivative functor constructions are used (`Φ⁻`,
   `Ψ⁻`, `Ψ⁺`, the iterated derivative and its rank transport). Their
   independence is checked by this inventory, since their modules and
   closures lie in it. No exactness, Leibniz filtration, geometric lemma,
   cuspidal-support or finite-length module is in the closure.
   `Geometric.ClosedSubgroupDefinitions`, `Geometric.SmoothSupportFiltration`
   and `Geometric.CompactSmoothComparison` are support-filtration definitions
   and the compact-to-smooth inclusion, not the BZ77 geometric lemma. The
   product modules `Induction.BinaryProduct`, `Induction.BlockFactors` and
   `Mirabolic.MixedProducts` define product functors only; they contain no
   product structure, irreducibility or reducibility theorem, and only their
   carrier lift is used.
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
   task `5428fe2c`: satisfied. No finiteness or finite-length module is in
   the closure. The closure contains two Whittaker modules.
   `Whittaker.Algebraic` defines left-equivariant functions, equivariant
   functionals and coefficient models with their elementary laws.
   `Whittaker.GeneralLinear` defines the standard character
   `ψ(Σ u_(i,i+1))`, its inverse and scaled variants, GL coefficient
   models and the predicate `IsGeneric`. Their own imports are
   `MatrixCoefficient`, `Smooth.Definitions`, `Group.GL.UpperUnipotent` and
   `HarmonicAnalysis.Basic` modules. They enter the closure only through
   `Derivative.MirabolicCharacter`, which identifies the mirabolic
   character `θ` with a restriction of the standard character
   (`theta_eq_standardCharacter_comp`). They contain no coinvariant
   finiteness statement or theorem, and none of their declarations is used
   here except through that character.

The proofs use no `sorry`, `admit` or new axiom. This inventory and audit
are an author audit, not independent acceptance evidence.

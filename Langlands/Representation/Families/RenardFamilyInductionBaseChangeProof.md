# Renard VI.8.2: base change commutes with induction of families

Authors: Worker 1812 (the compact-quotient reduction, from the shared draft of
Task 5188, revision 1) and Worker 5188 (the unconditional assembly). Module
`Langlands.Representation.Families.RenardFamilyInductionBaseChangeProof`,
namespace `Langlands.Renard.AlgebraicFamily`.

The module proves the unchanged VI.8.2 Proposition
`InductionBaseChangeStatement.{u, uB, uC, uE}` of
[RenardFamilyParabolicStatements](RenardFamilyParabolicStatements.md), at its
own independent universe parameters:

```lean
theorem inductionBaseChange : InductionBaseChangeStatement.{u, uB, uC, uE}
```

No hypothesis is added. The compactness of `P(F)\G(F)` that the argument needs
is not assumed: it is obtained inside the proof from three published Library
theorems (see "Statement" below).

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, VI.8.2 Proposition, its proof and formula (VI.8.2.2), printed
p. 190 / PDF p. 196. Literature ID
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Renard
compares `K`-fixed vectors of both sides through (VI.8.2.1), a product over a
finite set `Ω` of double-coset representatives, and then says that (VI.8.2.2)
is clearly an isomorphism. The VI.8.3 remark (PDF p. 197, "le point crucial est
la compacité de `P\G`, et donc la finitude de `P\G/K`") names the ingredient
that makes `Ω` finite. The implemented argument below follows this route; the
details (VI.8.1 averaging for the fixed vectors of a tensor product, injectivity
of evaluation on a transversal) are the authors' implementation.

## Proof

### `CompactOpen`

- `exists_isCompact_openSubgroup_subset`: in a locally compact nonarchimedean
  group every open subgroup contains a compact open subgroup: intersect it
  with a compact neighbourhood of `1` and take an open subgroup inside.
- `exists_isCompact_fixedVectors`: hence every smooth vector is fixed by some
  compact open subgroup.
- `isCompact_conjOpenSubgroup`: for closed `P` and compact open `K`, the
  subgroup `Induction.conjOpenSubgroup P K i = P ∩ i K i⁻¹` of `P` is compact. It
  is the preimage, under the closed embedding `P → G`, of the compact set
  `i K i⁻¹`.

### `BaseChangeTensor`

For a family `ρ` over `B` of a group `H` and a `B`-algebra `C`:

- `tprod_trivial_apply` and `tprod_trivial_apply_of`: `baseChange C ρ`, and any
  `C`-linear action acting as `c ⊗ v ↦ c ⊗ ρ(h) v` on pure tensors, agrees with
  the published tensor product `(Representation.trivial B H C).tprod ρ`. This is
  the form used by VI.8.1 in `RenardFamilyFixedTensorProof`.
- `lTensor_subtype_mem_fixedVectors`: the image of `C ⊗[B] V^K` in
  `C ⊗[B] V` is `K`-fixed.
- `twist_constantCharacter_baseChange_tmul`: twisting by a `ℂˣ`-valued
  character commutes with base change on pure tensors. This uses
  `IsScalarTower ℂ B C`.
- `isSmooth_baseChange`: base change preserves smoothness (from the published
  `trivialTensor_isSmooth`).

### `InductionBaseChange`

For a subgroup `P` of a topological group `G` and `τ : Representation B P E`,
let `τC` be any `C`-linear action of `P` on `C ⊗[B] E` acting by
`c ⊗ v ↦ c ⊗ τ(p) v` on pure tensors (hypothesis `hτC`).

- `inducedEval g` is evaluation `f ↦ f(g)` on smooth induced functions.
- `inducedBaseChangePi` sends `x ∈ C ⊗[B] i(E)` to the function
  `g ↦ (1 ⊗ ev_g)(x)`. On `c ⊗ f` it is `g ↦ c ⊗ f(g)`, formula (VI.8.2.2) with
  the tensor factors in the Lean order. It is `P`-covariant for `τC`
  (`inducedBaseChangePi_covariant`) and right-invariant under some open subgroup
  (`inducedBaseChangePi_exists_openSubgroup`, by induction on tensors).
- `inducedBaseChange τC hτC : C ⊗[B] i(E) →ₗ[C] i(C ⊗[B] E)` packages these
  functions with the published `Induction.smoothFunctionOf`.
  `eval_inducedBaseChange_tmul` records the formula `c ⊗ f ↦ (g ↦ c ⊗ f(g))`.
- `inducedBaseChange_equivariant`: the map intertwines `baseChange C` of the
  induced action with the induced action of `τC`. On pure tensors both sides are
  `y ↦ c ⊗ f(y g)`.

### `Bijective`

Assume now that `G` is nonarchimedean and locally compact, `B` is a
`ℂ`-algebra, `P` is closed, `τ` is smooth and
`CompactSpace (Induction.LeftQuotient P)`.

- `exists_lTensor_fixedEvaluation`: for compact open `K` and a finite
  double-coset transversal `t` of `P\G/K`, the published
  `Induction.fixedEvaluationEquiv` identifies `i(E)^K` with
  `∏_{i ∈ t} E^{P ∩ i K i⁻¹}` (the source's (VI.8.2.1)). Tensoring with `C`
  (`LinearEquiv.baseChange` followed by `TensorProduct.piRight`) gives
  `Θ : C ⊗[B] i(E)^K ≃ ∏_{i ∈ t} C ⊗[B] E^{P ∩ i K i⁻¹}`, compatible with
  evaluation at each `i`.
- `exists_lTensor_fixedVectors_eq`: by VI.8.1
  (`fixedTensorComparison_of_smooth`, the averaging comparison for smooth
  families over a `ℂ`-algebra), every `K`-fixed vector of `C ⊗[B] i(E)` comes
  from `C ⊗[B] i(E)^K`.
- `inducedBaseChange_injective`: let `x` map to `0`. Choose a compact open `K`
  fixing `x`, write `x` as the image of `y ∈ C ⊗[B] i(E)^K`, and take a finite
  transversal `t` from compactness of `P\G`
  (`Induction.exists_finset_doubleCoset_representatives`). Each component
  `Θ y i ∈ C ⊗[B] E^{P ∩ i K i⁻¹}` maps to the value at `i` of the image of `x`,
  which is `0`. That map is injective by VI.8.1 applied to the compact group
  `P ∩ i K i⁻¹`. Hence `Θ y = 0`, so `y = 0` and `x = 0`.
- `inducedBaseChange_surjective`: let `f ∈ i(C ⊗[B] E)` be fixed by a compact
  open `K`, with transversal `t`. Each value `f(i)` is fixed by
  `P ∩ i K i⁻¹` (`Induction.eval_mem_fixedVectors`), so by VI.8.1 it equals the
  image of some `z_i ∈ C ⊗[B] E^{P ∩ i K i⁻¹}`. Let `x` be the image of
  `Θ⁻¹ (z_i)_i`. Then `x` is `K`-fixed, so its image is `K`-fixed, and that image
  has the same values as `f` on `t`. Injectivity of evaluation on a transversal
  (`Induction.fixedEvaluation_injective`) gives that the image equals `f`.
- `exists_inducedBaseChangeEquiv`: the comparison is therefore a `C`-linear
  equivalence, `G`-equivariant and given by `c ⊗ f ↦ (g ↦ c ⊗ f(g))`.

### `Represented`

For a represented parabolic `p` with rational Levi `l`, radical `r` and
`hmul`, and smooth `σ` on the Levi points:

- `isSmooth_leviInducingRepresentation`: the inducing representation of
  `LeviInduced` (the Levi representation transported to the Levi image, twisted
  by the induction character and inflated along the projection of
  `pointImage p` onto its Levi factor) is smooth. This uses
  `isSmooth_comp`, `isSmooth_twist_iff` and the published continuity
  `continuous_projection_pointImage`.
- `leviInducingRepresentation_baseChange_tmul`: the inducing representation
  of `baseChange C σ` acts by `c ⊗ v ↦ c ⊗ τ(q) v`, where `τ` is the inducing
  representation of `σ`. The twisting character
  `HaarModulus.closedHalfCharacter` is `ℂˣ`-valued and is the same for `B`
  and `C`, so `twist_constantCharacter_baseChange_tmul` applies.
- `exists_leviInducedBaseChangeEquiv`: given
  `CompactSpace (Induction.LeftQuotient (pointImage p))`, apply
  `exists_inducedBaseChangeEquiv` with `P = pointImage p`, which is closed by
  `isClosed_pointImage`.

### `Statement`

`inductionBaseChange` introduces the binders of `InductionBaseChangeStatement`,
installs `hG.isAffineHom` and the canonical point topology exactly as the
statement does, and obtains the compactness instance
`CompactSpace (Induction.LeftQuotient (pointImage p))` from three published
theorems:

- `Langlands.Aubert.General.RepresentedParabolic.compactSpace_leftQuotient_pointImage_of_dynamic`
  (module `ArbitraryParabolicFiniteSupportReduction`), which derives this exact
  compactness from `GroupScheme.ParabolicDynamicStatement` and
  `BruhatTits.DynamicParabolicQuotientCompactStatement`;
- `Langlands.GroupScheme.parabolicDynamic`, the published proof of
  `ParabolicDynamicStatement` (every parabolic is `P(λ)` for a rational
  cocharacter `λ`);
- `Langlands.BruhatTits.dynamicParabolicQuotientCompact`, the published proof of
  `DynamicParabolicQuotientCompactStatement` (compactness of the quotients of
  the rational points by a dynamic parabolic).

This is the same composition that Renard's V.5.1 Corollary (compactness of
`G/P`, printed p. 123 / PDF p. 129) supplies in the source. It then concludes
with `exists_leviInducedBaseChangeEquiv`.

## Hypotheses not used

The proof does not use flatness of `E`, nor the Noetherian, finite-type and
reduced hypotheses on `B` and `C`. Averaging over compact open subgroups (VI.8.1) needs only that `B`
is a `ℂ`-algebra. Compactness of `P(F)\G(F)` is essential: it makes `P\G/K`
finite, so that `i(E)^K` is a finite product and commutes with `C ⊗[B] -`.

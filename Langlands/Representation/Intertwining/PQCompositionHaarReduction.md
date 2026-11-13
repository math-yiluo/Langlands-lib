# Renard VII.3.5 (i): compatible Haar measures from the product decomposition

Author: Worker 102. Module
`Langlands.Representation.Intertwining.PQCompositionHaarReduction`, namespace
`Langlands.Aubert.General.RepresentedParabolic`. Universe parameter `u`.

This is a conditional reduction. It proves `PQCompositionHaarStatement` (clause 1 of the
published `PQIntertwiningCompositionStatement`, stated on its own in
`Langlands.Representation.Intertwining.PQIntertwiningCompositionReduction`) from one
proposition about the subgroups `V₁₂ = N̄₁(F) ∩ N₂(F)`, `V₂₃ = N̄₂(F) ∩ N₃(F)` and
`V₁₃ = N̄₁(F) ∩ N₃(F)` of `G(F)`:

- `PQCompositionProductStatement` (defined in `PQIntertwiningCompositionReduction`):
  multiplication `V₁₂ × V₂₃ → V₁₃`, `(w, u) ↦ w u`, is a homeomorphism.

That proposition is not proved here, so `PQCompositionHaarStatement` is not yet proved
unconditionally. The module adds no new `Prop`-valued definitions.

The module contains:

- four abstract lemmas: `isMulRightInvariant_of_forall_isCompact_subgroup`,
  `sigmaCompactSpace_of_isClosed_subgroup`, `forall_isCompact_subgroup_of_le` and
  `exists_compatible_haar_of_mul_homeomorph`;
- the reduction theorem `pqCompositionHaar_of_product`;
- the definition `pqCompositionHaarOfProduct`, whose type is the same implication
  `PQCompositionProductStatement.{u} → PQCompositionHaarStatement.{u}`. This definition is the
  declaration recorded for this unit. It follows the Library pattern for conditional
  reductions.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026. Literature ID `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. Proposition VII.3.5 is on
printed p.237 / PDF p.243. In the proof of (i), printed p.239 / PDF p.245, Renard translates
`d(P₁, P₃) = d(P₁, P₂) + d(P₂, P₃)` into `N̄₁ ∩ N₃ = (N̄₁ ∩ N₂)(N̄₂ ∩ N₃)`. He then uses
`∫_{N̄₂∩N₃} ∫_{N̄₁∩N₂} f(vu) dv du = ∫_{N̄₁∩N₃} f(u) du` for compatible Haar measures, without
proving that such measures exist. This module supplies that existence argument. It is
derived content: the lemmas and their proofs are standard measure theory, not taken from
Renard.

## Why unimodularity is used

Suppose a locally compact group `H` factors as `H = A B` with `A × B → H` a homeomorphism. The
image of `haar_A × haar_B` is a Haar measure of `H` only up to modular-function factors in
general. Here they cancel because `V₂₃` and `V₁₃` are unimodular. Both lie in
`N₃(F) = pointImage (r₃ ≫ p₃)`, and the Library proves that this group is a limit of compact
subgroups: every compact subset lies in a compact subgroup
(`isLimitOfCompactSubgroups_pointImage_radical`). A group with that property is unimodular.
No property of `V₁₂` beyond being a closed subgroup is used.

## Abstract lemmas

- `isMulRightInvariant_of_forall_isCompact_subgroup`: let `X` be a Hausdorff, locally compact,
  second countable topological group with its Borel σ-algebra. Suppose every compact subset of
  `X` lies in a compact subgroup. Then every Haar measure `m` on `X` is right invariant.

  Proof. Fix `g`. Take a compact neighbourhood `C` of `1` and a compact subgroup `K ⊇ C ∪ {g}`.
  Then `K` is a neighbourhood of `1`, so `0 < m(K) < ∞`. The right translate `(· g)_* m` is a
  left-invariant Haar measure. By uniqueness (`isMulLeftInvariant_eq_smul`) it equals `c • m`
  with `c = haarScalarFactor`. Since `g ∈ K`, the preimage of `K` under `x ↦ x g` is `K`.
  Evaluating both sides on `K` gives `m(K) = c m(K)`, so `c = 1`.

Let `H` be a Hausdorff, second countable, locally compact topological group.

- `sigmaCompactSpace_of_isClosed_subgroup`: a closed subgroup `V` of `H` is σ-compact. It is
  locally compact, being closed, and second countable as a subspace. Mathlib's
  `sigmaCompactSpace_of_locallyCompact_secondCountable` then applies. (Only the topology of
  `H` is used here.)
- `forall_isCompact_subgroup_of_le`: let `U` be a limit of compact subgroups
  (`Jacquet.Localization.IsLimitOfCompactSubgroups U`) and `V ≤ U` a closed subgroup. Then every
  compact subset `C` of `V` lies in a compact subgroup of `V`.

  Proof. The image of `C` in `U` lies in a compact subgroup `K` of `U`. Take the preimage of `K`
  under the inclusion `V → U`. As a subset of `V` it is the preimage, along the closed embedding
  `V → H`, of the compact set `K ⊆ H`, so it is compact.
- `exists_compatible_haar_of_mul_homeomorph`: let `V₁₂, V₂₃, V₁₃` be closed subgroups of `H`
  with Borel σ-algebras. Suppose every compact subset of `V₂₃`, and every compact subset of
  `V₁₃`, lies in a compact subgroup. Let `e : V₁₂ × V₂₃ ≃ₜ V₁₃` be a homeomorphism with
  `e(w, u) = w u` in `H`. Then for all Haar measures `μ₁₂` on `V₁₂` and `μ₂₃` on `V₂₃` there is
  a Haar measure `μ₁₃` on `V₁₃` such that
  `∫_{V₁₃} φ dμ₁₃ = ∫_{V₂₃} ∫_{V₁₂} φ(w u) dμ₁₂(w) dμ₂₃(u)` for every continuous compactly
  supported `φ : H → ℂ`.

  Proof. The three subgroups are closed, so they are locally compact, second countable and
  σ-compact. Put `ν = μ₁₂ × μ₂₃` and `μ₁₃ = e_* ν`.
  - Unimodularity: by the first lemma, `μ₂₃` is right invariant, and so is a fixed Haar measure
    `m` on `V₁₃`.
  - Coordinates: let `ψ(w, u) = (w, u⁻¹)` on `V₁₂ × V₂₃` and `f = ψ ∘ e⁻¹ : V₁₃ ≃ₜ V₁₂ × V₂₃`.
    For `x = (x₁, x₂) ∈ V₁₂ × V₂₃` and `g = e(w, u)` we have `x₁ g x₂⁻¹ = e(x₁ w, u x₂⁻¹)`, hence
    `f(x₁ g x₂⁻¹) = (x₁ w, x₂ u⁻¹) = x · f(g)`.
  - `f_* m` is left invariant on the product group. Left translation by `x` corresponds under
    `f` to `g ↦ x₁ g x₂⁻¹`, which preserves `m` because `m` is left and right invariant.
  - `ψ_* ν` is left invariant. We have `x · ψ(y) = ψ(x₁ y₁, y₂ x₂⁻¹)`. The map
    `(y₁, y₂) ↦ (x₁ y₁, y₂ x₂⁻¹)` preserves `ν` (`map_prod_map`), because `μ₁₂` is left invariant
    and `μ₂₃` is right invariant.
  - Both measures are finite on compacts and positive on open sets, since these properties pass
    along homeomorphisms. So both are Haar measures on `V₁₂ × V₂₃`. Uniqueness gives
    `f_* m = c • ψ_* ν` with `c > 0` (`haarScalarFactor_pos_of_isHaarMeasure`). Pushing forward
    along `f⁻¹`, and using `f⁻¹ ∘ ψ = e`, gives `m = c • μ₁₃`. So `μ₁₃ = c⁻¹ • m` is left
    invariant.
  - `μ₁₃` is finite on compacts and positive on open sets, again because `e` is a
    homeomorphism. So it is a Haar measure.
  - The formula: `x ↦ φ(e x)` on `V₁₂ × V₂₃` is continuous with compact support, because
    `V₁₃ → H` and `e` are closed embeddings. So it is integrable. Change of variables along the
    measurable embedding `e`, then Fubini in the order "first `V₁₂`, then `V₂₃`"
    (`integral_prod_symm`), give the stated iterated integral.

## The reduction `pqCompositionHaar_of_product`

```
theorem pqCompositionHaar_of_product (hProd : PQCompositionProductStatement.{u}) :
    PQCompositionHaarStatement.{u}
```

After introducing the binders of `PQCompositionHaarStatement`, the proof takes the
homeomorphism `e : V₁₂ × V₂₃ ≃ₜ V₁₃` from `hProd` for the same data. The other inputs come from
the Library:

- Hausdorff `G(F)`: `Langlands.AlgebraicGeometry.PointTopology.rationalPoint_t2Space`;
- second countable `G(F)`:
  `Langlands.Aubert.General.RationalPointFamily.reductiveRationalPoint_secondCountable`;
- locally compact topological group: hypotheses of the statement;
- closedness of `V₁₂, V₂₃, V₁₃`: each is an intersection of two images `pointImage (r ≫ p)`,
  which are closed by `isClosed_pointImage_comp`;
- compact subsets of `V₂₃` and `V₁₃` lie in compact subgroups. Both groups are contained in
  `pointImage (r₃ ≫ p₃)` (`inf_le_right`). That group is a limit of compact subgroups by
  `isLimitOfCompactSubgroups_pointImage_radical`, and `forall_isCompact_subgroup_of_le` applies.

The abstract lemma `exists_compatible_haar_of_mul_homeomorph` then gives the required
`haar₁₃`. Its order of integration is the one in the definition of `Compatible` in the
published statement. The root-distance hypotheses of the statement are used only through
`hProd`.

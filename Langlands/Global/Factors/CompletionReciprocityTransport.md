# Transport of geometric reciprocity candidates along isomorphisms of p-adic fields

Lean module: `Langlands.Global.Factors.CompletionReciprocityTransport`
(`Langlands/Global/Factors/CompletionReciprocityTransport.lean`).

## Purpose and provenance

Henniart (2000), §3.8, obtains the properties of the composite map at a p-adic field
`K` from those at the completion `F_v` "par transport de structure". The twist and
character clauses quantify over geometric reciprocity candidates, so a geometric
candidate of `K` has to be matched with a geometric candidate of `F_v` along the
isomorphism `f : K ≅ F_v`. This module proves that matching. It is internal
infrastructure for the proof tasks of
`Langlands.Global.PoleComparison.HenniartCompositeOperationStatement` and
`Langlands.Global.PoleComparison.HenniartCompositeFactorStatement`. The source has no
separate statement of it; the content is the naturality of local reciprocity under
field isomorphisms.

## Declarations

### `Langlands.LocalClassField.transfer_eq_of_forall_mem`

For a finite-index subgroup `H` of a group `G` that contains every element of `G`,
a commutative group `A`, a homomorphism `ϕ : H →* A` and `g : G`,

`MonoidHom.transfer ϕ g = ϕ ⟨g, hH g⟩`.

*Proof.* The quotient `G ⧸ H` is a subsingleton, so the constant section `q ↦ 1` is
a section of `G → G ⧸ H`. The published section formula
`Langlands.GroupTheory.Transfer.transfer_eq_prod_section` writes the transfer as a
product over `G ⧸ H` of `ϕ ⟨1⁻¹ * g * 1, _⟩`. Mathlib's `Fintype.prod_subsingleton`
reduces the product to its single factor, and `1⁻¹ * g * 1 = g`.

### `Langlands.LocalClassField.exists_geometric_extensionWeilEquiv`

Let `F` and `E` be p-adic fields, in arbitrary universes, and let
`g : F ≃ₐ[ℚ_p] E`. Let `eE` be a reciprocity candidate of `E` with the geometric
relation `GeometricWeilReciprocityRelation E E.canonicalTopologicalData eE`. Then
there is a reciprocity candidate `eF` of `F` with the geometric relation
`GeometricWeilReciprocityRelation F F.canonicalTopologicalData eF`, such that for
every `w` in the local Weil group of `E`

`(reciprocityUnits F eF (extensionWeilEquiv F E g w) : F) = g⁻¹ (reciprocityUnits E eE w : E)`.

Here `extensionWeilEquiv F E g : W_E ≃ₜ* W_F` is the published Weil-group
isomorphism of `g`, whose forward map is `extensionWeilMap F E g`.

*Proof.*

1. The published theorem `Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness`
   gives a geometric candidate `eF` of `F` for its canonical topology.
2. The published transfer/inclusion square
   `Langlands.LocalClassField.extensionWeilTransferReciprocity` for the embedding
   `g`, the candidates `eF` and `eE`, evaluated at `y = extensionWeilMap F E g w`,
   says: the transfer from `W_F` to the range of `extensionWeilMap F E g` of
   `reciprocityUnits E eE ∘ rangeInverse` at `y` equals `g (reciprocityUnits F eF y)`
   on units.
3. Since `extensionWeilEquiv F E g` is surjective with forward map
   `extensionWeilMap F E g`, every element of `W_F` lies in this range. By
   `transfer_eq_of_forall_mem`, the transfer is evaluation at `⟨y, _⟩`.
4. `InductionAlong.rangeInverse_apply` sends `⟨extensionWeilMap F E g w, _⟩` back to
   `w`, so the left side is `reciprocityUnits E eE w`.
5. Hence `reciprocityUnits E eE w = g (reciprocityUnits F eF y)` in `E`, and applying
   `g⁻¹` (`AlgEquiv.symm_apply_apply`) gives the claim.

### `Langlands.Global.exists_geometric_completionReciprocity`

Let `F` be a number field, `v` a finite place of `F`, `p` a prime with
`h : residuePrime v = p`, `K` a p-adic field in any universe, and
`f : K ≃ₐ[ℚ_p] padicFieldAt v h`. For every reciprocity candidate `e` of `K` with
`Correspondence.IsGeometricReciprocity K e`, there is a reciprocity candidate `e'`
of the canonical completion package `padicField v` with
`Correspondence.IsGeometricReciprocity (padicField v) e'` such that for every `w` in
the local Weil group of `K`

`(reciprocityUnits (padicField v) e' (completionWeilEquiv v h K f w) : F_v) = f (reciprocityUnits K e w : K)`.

The two sides live in the same carrier, the completion of `F` at `v`, which is the
carrier of both `padicField v` and `padicFieldAt v h`.

*Proof.* After `subst h`, the package `padicFieldAt v rfl` is definitionally
`padicField v` and `completionWeilEquiv v rfl K f` is definitionally
`extensionWeilEquiv (padicFieldAt v rfl) K f.symm` followed by the identity. The
claim is then `exists_geometric_extensionWeilEquiv` for `F := padicFieldAt v rfl`,
`E := K` and `g := f.symm`, since `f.symm.symm = f`.

## Public results used

- `Langlands.LocalClassField.geometricWeilReciprocityExistenceUniqueness`
  (`Langlands/ClassFieldTheory/Local/WeilReciprocityExistenceProof.lean`)
- `Langlands.LocalClassField.extensionWeilTransferReciprocity`
  (`Langlands/ClassFieldTheory/Local/WeilTransferReciprocityProof.lean`)
- `Langlands.GroupTheory.Transfer.transfer_eq_prod_section`
  (`Langlands/GroupTheory/TransferDoubleCoset.lean`)
- `Langlands.Weil.Local.extensionWeilEquiv`, `extensionWeilMap_range_finiteIndex`,
  `extensionWeilMap_injective`, `Langlands.InductionAlong.rangeInverse_apply`
- `Langlands.Global.completionWeilEquiv` (`Langlands/Global/Factors/HenniartCompositeMapStatement.lean`)
- Mathlib: `MonoidHom.transfer`, `Fintype.prod_subsingleton`, `AlgEquiv.symm_apply_apply`

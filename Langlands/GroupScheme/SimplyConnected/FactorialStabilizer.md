# Stabilizers of closed subsets under left translation

This internal helper module, used in the exhaustion step of the proof of
`SplitSimplyConnectedFactorialStatement`, defines the stabilizer of a set of
points of a group scheme `G` over a field `k` as a subgroup functor. As a
consequence of `range_subset_of_maximal` below, a smooth connected affine group
stabilizes a maximal irreducible closed subset of the complement of an open
set, as soon as the translates of that subset avoid the open set. The lemma
itself is stated under the weaker hypotheses described below.

## The stabilizer

- `stabilizer Z` (for `Z : Set G.X.left`) is the subgroup functor whose
  `Y`-points are the `g : Y ⟶ G.X` with the following property. For every
  `W`, every `y : W ⟶ Y` and every `z : W ⟶ G.X` whose image lies in `Z`, the
  images of `(y ≫ g) · z` and `(y ≫ g)⁻¹ · z` also lie in `Z`. Closure under
  multiplication, inverses and base change is checked directly.
  `mem_stabilizer` unfolds membership.

## Translation by a smooth connected group

For group schemes `H` and `G'` over `k`:

- `prodOver H G'` is `H ×ₖ G'` over `k`, with projections `prodFst` and
  `prodSnd`; `prodLift h z` is the point with coordinates `h` and `z`
  (`prodLift_fst`, `prodLift_snd`).
- `range_subset_of_maximal`: let `H` be smooth, affine and connected over `k`,
  let `j : H ⟶ G`, and let `V ⊆ G` be open. Let `Z` be irreducible, and assume
  that every irreducible closed subset of `G` containing `Z` and disjoint from
  `V` is contained in `Z`. The lemma assumes neither that `Z` is closed nor that
  `Z` is disjoint from `V`. Assume also that `j(h) · z ∉ V` at every point
  where `z` lies in `Z`. Then `j(h) · z` lies in `Z` for every point `h` of `H`
  and every point `z` with image in `Z`.

  Proof: `H` is geometrically integral over `k`
  (`smoothConnectedAffineGeometry`), so the preimage `T` of `Z` in `H ×ₖ G` is
  irreducible (Mathlib's `Scheme.Hom.isIrreducible_preimage`, the projection
  being open). The closure of the image of `T` under the action map
  `(h, z) ↦ j(h) · z` is irreducible and closed. It contains `Z` (use `h = 1`)
  and is disjoint from `V` (the image avoids `V` by hypothesis, and `V` is
  open). By the assumption on `Z`, it is contained in `Z`.

Provenance: internal; a standard argument with irreducible components.

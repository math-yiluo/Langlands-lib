# Classes of points with the same image under a finite map

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.SameImageClasses`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

## Topology

- `exists_mem_specializes_of_mem_closure`. Let `α` be a Noetherian quasi-sober space, `H`
  closed and `O` open. Every point `x` of `closure (H ∩ O)` is a specialization of a point of
  `H ∩ O`.

  Proof: write the closure as a finite union of irreducible closed sets, using
  `NoetherianSpace.exists_finite_set_isClosed_irreducible`, with the smallest possible number
  of pieces (`Nat.find`). Take a piece `Z` containing `x` and its generic point `ζ`. Then
  `ζ ∈ H`. If `ζ ∉ O`, then `Z ∩ O` is empty, so `H ∩ O`, and hence its closure, is covered by
  the other pieces. This contradicts minimality.
- `exists_generic_class`. Let `α` be a T0 space with an equivalence relation `r`. Assume:
  - `r a b` and `a ⤳ b` imply `a = b`;
  - specializations transport along `r`: if `r x x'` and `x ⤳ y`, then some `y'` has
    `r y y'` and `x' ⤳ y'`;
  - a finite nonempty set `G` has every point of `α` as a specialization of one of its points.

  Then some `γ ∈ G` has a class closed under generization: `a ⤳ b` and `r b γ` imply `r a γ`.

  Proof: take `γ` minimal in `G` for the strict order derived from the preorder "`a`
  specializes to a point related to `b`". Well-foundedness comes from the finiteness of `G`.
  Then transport specializations along `r`, and use the first hypothesis and T0 to close the
  loop.

## Finite maps

Let `f : h_U ⟶ Y` be finite (`IsFinite`).

- `SameImage.exists_specializes`. If `SameImage f x x'` and `x ⤳ y`, then some `y'` has
  `SameImage f y y'` and `x' ⤳ y'`. Proof: specializations lift along the closed projection
  `snd` of `U ×_Y U`.
- `SameImage.finite_class`. Each class `{x' | SameImage f x x'}` is finite. It is the image of
  the finite fibre of `snd : U ×_Y U ⟶ U` (`finite_preimage_singleton`).
- `saturation f T` (definition): the set of points with the same image as a point of `T`.
  - `subset_saturation` and `saturation_saturated` are its basic properties.
  - `isClosed_saturation`: for closed `T`, `saturation f T = fst' '' (snd ⁻¹' T)`, which is
    closed because `fst'` is finite, hence closed.

Provenance: internal. The topological lemmas are standard facts about Noetherian sober spaces
(compare Stacks Project, Tag 0052) and are proved directly. The finite-map results use only
the Library's represented pullbacks and Mathlib's finiteness and closedness of finite
morphisms.

# The split Cartan subalgebra of a Levi subalgebra

Module `Langlands.Algebra.HarishChandra.SplitCartanLevi`, namespace
`Langlands.Algebra.HarishChandra`.

## Setting

`𝔥` is a split Cartan subalgebra (`IsSplitCartan`) of a complex Lie algebra `𝔤`, `X₁ ∈ 𝔥`, and
`ι : 𝔪 → 𝔤` is an injective Lie algebra map with range `ker ad X₁`.

## Contents

- `comapCartanMap H ι : H.comap ι → H` is the restriction of `ι` to `ι⁻¹(𝔥)`. It is injective
  (`comapCartanMap_injective`). It is surjective because the abelian `𝔥` lies in `ker ad X₁`
  (`cartan_le_range`, `comapCartanMap_surjective`). `comapCartanEquiv` is the resulting linear
  isomorphism `ι⁻¹(𝔥) ≃ 𝔥`.
- `mem_weightSpace_comp_iff` and `mem_weightSpace_iff_symm`: `x ∈ 𝔪` is a weight vector for a
  weight `χ` of `ι⁻¹(𝔥)` exactly when `ι x` is a weight vector of `𝔤` for the transported
  weight `χ ∘ φ⁻¹`.
- `weightSpace_symm_ne_bot`, `weight_symm_ne_zero`: the transported weight of a root of `𝔪` is a
  root of `𝔤`. `weight_symm_apply_eq_zero`: it vanishes at `X₁`.
- `mem_range_of_mem_weightSpace`: a weight vector of `𝔤` whose weight vanishes at `X₁` lies in
  the range of `ι`. `weight_eq_zero_of_mem_range` is the converse for nonzero weight vectors in
  the range.
- `IsSplitCartan.comap`: `ι⁻¹(𝔥)` is a split Cartan subalgebra of `𝔪`. The bracket of
  `ι⁻¹(𝔥)` is zero since `ι` is injective. Every element of `𝔪` is a sum of weight vectors: the
  coordinates of `ι x` in a `WeightBasis` of `𝔤` are supported on weights vanishing at `X₁`, and
  the corresponding basis vectors have preimages that are weight vectors. The zero weight space is
  `ι⁻¹(𝔥)` because that of `𝔤` is `𝔥`. A root space of `𝔪` injects into a root space of `𝔤`, so it
  is a line. The `𝔰𝔩₂`-triples of `𝔤` for roots vanishing at `X₁` lie in the range of `ι`.
  Reducedness passes to `𝔪` through the transported weights.

For a reductive Lie algebra with Cartan subalgebra `𝔥`, the centralizer of an element of `𝔥` is
a Levi subalgebra containing `𝔥`, and its roots are the roots of `𝔤` vanishing at that element.
The module proves the corresponding statements for the axioms of `IsSplitCartan`.

# Restricted subspaces in the ambient character quotient

This is internal algebraic infrastructure for the support filtration in the general geometric lemma. It extends the published `Jacquet.LocalizationFiltration` construction to subspaces stable under a subgroup `Q` rather than under the whole ambient group `G`. It is derived from the existing character quotient and subrepresentation APIs; no new result is attributed directly to the literature.

Let `ρ` be a representation of `G` over a commutative ring `R`, let `U` be a subgroup, and let `θ : U →* Rˣ`. Assume that `M` normalizes `U`, preserves `θ`, and lies in `Q`. For a subrepresentation `S` of the restriction of `ρ` to `Q`, `restrictedImageSubrepresentation` is the image of its underlying submodule under the canonical map

`V → V / span {ρ(u)v − θ(u)v}`.

This is the quotient of the original ambient representation. The definition does not replace it by the quotient of `S` or of any other carrier. An image class is `M`-stable because each element of `M` belongs to `Q`, so it sends a representative in `S` to another representative in `S`. Neither `U ≤ Q` nor `G`-stability of `S` is required.

The membership lemmas say that a class belongs to this image exactly when it has a representative in `S`; for a specified ambient vector `v`, this means that there is `s ∈ S` with `s − v` in the ambient relation span. Monotonicity follows by reusing the representative. The zero image is zero, the full image is full by surjectivity of the quotient map, and images preserve sums by the corresponding submodule image identity.

For an arbitrary input category and functor `F` into `G`-representations, `restrictedImageSubfunctor` maps an actual subfunctor of `F` restricted to `Q` into the localization of `F`. Naturality follows from the existing localization map formula on quotient representatives and preservation of the original subspaces. `restrictedImageFiltration` applies this construction to each step of a specified finite filtration, with the same indices, monotonicity and endpoints. Its final membership lemma exposes the representative in the corresponding input step.

These constructions prove no intersection preservation, exactness, graded-piece identification, or geometric lemma. No topology or smoothness hypotheses are imposed. The scalar, group, representation-carrier and input-category universes are independent.

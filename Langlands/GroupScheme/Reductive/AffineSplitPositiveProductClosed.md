# Ordered products over positive roots are closed immersions

This module is a step toward clause 3 of
[`AffineSplitRootSubgroupSpanningStatement`](AffineSplitRootSubgroupSpanningStatement.md).
Fix a base `b`. For an injective family `e : Fin n → J` of `b`-positive roots, it shows that
the ordered product morphism `positiveProductMap u e : 𝔾ₐⁿ ⟶ G`,
`w ↦ ∏ₖ u_{e k}(wₖ)` (from [`SplitBorelPositiveIso`](SplitBorelPositiveIso.md)), is a closed
immersion. Conrad's proof of Proposition 5.1.16 (*Reductive group schemes* (2014), p.147)
starts from the same fact: "since `U_{Φ⁺}` is directly spanned in any order by the root
groups `U_a` for `a ∈ Φ⁺`, for any enumeration `{a_i}` of `Ψ` the multiplication map
`∏ U_{a_i} → G` is an isomorphism onto a smooth closed subscheme of `U_{Φ⁺}`".

The module adds two auxiliary coordinate morphisms and some theorems. It adds no
statements or axioms. Everything is in `Langlands.GroupScheme.LocalSplitCell`.

## Definitions

- `vectorPad n n' : 𝔾ₐⁿ ⟶ 𝔾ₐⁿ⁺ⁿ'` is `x ↦ (x, 0)`, defined through the coordinates of the
  universal point.
- `vectorTrunc n n' : 𝔾ₐⁿ⁺ⁿ' ⟶ 𝔾ₐⁿ` is the projection onto the first `n` coordinates.

These are morphisms of schemes over `Spec R`, not group-scheme homomorphisms. Only their
underlying morphisms are used.

## Results

- `coordinates_vectorPad`: the coordinates of `vectorPad` are `Fin.addCases x 0`.
- `vectorPad_comp_vectorTrunc`: `vectorPad ≫ vectorTrunc = 𝟙`.
- `vectorPad_comp_positiveProductMap`: if the enumeration `posF : Fin (n + n') → J` begins
  with `e`, then `vectorPad ≫ positiveProductMap u posF = positiveProductMap u e`. This
  uses `orderedProduct_initial`: trailing zero coordinates do not change the product.
- `isClosedImmersion_positiveProductMap_aux`: assume that the big cell for `neg` and
  `posF` is an open immersion, that `posF` begins with `e`, and that `ν` is negative on
  `neg` and positive on `posF`. Then `positiveProductMap u e` is a closed immersion.
- `isClosedImmersion_positiveProductMap hG hmax hP hv b e he hpos`: the main result, for a
  reductive `G` with the hypotheses of the target statement.

## Proof

Let `χ = AffineRegularBorel.cocharacter i ν`, and let `jU : U ⟶ G` be the Library's closed
representative of the contracting subgroup `U_G(χ)`
(`Dynamic.Affine.unipotentScheme`). Since `ν` is positive on `e`, `positiveProductMap u e`
factors through `jU` as `s`, by the Library's `positiveProductToUnipotent`. Since
`jU.left` is a closed immersion, it suffices to show that `s.left` is a closed immersion.

The Library's `positiveProductIso` gives an isomorphism `φ : 𝔾ₐⁿ⁺ⁿ' ≅ U` with
`φ.inv ≫ positiveProductMap u posF = jU`. Since `positiveProductMap u posF` is a
monomorphism, `s ≫ φ.inv = vectorPad`. Hence `s ≫ (φ.inv ≫ vectorTrunc) = 𝟙`. So `s` has
a retraction. Since the identity is a closed immersion and the retraction is a morphism of
affine schemes, hence separated, `IsClosedImmersion.of_comp` shows that `s.left` is a
closed immersion. The main theorem obtains the data for the auxiliary lemma from the
Library's `exists_cell_initial`, applied to the duplicate-free list `List.ofFn e`.

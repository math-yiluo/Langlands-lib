# Orbit-block products and actual coordinate pullbacks

This internal helper works with arbitrary fields `k` and `K` in universe `u`,
an algebra structure `Algebra k K`, an index type `I : Type u`, and an actual
group scheme `G` over `k`. It constructs no root maps, pinning, or cross-section.
Its products consist of actual points of `G` with values in `MvPolynomial I K`.

For a list of lists `blocks` and a supplied family of factors `f`,
`blockProduct` first multiplies each list of factors in its given order and
then multiplies the resulting block products in the given block order.
The lists may be empty and need not cover `I` or have distinct entries.

`blockProduct_fixed` takes a supplied action `ρ` of `Aut(K/k)` on `I` and
three explicit premises:

- Every automorphism preserves each supplied block as a multiset.
- The factors in each block commute pairwise.
- Applying the actual point map induced by `PolynomialGalois.orbitAction`
  to `f i` gives `f (ρ σ i)`.

It proves that this combined coefficient-and-variable action fixes the actual
block product. The proof maps both list products through the point monoid
homomorphism and uses `List.Perm.prod_eq'` within each block. The order between
blocks is retained; no relation between factors in different blocks is assumed.

Assuming `G` affine, `pullbackK x` is the scalar extension of the actual
coordinate map `CocharacterDatum.coord x`. Writing `A` for
`CocharacterDatum.coordAlgebra G`, it is the `K`-algebra map
`K ⊗[k] A →ₐ[K] MvPolynomial I K` sending

`c ⊗ a ↦ C(c) * (CocharacterDatum.coord x).hom a`.

`pullback x` is this same map restricted to the ground scalars. Both pure-tensor
formulas are proved. Thus the coordinate algebra and its evaluation come from
the actual affine group scheme, rather than from a substitute polynomial model.

For any actual point `x` fixed by the combined action, `coord_fixed` proves
that each ground-coordinate evaluation is fixed, using naturality of
`CocharacterDatum.coord`. `pullback_equivariant` then proves, for every tensor
`z` and every automorphism `σ`, the equation

`pullback x (coefficientConjugate σ z) = orbitAction ρ σ (pullback x z)`.

The implemented proof uses tensor induction. On a pure tensor, the two sides
agree by the displayed formula, the action on constant polynomials, and
`coord_fixed`; the sum case follows from the algebra-map laws. The induction
principle includes zero as the pure tensor with both entries zero.

If `IsGalois k K`, `map_groundIdeal_pullback_ker_eq` applies the published
`PolynomialGalois.map_groundIdeal_ker_eq`. The actual ideal
`RingHom.ker (pullback x).toRingHom` equals the extension of its contraction
along `a ↦ 1 ⊗ a`. The final theorem
`map_groundIdeal_blockProduct_ker_eq` specializes this equality to the block
product using `blockProduct_fixed`. No finite degree, perfectness, infinitude,
reductivity, or splitness premise is used.

The provenance is internal: the list-product argument uses Mathlib's monoid
homomorphism and permutation lemmas, the pullback uses the tensor-product
universal property and the Library's actual affine coordinates, and ideal
descent reuses the published arbitrary-Galois helper. This unit asserts no new
literature-specific theorem from Steinberg or Borel–Springer.

Consumers must construct a compatible base-changed pinning and actual root
factors, supply orbit blocks, prove factor transport and within-block
commutation, and identify this product with the relevant Steinberg morphism.
They must also identify the closed-image ideal, perform the required scheme
and ideal-sheaf descent, and establish the remaining cross-section and rational
lifting geometry. This helper proves none of those existence or comparison
claims and makes no assertion of a global section in even type A.

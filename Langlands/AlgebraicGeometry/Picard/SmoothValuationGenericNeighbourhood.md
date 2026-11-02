# Total neighbourhoods trivializing a generic line bundle

For a morphism `q : Y ⟶ X`, a Library line bundle `D` on `Y`, and a point
`x` of `X`, `GenericTrivializingNeighbourhood q D x` stores an actual open
neighbourhood `U` of `x` and an actual isomorphism from the restriction
of `D.obj` to `q⁻¹(U)` to the structure sheaf there. The proposition
`HasGenericTrivializingNeighbourhoods` requires such data at every point
of the total scheme. These definitions apply to arbitrary scheme maps.

The first transport lemma recovers an actual sheaf trivialization from
one after pullback along a scheme isomorphism. It pulls back along the
inverse, and uses the identity, composition and structure-sheaf
pullback comparisons. The second lemma applies this to the restriction
of a scheme isomorphism over each inverse-image open. Consequently a
change of presentation of the generic scheme preserves the existence
of these total neighbourhoods.

Let `R` be any valuation domain, `A` a smooth `R`-algebra, and `K` any
specified fraction field of `R`. Set `B = A ⊗[R] K`. For every actual
Library line bundle on `Spec B` and every point `x` of `Spec A`, the
imported generic principal-neighbourhood theorem supplies `a` outside
`x.asIdeal` and an actual trivialization after inverting its image in
`B`. Mathlib's `basicOpenIsoSpecAway` identifies that localization
spectrum with the actual basic open in `Spec B`. Pullback composition
and the canonical structure-sheaf comparison turn the localization
trivialization into a trivialization of the restriction to that open.
It is precisely the inverse image of `D(a)` in `Spec A`, so it gives
`hasGenericTrivializingNeighbourhoods_tensorSpec`.

The canonical `pullbackSpecIso` identifies the actual fibre product
`Spec A ×[Spec R] Spec K` with `Spec B`. Its projection identity gives
exactly the total-space coefficient inclusion used above. Transport
through this isomorphism proves the same neighbourhood result for the
actual fibre product and its canonical first projection. The definition
`affineGenericTrivializingNeighbourhood` chooses the total open,
its point membership, and the actual restriction-sheaf isomorphism.

This is an internal derivation from `SmoothValuationGenericChart`, the
actual line-bundle pullback functor, and Mathlib's basic-open and affine
fibre-product isomorphisms. Arbitrary valuation rank and the field case
are retained. This pair establishes local generic trivializations for
smooth affine total schemes. Compatibility on intersections and global
extension remain to be proved.

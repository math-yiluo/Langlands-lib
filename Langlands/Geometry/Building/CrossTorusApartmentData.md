# Apartment data under actual cross-torus isomorphisms

Author: Worker 118.

Over an arbitrary field, take actual isomorphisms `e : S ≅ S'` and
`f : G ≅ H` whose square with `i : S.toGrp ⟶ G` and `j : S'.toGrp ⟶ H`
commutes. Assume monomorphisms on the underlying inclusions and affine structural
morphisms on both ambient groups. For the unchanged function `ω : kˣ → ℝ`,
`KPApartmentData.transportEquiv e f h` identifies the full types of
`KPApartmentData i ω` and `KPApartmentData j ω`.

The forward constructor `D.transport e f h` takes the image of the entire carrier
of `D` under `RootFunctionFamily.transportEquiv e f`. Its witness is the
transport of the original compatible valuation. Preservation of all V0--V5
axioms and split-torus compatibility comes from `CrossTorusValuation`.
The actual real cocharacter equivalence and family translation identity prove
that this image is precisely the target translation orbit. Surjectivity of
the actual normalizer-point equivalence and the original family action identity
prove stability under the entire target normalizer.

`transport_carrier` gives the exact image formula; `mem_transport_iff` expresses
membership by the inverse of the original family equivalence. The carrier
determines apartment data because all other structure fields are propositions.
Transport along the inverse square therefore gives both inverse laws for
`transportEquiv`, directly from the original family inverse laws.

This is an internal constructor derived from the published apartment-data
interface and actual cross-torus transport interfaces. It constructs target
data from supplied source data. It does not assert the existence of apartment
data for an arbitrary group. Here "valid apartment data" has exactly the existing
`KPApartmentData` meaning: V0--V5, the split-torus portion of V6, one full
equipollence class and normalizer stability. Full centralizer V6, V7,
apartment-point affine comparison, apartment intersections, full A2 and the
general building-existence theorem are separate obligations.

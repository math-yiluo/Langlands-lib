# Scheme extraction over a represented base

This is an internal categorical consequence of the published definitions of
`IsRepresentableMorphism`, `IsAffineMorphism`, and Mathlib's relative morphism
properties. It supplies the scheme-extraction step needed after a geometric
representability theorem; it does not assert proper-Hom representability.

`IsRepresentableMorphism.representingScheme` is the actual scheme over the
base obtained from the represented pullback along the identity of the
represented target. The following existence results use this scheme.

`IsRepresentableMorphism.exists_representation_over` takes a relatively
representable natural transformation `f : F ⟶ schemeYoneda(S)(B)` for an
arbitrary scheme `S` and scheme `B` over `S`. It constructs an actual scheme
`V` over `S`, an actual morphism `p : V ⟶ B` over `S`, and a natural
isomorphism `schemeYoneda(S)(V) ≅ F`. The forward isomorphism composed with
`f` is exactly `schemeYoneda(S).map p`. The presheaves retain the published
lifted value universe.

The proof takes the represented pullback of `f` along the identity of its
represented target. Its first projection is an isomorphism because it is
the base change of an identity. The pullback square gives the required
equality of natural transformations.

`IsAffineMorphism.exists_representation_over` uses the same construction,
assuming both affineness and relative local finite presentation of `f`.
Each hypothesis applies to this represented pullback, so the actual map
`p.left` is affine and locally of finite presentation. Both properties
are transferred to the same chosen representative, independently of the
representative chosen internally by the local finite-presentation hypothesis.

`IsAffineMorphism.exists_representation` specializes to
`B = Over.mk (𝟙 S)`. The equation defining the slice morphism identifies
`p.left` with the structure map `V.hom`; hence the result is an actual scheme
over `S` with affine, locally finitely presented structure map and a natural
isomorphism on the entire slice of schemes over `S`.

No sheaf, algebraic-space, or finiteness hypothesis on the base scheme is
needed for these categorical results. The mathematical inputs are the
existing definitions and pullback universal property, so the provenance is
derived rather than a new claim from external literature.

# Limit descent from one represented target-atlas pullback

This internal unit transports four published scheme limit-descent theorems
through an actual fixed represented target-atlas pullback. It retains
representability and scheme finiteness as explicit premises. It does not prove
eventual representability or the four unrestricted clauses of
`SpaceLimitPropertyDescentStatement`.

`RepresentedMorphismAtlas f` consists of an explicit proof that `f` is
representable, a surjective étale scheme atlas of its target, and a scheme
pullback of `f` along that atlas, with the full cartesian square. Its
`baseChange` restricts this square and uses the natural scheme-Yoneda
comparison at both scheme corners. The square remains cartesian; the target
chart remains étale and geometrically surjective.

For any scheme morphism property stable under base change and descending
along surjective étale scheme maps, `property_baseChange_iff` identifies the
space property after base change with the same property on the base change
of the original fixed scheme projection. The generic represented-atlas test
supplies both directions. The arrow isomorphism induced by exchanging the
two scheme-pullback factors reconciles the slice convention with the
published scheme-limit convention.

`SchemeStructuralPropertyDescent` packages a sufficient scheme theorem:
both structural maps are locally of finite presentation, quasi-compact and
quasi-separated over the affine base. It is proved here for closed
immersions, affine morphisms, open immersions and finite morphisms by the
existing relative scheme descent theorems. For the three theorems needing
finiteness of the scheme projection, its source is compact and its target
quasi-separated; cancellation of the structure-map factorization gives
local finite type, and quasi-separatedness of the source gives
quasi-separatedness of the projection.

Under precisely these six structural scheme hypotheses,
`RepresentedMorphismAtlas.property_limit_iff` proves detection at a later
stage for the space morphism. The proof uses the cofiltered category
`Over i`, whose initial forgetful functor preserves the original limit.
An object of this category supplies the required arrow to the original
stage. The reverse direction uses iterated-base-change naturality.
The four final specializations concern the original published space
predicates `IsClosedImmersion`, `IsAffineMorphism`, `IsOpenImmersion` and
`IsFinite`, with their definitions unchanged.

The remaining geometric step for the host task is to obtain such a finite
represented pullback at a suitable stage from representability only at the
limit. Neither the explicit representability field nor the six structural
premises are discharged by this unit.

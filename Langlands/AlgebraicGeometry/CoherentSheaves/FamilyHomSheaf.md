# The sheaf of all actual coherent-family morphisms

For any morphism of schemes `f : X ⟶ S`, any test `T : Over S`, and any
two actual families `M N : FamilyGroupoid f T`, `homSheaf f M N` is an fppf
sheaf on the entire scheme slice over `T.left`. Its underlying presheaf is
exactly the existing `FamilyGroupoid.homPresheaf f M N`.

Thus the values remain the explicitly lifted types of all actual module
maps between the pulled-back families. The restriction maps remain the
ones already defined for that presheaf. The construction includes every
scheme test and slice arrow. It assumes no properness, finite presentation,
or flatness of `f`, and no condition on the base or test scheme beyond
being schemes in the given universe. The families retain their existing
finite-presentation and relative-flatness conditions.

`homPresheaf_isSheaf_fpqc` proves the stronger fpqc sheaf condition, and
`homPresheaf_isSheaf_fppf` gives the fppf condition used to bundle
`homSheaf`. Each proof transfers the corresponding intrinsic module Hom
descent theorem through the full-slice natural isomorphism
`homPresheafIntrinsicIso`. The underlying target module of `N` is finitely
presented and therefore quasi-coherent, supplying the only hypothesis of
the intrinsic descent theorem. The conversion between the two standard
type-valued sheaf predicates does not change the presheaf.

This is an internal derived composition of the actual-family comparison
and intrinsic module Hom descent. The supporting intrinsic descent pair
proves its own sheaf theorem by open-cover and affine faithfully flat
descent of ordinary module maps, as described in its paired Markdown.
Neither this transfer nor that descent proves finite linear model
existence or the affine finite-presentation representation theorem for
proper coherent-family Hom.

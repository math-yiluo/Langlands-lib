# The sheaf of natural local group isomorphisms

This is internal categorical content derived from the existing
all-test `LocalGroupIso` interface, the group-valued represented point functor,
and Mathlib's theorem that the internal Hom into a sheaf is a sheaf.

`LocalGroupIso.toHom` views a local group-isomorphism family on `U` as a
natural transformation of the group-valued point functors restricted to the
slice over `U`. `ofNatIso` recovers a family from an isomorphism of those
restricted functors. Forgetting the inverse is injective, commutes with
parameter refinement, and composition with the family inverse gives the
identity transformation.

`points_isSheaf` uses the representability of the underlying group-point
functor and reflection of limits by the forgetful functor from groups.
Consequently it applies to every subcanonical topology on the category of
schemes over the base.

`LocalGroupIso.isSheaf` glues the forward and inverse transformations using
Mathlib's internal Hom sheaf theorem. The two composites are identities
because this equality holds after restriction to each cover member, and the
endomorphism internal Hom is separated. The resulting natural isomorphism
recovers a local family. Injectivity into the forward internal Hom proves
uniqueness. All relative scheme tests are retained, with no affine,
connectedness, finiteness, reductivity, or representability-of-Isom premise.
`LocalGroupIso.sheaf` packages this underlying presheaf and proved sheaf condition.
This proves a sheaf property; geometric representability still requires
construction and effective descent of scheme representatives.

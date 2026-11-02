# Open subsheaves and images of etale morphisms

This internal module derives local membership and sheaf closure for open
subfunctors from the imported Library and Mathlib constructions. No independent
source assertion is introduced.

`mem_of_coveringSieve` proves that membership in a representable open
subfunctor is local for the fppf topology. It refines a covering sieve to a
scheme covering family and uses the fact that the maps in that family cover
the points of the test scheme. The jointly surjective membership criterion
from OpenSubfunctorPoints then gives global membership. The ambient presheaf
need not be a sheaf for this local membership assertion.

`isSheaf_of_open` combines local membership with the sheaf property of the
ambient presheaf. Thus a representable open subfunctor of an fppf sheaf is
itself an fppf sheaf.

`sheafify_preimage` identifies local closure after inverse image with the
inverse image of local closure: their sieves of membership are equal by
naturality. `sheafify_range_comp` says that an open chart preceded by an
fppf locally surjective scheme morphism has that chart as its sheafified
image. One inclusion uses the local membership criterion for opens; the
other uses the covering image sieve of the preceding map.

For an etale scheme morphism, `schemeImageOpen`, `schemeImage`,
`schemeImageι`, and `toSchemeImage` construct its actual open image and
factorization through it. The factor is etale by cancellation of the open
inclusion and is surjective by the description of the image. Consequently
`sheafify_range_schemeYoneda_map` identifies the sheafified presheaf image
with the range of this open inclusion. The general theorem
`sheafify_range_open` applies this scheme construction to each represented
base change of an etale transformation. The inverse-image identity for
sheafification and the range identity for pullback squares identify the
required subfunctor. The source can be any presheaf. If the target is a
sheaf, `sheafify_range_isSheaf` then proves the image is a sheaf.

`isLocallySurjective_of_isPullback` proves stability of local surjectivity
by lifting sections in the pointwise pullback of types. For an etale scheme
morphism, `scheme_surjective_of_isLocallySurjective` first identifies its
sheafified range with the top subfunctor. The identity section therefore
factors through its open image, so that image contains every point.
Applying this argument to represented base changes gives
`isSurjective_of_isEtale_isLocallySurjective`.

The canonical transformation `Subfunctor.toRangeSheafify` factors the
original map through its sheafified image. `toRangeSheafify_isPullback`
exhibits this factor as the base change of the original map along the
image inclusion. Base change proves `toRangeSheafify_isEtale`; its automatic
local surjectivity and the preceding geometric criterion prove
`toRangeSheafify_isSurjective`.

`diag_isPullback_of_mono` is a general categorical lemma: the diagonal of
the source of a monomorphism is the pullback of the target diagonal along
the product of that monomorphism with itself. Its proof constructs the
pullback limit and uses cancellation of the monomorphism. Applied to the
inclusion of any subfunctor, this proves
`isClosedImmersion_diag_subfunctor` by base change of closed immersions.
This assertion requires neither openness nor a sheaf hypothesis.

Finally, `sheafify_range_isAlgebraicSpace` applies these results to an
etale map from an actual scheme to an fppf sheaf with closed diagonal.
Its image is a sheaf with representable closed diagonal, and the canonical
factorization is an etale surjective atlas. These are precisely the
Library conditions for an algebraic space. This module supplies helper
proofs for the group-space representability task; it does not prove that
task's final representability statement.

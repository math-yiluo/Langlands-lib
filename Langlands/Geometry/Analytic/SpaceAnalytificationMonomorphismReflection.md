# Reflection of monomorphisms by affine overlaps

The algebra map `affineOverlapComparison` runs from the overlap algebra for
two affine tests over the target to the overlap algebra over the source.
It comes from the lift between their presheaf pullbacks, transported
through the fully faithful scheme Yoneda functor and the relative spectrum
point equivalence. Its composites with the two projection algebra maps
are the original projection algebra maps for the source overlap.

If the source overlap algebra is a quotient of the tensor product of the
test algebras, its comparison map is surjective. Indeed, the surjective
tensor product map factors as the tensor product map to the target overlap
followed by the comparison.

For compatible analytifications, the affine pullback axiom produces the
two categorical analytic pullbacks. If the analytic map is monic, the
pullback over the source can also serve as the pullback over the target.
Functoriality of affine analytification identifies the comparison map
with the canonical isomorphism between the two analytic pullbacks by its
two projections.

Assume that the analytification of an affine algebra map reflects
étaleness. The analytified isomorphism is étale, so the comparison algebra
map is étale and therefore flat. The analytic isomorphism is surjective on
points. The maximal-center criterion then proves that the surjective
comparison map is bijective. Its algebra inverse gives a map from the
target overlap to the source overlap preserving both affine projections.
Consequently, maps from any scheme test into the two affine tests that
agree over the target also agree over the source.

For `mono_of_mono_analytification`, the two algebraic spaces are separated,
and the source is locally of finite type over `Spec K`. The proof chooses
an étale source atlas and takes the affine open cover of its representing
scheme. Each member of this cover has a finite-type coordinate algebra
over `K`. For each section on an arbitrary test scheme, the sieve of arrows
on which it factors through one such affine chart is covering. This follows
from local surjectivity of the atlas and pullback stability of the affine
open cover. Two sections with the same target image thus agree on the
intersection of their covering sieves by the affine cancellation result.
Separatedness for the algebraic étale sheaf identifies the sections, giving
monicity of the map of presheaves.

This is an internal consequence of the Library's relative spectrum point
equivalence, affine analytification and pullback interfaces, together with
the maximal-center criterion and the stated affine étale reflection premise.

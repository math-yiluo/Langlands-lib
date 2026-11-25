# Split maximal tori in actual product factors of a prescribed split pair

This derived construction works over arbitrary fields at every
universe parameter. It supplies actual split maximal tori in the factors of
a `SimplyConnectedAlmostSimpleProduct`, with explicit compatibility with a
specified ambient split maximal torus and an actual split projection from it.
No extra conjugacy or arithmetic premise is imposed.

`commute_inclusion_iff` says that commutation with the inclusion of one factor
is detected by projection of the other point to that factor. Projection proves
one direction; equality of every product coordinate proves the other. The
self-coordinate uses the original commutation, and all other coordinates of
the inserted point are the identity.

`FactorMaximalTorus` extends `CompatibleNormalMaximalTorus` for a specified
factor inclusion and the prescribed ambient torus. It adds splitness of the
factor torus, a projection from the ambient torus, the exact projection square
in the factor, and the equality that its ambient-torus inclusion followed by
this projection is the identity.

`nonempty_factorMaximalTorus` constructs this data. Project the ambient torus
to the selected factor and insert it back into the original group. Its actual
closed split-torus image is supplied by `dominantFactorization`. Product
coordinate commutation shows that the original map centralizes the ambient
torus. The published self-centralization theorem identifies that centralizer
with the ambient torus. Closed containment for a schematically dominant image
therefore factors the image through the ambient torus. Its original map also
factors through the chosen group factor, so the same image has a closed
inclusion there. These two factorizations retain the same ambient composite.
The dominant factor map from the original torus gives the required projection;
cancelling the closed factor inclusion proves the section identity.

To prove maximality in the group factor, let a factor point centralize this
image torus. The projection square and `commute_inclusion_iff` show that its
ambient image centralizes the prescribed ambient torus. It therefore comes
from an ambient-torus point. Projecting that point back to the group factor
shows that the original point lies in the factor torus. Thus the full
centralizer of this factor torus is contained in its own range. Any larger
closed torus would centralize it by commutativity, hence would lie in that
same range. The two represented subgroup factorizations give an inverse to
the inclusion between the tori, which proves maximality in the Library's
actual definition.

`factorMaximalTorus` chooses one such set of actual data. This module compares
actual tori and their maps. It does not construct a factor-root datum map or
prove the whole component-factor realization theorem. Provenance is internal
derived interface material, with no downstream local rank-one classification
or Kneser–Tits input.

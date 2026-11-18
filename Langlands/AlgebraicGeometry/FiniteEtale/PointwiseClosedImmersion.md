# Closed immersions detected on points of an étale scheme

This internal helper module supports the converse direction of
`Langlands.GroupScheme.EtaleMultiplicativeTypeOrderStatement`. It proves that a
morphism from an affine étale scheme over a separably closed field to an affine
scheme is a closed immersion if its source has finitely many rational points
and its map on rational points is injective.

The proof adapts the published interpolation and section extensionality
arguments of `Langlands.GroupScheme.Cartier.AlgClosedCharacterSeparation`.
Section extensionality uses reducedness of an étale scheme over a field and
that every point of an étale scheme over a separably closed field is rational.
Thus its proof works over a separably closed field without the stronger
algebraically closed hypothesis of the existing lemma.

For interpolation, affine target functions separate the distinct images of
two source points. Normalize their differences, form finite products giving
delta functions on the source point set, and take linear combinations. Every
source section has the same point values as the pullback of such a target
function; section extensionality makes these sections equal. The resulting
surjectivity on global functions implies that the affine morphism is a closed
immersion.

This is an internal derived result, not a separate assertion attributed to
Milne. It imposes no smoothness or finite type hypothesis on the target.

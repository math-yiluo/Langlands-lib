# Induction of actual geometric pieces on exact finite-length K0

This internal adapter derives the induced-piece identity from the actual
intersection transport, flattened coordinates, normalized induction in stages
and whole-Levi conjugacy invariance. It concerns the full exact Grothendieck
quotient of finite-length smooth complex representations.

`refinedIntersectionTransportK0` is the map of actual equality relabeling,
inverse intersection conjugation and equality relabeling. Their published
finite-length and short-exact preservation results prove that the map descends
to the exact quotient. Its generator formula computes the class of the literal
transported smooth object.

`flattenedLeviK0_comp_refinedIntersectionTransportK0` compares flattening after
this transport with whole-Levi inverse conjugation after source flattening.
The proof uses object-generator extensionality, the generator formulas and
`flattenedIntersectionTransportEquiv` between the actual representations. This
part holds over any topological field whose ring operations are continuous.

For any supplied p-adic field and topology,
`geometricPieceK0_eq_refinedInduction_comp_transport` factors the actual geometric
piece into normalized refined Jacquet restriction, the middle transport and
normalized refined induction. It is proved on actual finite-length generators
using the defining smooth functor and the generator formulas.

`normalizedInductionK0_comp_geometricPieceK0` identifies induction of this piece
to the ambient general linear group with induction from the source Levi of its
normalized refined induction-after-Jacquet term. Both supplied intersection
equalities determine the concrete conjugacy between the flattened Levis. The
proof composes the factorization, flattened induction in stages, the middle
comparison, whole-Levi induction invariance and source induction in stages.

All identities are equalities of integer-linear maps, so apply to every virtual
class. They retain independent field and carrier universes, saturated carriers
`Type (max uF uV)` and every rank, including zero. Only the stated intersection
equalities are assumed; minimality and positive rank are unnecessary. The
normalizations are those of the existing upper block parabolics, positive
half-modulus covariance and right translation. This adapter is a derived
algebraic prerequisite and asserts neither Aubert commutation nor analytic
segment classification.

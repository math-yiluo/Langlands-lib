# General presented affinoids: Noetherianity and closed ideals

This is an internal prerequisite for finite-cover closed-ideal descent. Its
proof is derived from the Library's strict Tate Noetherianity theorem and the
actual coefficient retraction constructed in `StrictBaseChangeRetraction`.
It does not assume flatness or ideal effectiveness.

For any strict scalar extension equipped with the published bounded
module-linear retraction, `comap_map_strictBaseChangeHom` proves that extending
an arbitrary algebraic ideal and contracting it recovers that ideal. The
published descent ideal contains the generated image ideal, and applying its
defining condition at the unit, followed by the retraction identity, proves the
nontrivial containment. Extension is therefore an order embedding of ideal
lattices, constructed as `strictBaseChangeIdealOrderEmbedding`.

Realize the finitely many radii of the original presentation in a complete
extension field. Its actual strict scalar extension is Noetherian by
`TateNoetherian`; the ideal order embedding transfers the ascending-chain
condition back to the original algebra. This supplies a Noetherian instance for
every presented positive-polyradius affinoid over a complete ultrametric normed
field.

For closedness, realize one additional radius, equal to two. This guarantees
that the extension field is nontrivially normed even if the original field is
trivially valued. Every ideal in the strict extension is closed by
`isClosed_ideal_of_noetherian_banach`. The original ideal is its inverse image
under the continuous scalar-extension homomorphism, by the contraction
identity, so is closed in the original stored quotient norm.

Both arguments retain arbitrary positive radii, trivial coefficient valuations,
nonreduced and zero algebras. No nonempty-spectrum hypothesis is used. These
results do not prove the reverse containment in finite-cover ideal
effectiveness.

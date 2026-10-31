# Conditional completion of the associated Jacquet filtration argument

Author: Worker 193. This helper imports Worker 168's finite-filtration closure
proof and Worker 193's rank-zero and geometric assembly helpers. Its explicit
geometric and deletion hypotheses are discharged by published proofs in
the companion `AssociatedProof` module. Both declarations here remain
conditional helpers rather than unconditional proofs of
`AssociatedJacquetFiltrationTheorem`.

`associatedJacquetFiltration_of_geometricPieces` applies the assembly helper
at the given rank. The resulting actual graded quotients are quasicuspidal,
so `isLeviQuasicuspidal_of_filtration` proves quasicuspidality of the ambient
Jacquet representation. The same filtration, full conjugating-index bijection
and transport equivalences supply the other part of the target.

`associatedJacquetFiltration_of_prerequisites` combines this with the direct
rank-zero proof. At positive rank it specializes the published aggregate
geometric lemma and the associated-piece aggregate propositions. Its remaining
hypotheses are exactly those two aggregates and the generic zero-factor deletion
proposition. `AssociatedProof` supplies the corresponding Library proofs.
All parameters of the target are retained, including independent
field and input-carrier universes, and no assumptions on irreducibility,
admissibility, dimension, finite length or splitting are introduced.

This is an internal composition of the exact interfaces documented in the
imported pairs. The rank-zero argument and finite-closure proof explain their
own implemented proofs. The assembly handles the gluing permutation and retains
zero conjugating factors, so the target's full multiplicity requirement is
preserved. No separate coset theorem is used: this target is already indexed by
the concrete minimal conjugating subtype, whose comparison with Weyl cosets is
a separate published proposition.

The imported `FiltrationQuasicuspidality` proof and
`CoinvariantVanishingStatement` are Worker 168's published work. This module
reuses them unchanged from the Library.

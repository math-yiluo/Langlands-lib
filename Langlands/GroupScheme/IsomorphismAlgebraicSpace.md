# The full Isom algebraic space from supplied local representatives

Worker 812. This is an internal specialization of
`LocalRepresentation.ofCover`, the published all-test Isom sheaf, and the
Isom chart and transport constructions. It cites no additional literature.

For arbitrary group schemes `G,H` over an arbitrary scheme `S`, supplied full
Isom scheme representatives on the members of an actual étale covering family
give `GroupIsomorphismScheme.algebraicSpaceOfEtaleCover`. Its underlying
presheaf is definitionally `LocalGroupIso.presheaf G H`, with every relative
scheme as a test. The local representations are identified with restrictions
of that original presheaf by `localRepresentationIso`. The generic descent
construction derives a representable diagonal and a surjective étale scheme
atlas; neither is an extra assumption here.

`algebraicSpaceOfLocalAutomorphisms` instead takes full Aut scheme
representatives for the pullbacks of `G`, together with actual isomorphisms
from those pullbacks to the pullbacks of `H`. Postcomposition transports each
Aut representative on its identical parameter scheme to the required Isom
representative. All classification maps concern natural isomorphism families
on all relative schemes, rather than only points over fields.

`reductiveIsomorphismAlgebraicSpace` assumes
`ReductiveAutomorphismSchemeGeometryStatement` explicitly. Its application to
each pullback of the reductive source group supplies local Aut representatives.
The remaining input is an actual étale cover with nonempty actual
pullback-isomorphism types. No reductivity assumption on `H` is needed for this
constructor because the isomorphisms are already supplied.

`genericIsomorphismAlgebraicSpace` applies the existing actual fpqc isomorphism
cover of a generically isomorphic reductive DVR pair, and then the explicitly
supplied `ReductiveFpqcLocalIsomorphismStatement` to obtain such an étale cover.
It retains the original same-universe domain-DVR and specified fraction-field
hypotheses, without completeness, splitting or residue-field restrictions.
Both geometric statements are hypotheses, not proofs delivered by this module.

The output is an algebraic space for the full Isom sheaf. An actual representing
scheme and a proof of `GenericIsomorphismSchemeExistenceStatement` still require
further effective descent using the quotient geometry. This module establishes
neither those results nor either supplied geometric statement.

# Full Isom representability for generically isomorphic reductive DVR groups

`Langlands.GroupScheme.genericIsomorphismSchemeExistence` proves the
published `GenericIsomorphismSchemeExistenceStatement.{u}` for every
universe `u`. It gives a `GroupIsomorphismScheme G H` for reductive group
schemes over a domain DVR with a specified fraction field and a
generic-fibre isomorphism. The representative carries the universal
`LocalGroupIso` and classifies natural isomorphism families bijectively on
every relative scheme test. [Target statement](GenericIsomorphismSchemeExistenceStatement.md)

The proof applies the published affine pinned Isomorphism Theorem to
obtain smooth separated local automorphism representatives and, using
fppf-local pinned normalization, the constant full-label quotient charts.
The published local-model reduction combines those inputs with relative
adjoint quotient existence to give the automorphism geometry used in
the DVR construction. [Affine pinned theorem](AffinePinnedIsomorphismTheoremProof.md),
[Pinned quotient charts](PinnedOuterIsomorphismChartConstruction.md),
[Automorphism geometry from local models](AutomorphismSchemeGeometryFromLocalModels.md)

The DVR construction uses relative adjoint quotient existence for the
source group, and the fpqc-to-étale theorem to turn the generic
isomorphism cover into an étale family of group isomorphisms. It glues the
isomorphisms on the coproduct of that cover and uses postcomposition to
transport the local automorphism representative and its outer quotient
to the local Isom functor. Descent of the separated étale outer parameter
and effectivity of the affine map to that parameter then give the full
Isom scheme over the DVR. [Relative adjoint existence](../Adjoint/RelativeExistenceProof.md),
[Fpqc-to-étale theorem](FpqcLocalIsomorphismProof.md),
[DVR Isom construction](IsomorphismSchemeFromGeometry.md)

This proof composes published Library results at the same universe. The
original hypotheses on the DVR, fraction field, and groups suffice for
every step.

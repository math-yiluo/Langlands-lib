# Reductivity transport for represented dynamic centralizers

This internal, derived construction transports the Library's connected reductivity
predicate across isomorphisms and across different representatives of one
subgroup functor. It also proves affineness of closed subgroups and the reductivity
of every representative of a full dynamic centralizer. All declarations are
polymorphic in the universe `u`.

For any base scheme, `IsClosedSubgroup.isAffineHom` proves that a closed subgroup
`j : M ⟶ G` of a group scheme affine over the base is itself affine over the base.
Its proof writes the structure morphism of `M` as the closed immersion followed
by the affine structure morphism of `G`.

Over any field, `IsConnectedReductive.of_iso` transfers all four fields of
`IsConnectedReductive` from `G'` to `G` along an isomorphism `e : G ≅ G'`.
Smoothness and affineness transfer along its underlying scheme isomorphism;
connectedness transfers along the induced homeomorphism. For the geometric
unipotent radical, the proof base changes `e` to the algebraic closure and
applies the existing `HasTrivialUnipotentRadical.of_iso` from
`Langlands.GroupScheme.Reductive.GeneralLinear`. The ambient groups are general:
the import supplies an existing transport theorem and imposes no general-linear
hypothesis on the new declarations.

`SubgroupFunctor.top_isRepresentedBy_id` proves that the identity represents
the full subgroup functor. From any representative `j : M ⟶ G` of that functor,
`SubgroupFunctor.IsRepresentedBy.topIso` constructs an isomorphism `M ≅ G`,
and `topIso_hom` proves that its forward homomorphism is `j`.
The construction uses the published Yoneda isomorphism
`isoOfIsRepresentedBy`.

For any two representatives of the same subgroup functor of a group scheme over
a field, `SubgroupFunctor.IsRepresentedBy.isConnectedReductive` transfers
connected reductivity from one representative to the other. No closedness
assumption is needed for this transport.

`Dynamic.isConnectedReductive_of_centralizer_eq_top` applies these results to
every representative of a cocharacter's centralizer when the centralizer is
the full subgroup functor. In particular,
`Dynamic.isConnectedReductive_trivialCocharacter` covers the trivial cocharacter,
and `Dynamic.isConnectedReductive_of_commutative` covers every cocharacter of a
commutative connected reductive group. These proofs use the all-test equalities
already published in `Dynamic.ImproperParabolic`.

This module does not establish reductivity for a general cocharacter centralizer.
Its results isolate affine descent, independence of the chosen representative,
and the full-centralizer cases for use in that structural proof. No new
literature assertion or structural theorem is assumed.

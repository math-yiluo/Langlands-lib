# Transport of Galois pinning data along an isomorphism of groups

For fields `k`, `K` with `Algebra k K`, affine group schemes `G`, `G'` over `Spec k`, Galois
pinning data `d : GaloisPinningData k K G` and an isomorphism `e : G ≅ G'` of group schemes
over `k`, this module constructs Galois pinning data of `G'` and a pinned isomorphism from
`d` to it (`Reductive/GaloisPinningIso`). For a group scheme over `k`, `_K` denotes the actual
base change along `Spec K → Spec k`. The module declares a local instance that this base
change of an affine group scheme is affine.

## Construction

`GaloisPinningData.transport d e : GaloisPinningData k K G'` has:

* torus `d.torus` (the same `k`-torus) and inclusion `d.inclusion ≫ e.hom`;
* connected reductivity of `G'_K` (`transport_isConnectedReductive`), from that of `G_K`
  through the base change of `e` (Library `IsConnectedReductive.of_iso`);
* splitness of `T_K`, unchanged;
* maximality of `T_K` in `G'_K` (`transport_isMaximalTorus`), from that in `G_K` (Library
  `IsMaximalTorus.of_eq_iso_comp_comp_iso`);
* the same root indices, and the root datum and base of `d` transported along the identity
  `transportTorusIso` of `T_K`, which is the base change of the identity of `T`
  (`torusTransportRootDatum`, `torusTransportBase`). The transported root datum is realized
  by the new inclusion: the Library's `IsRootDatumOf.torusTransport` applied to the square
  `transport_square` (the inclusion of `d` followed by the base change of `e` is the new
  inclusion). Reducedness transfers by `torusTransportRootDatum_isReduced`;
* simple-root Lie vectors chosen by the Library's `RootPinning.ofSplitMaximalTorus`.

`groupHom_refl` records that the group homomorphism underlying the identity of a
commutative group scheme is the identity. `transport_torus` and `transport_inclusion` unfold
the construction.

## The pinned isomorphism

`GaloisPinningData.transportIso d e : d.Iso (d.transport e)` has group isomorphism `e`, torus
isomorphism the identity of `d.torus`, and root-datum equivalence
`torusTransportRootDatumEquiv` (identity on root indices, weight map
`characterLattice.congr` of the base change of the identity). Its square is
`d.inclusion ≫ e.hom = 𝟙 ≫ (d.inclusion ≫ e.hom)`. The base condition holds because
`torusTransportBase` has the same support (`torusTransportBase_support`).
`transportIso_groupIso` records that the group isomorphism is `e`.

## Provenance

Internal. Task 7603 (clause 1) asks for the transport of the Tits obstruction along actual
group isomorphisms. This construction supplies Galois pinning data on the target group that is
compatible with the given isomorphism, so that the transport along pinned isomorphisms applies
to every `k`-isomorphism of groups. No literature statement is formalized; the construction
only combines the Library's transport results for connected reductivity, maximal tori, root
data and root pinnings listed above.

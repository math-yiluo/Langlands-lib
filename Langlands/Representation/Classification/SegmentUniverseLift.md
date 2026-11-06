# Raising the carrier universe of segments and multisegments

This is internal implementation infrastructure, derived from the published
segment, multisegment and Langlands-head definitions and from the published
universe lift of smooth representations
(`Langlands/Representation/Category/UniverseLift.lean`). It is not attributed to
an original literature theorem. It assumes no classification theorem.

## Why it is needed

The Rodier classification statements in
`Langlands/Representation/Classification/MultisegmentClassificationStatement.lean`
quantify over multisegments `T.Multisegment.{max uF uV, uF}`, whose cuspidal
classes have carriers in the saturated universe `max uF uV`. Constructions such
as `Langlands.Correspondence.multisegmentOf` produce multisegments
`Multisegment.{uA, uF}` with carriers in an arbitrary universe `uA`. This module
moves such data to `max uF uA`, and proves that nothing about segments,
linkage or Langlands heads changes when it does.

## Supercuspidal objects and classes (`Langlands.GeneralLinear`)

For a field `F` with a topology and a rank `n`:

- `SupercuspidalRep.universeLift A` is the supercuspidal object whose
  underlying smooth representation is `SmoothRep.universeLift.{uF} A.obj`
  (carrier `ULift A.obj`, in `Type (max uF uV)`). Irreducibility transfers by
  `SmoothRep.isIrreducible_universeLift_iff`, and supercuspidality by
  `isSupercuspidal_of_equiv` along the equivalence `v ↦ ULift.up v`, which is
  `SupercuspidalRep.universeLiftEquiv A`.
- `SupercuspidalRep.equivOfIso` extracts the underlying representation
  equivalence of an isomorphism of supercuspidal objects.
  `universeLiftIso` lifts an isomorphism `A ≅ B` to `universeLift A ≅
  universeLift B`, and `isoOfUniverseLiftIso` goes back. Both are built by
  composing these equivalences with the `ULift` equivalences.
- `universeLiftTwistIso` is the isomorphism between the lift of the twist of
  `A` by a determinant character `χ` and the twist of the lift. Both have the
  carrier `ULift A.obj` and definitionally equal actions, so the identity
  linear map is an equivariant equivalence.
- `SupercuspidalClass.universeLift` is the induced map
  `SupercuspidalClass.{uV, uF} → SupercuspidalClass.{max uF uV, uF}` on
  isomorphism classes (`Quotient.map`). It sends `A.isoClass` to
  `(universeLift A).isoClass` (`universeLift_isoClass`, by definition). It is
  injective (`universeLift_injective`, from `isoOfUniverseLiftIso`), and it
  commutes with twists by determinant characters (`universeLift_twist`).

## Cuspidal data, segments and multisegments (`Langlands.PadicField.TopologicalData`)

For topological data `T` of a p-adic field `F`:

- `supercuspidalClassRealPowerTwist_universeLift`: lifting commutes with the
  real-power twist `T.supercuspidalClassRealPowerTwist n s`, which is a
  special case of the twist above.
- `CuspidalDatum.universeLift ρ` keeps the rank and lifts the class. It is
  injective (`universeLift_injective`, `universeLift_inj`), and it commutes
  with `CuspidalDatum.twist s` (`universeLift_twist`).
- `Segment.universeLift Δ` lifts the beginning `Δ.base` and keeps the length.
  Rank, length and degree do not change, by definition. The lift is
  injective. It sends `Δ.member i` to the lift of the member
  (`universeLift_member`), and its support is the image of `Δ.support`
  (`universeLift_support`). `exists_universeLift_eq`: a segment of the
  saturated universe whose beginning is a lift is itself a lift.
- `Segment.isLinked_universeLift_iff` and `Segment.precedes_universeLift_iff`:
  two lifted segments are linked, respectively one precedes the other, exactly
  when the original segments are. Linkage asks that neither support contain
  the other and that the union of supports be the support of a segment. The
  first two conditions transfer because the image of an injective map
  preserves and reflects inclusion. For the third, a segment whose support is
  the image of a union has a beginning in that image, so it is a lift (by
  `exists_universeLift_eq`), and injectivity of the image map then recovers
  the original equation. Precedence adds an equation between a beginning and
  a twisted beginning (`Δ₂.base = Δ₁.base.twist k` for some natural `k > 0`),
  which transfers by `CuspidalDatum.universeLift_twist` and injectivity. `isPrecedenceOrdered_universeLift_iff` is the resulting
  statement for families `Fin r → Segment`.
- `Multisegment.universeLift a` maps `Segment.universeLift` over the multiset.
  It is injective (`Multiset.map_injective`). It preserves the total degree
  (`universeLift_degree`), and on lists it is the map of lists
  (`universeLift_coe`).

## Segment heads and Langlands heads

- `segmentFactorUniverseLiftEquiv` is the equivalence between the twisted
  factor `T.segmentFactor A s` of a representative `A` and the same factor of
  `SmoothRep.universeLift A`. It is `twistEquiv` of the `ULift` equivalence.
  `segmentInducedUniverseLiftEquiv` is the equivalence between the normalized
  parabolic induction `T.segmentInduced A m hr` and its version for the lifted
  representative. It is the published cross-universe
  `T.normalizedParabolicInducedEquiv`, applied to the factorwise equivalences
  through `FiniteTensorFiltration.externalCongr`.
- `CuspidalDatum.universeLift_isRepresentedBy`: if `A` represents `ρ`, its lift
  represents the lift of `ρ`. This holds by `universeLift_isoClass`.
- `isSegmentHead_universeLift_iff`: for a representation `π` of
  `GeneralLinear Δ.degree F` with carrier in `max uF uV`,
  `T.IsSegmentHead Δ.universeLift π ↔ T.IsSegmentHead Δ π`. The proof picks a
  representative `A` of `Δ.base`. It rewrites both sides with the published
  `T.isSegmentHead_iff` (with `A` and with its lift), and then transports the
  irreducible-head property along `segmentInducedUniverseLiftEquiv` by
  `Classification.isIrreducibleHead_iff_of_equiv`.
- `SegmentProductDatum.universeLift d` lifts every segment and keeps the same
  output blocks, which live in `max uF uV` already. Its multisegment is the
  lift of `d.multisegment` (`universeLift_multisegment`), and it has the same
  Langlands heads (`universeLift_isLanglandsHead_iff`): precedence order
  transfers by `isPrecedenceOrdered_universeLift_iff`, each block condition by
  `isSegmentHead_universeLift_iff`, and the head condition on the induced
  representation is literally the same. `exists_universeLift_eq`: a datum all
  of whose segments are lifts is a lift.
- `Multisegment.isLanglandsHead_universeLift_iff`: for `π` with carrier in
  `max uF uV`, `a.universeLift.IsLanglandsHead π ↔ a.IsLanglandsHead π`.
  Backward: lift the witnessing datum. Forward: every segment of a witnessing
  datum `d'` lies in `a.universeLift`, so it is a lift. Hence `d'` is the lift
  of a datum `d` (`SegmentProductDatum.exists_universeLift_eq`), and
  `d.multisegment = a` by injectivity of `Multisegment.universeLift`.

The rank of every cuspidal datum and the degree of every segment and
multisegment are unchanged by the lift. So a representation of
`GeneralLinear a.degree F` is also a representation of
`GeneralLinear a.universeLift.degree F` up to the propositional equation
`Multisegment.universeLift_degree`.

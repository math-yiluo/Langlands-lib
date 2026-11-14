# Pullback and isomorphism transport of fibrewise maximal tori

This derived transport module retains the actual group homomorphisms and
scheme pullbacks used in the Library's `IsFibrewiseMaximalTorus` predicate.

`IsFibrewiseMaximalTorus.iso_comp` transports maximality through an isomorphism
of the source commutative group. It applies the published field-level
`IsMaximalTorus.iso_comp` to each residue fibre and needs no smoothness or
affineness assumption.

For a coordinate split torus, `isClosedSubgroup_coordinateBaseChange` retains
closedness, and `isFibrewiseMaximalTorus_coordinateBaseChange` retains
fibrewise maximality, for the actual pullback homomorphism precomposed with
the inverse canonical split-torus base-change isomorphism. The former uses
arbitrary base change of a closed subgroup and source-isomorphism transport;
the latter assumes the original ambient group smooth and affine. At a
point of the new base, the composite of its residue-field point with the base
morphism is an actual field-valued point of the original base.
`IsFibrewiseMaximalTorus.fieldPoint` gives maximality on that composite fibre;
the published `splitTorus.isMaximalTorus_baseChangedHom_comp` then compares it
with the actual coordinate pullback. Both helpers retain the same finite
coordinate index type. No reductivity or local-ring assumption is needed.

`splitTorus.fibrewiseMaximalBaseChange` packages this actual coordinate
pullback homomorphism with the two proved properties in a subtype. It takes
the original closedness and fibrewise maximality proofs, and assumes the
ambient group smooth and affine. Its underlying homomorphism is exactly the
inverse canonical coordinate isomorphism followed by the pullback of the
original homomorphism.

All results have derived provenance from the named Library pullback,
maximality and closed-subgroup lemmas. They are coherence and transport
helpers for refining an etale splitting neighborhood, and assert neither
existence of such a neighborhood nor finite etale refinement.

Shared declarations `IsFibrewiseMaximalTorus.iso_comp` are imported from `Langlands.GroupScheme.Torus.FibrewiseMaximalTransport`; their mathematical hypotheses, conclusions and data are unchanged.

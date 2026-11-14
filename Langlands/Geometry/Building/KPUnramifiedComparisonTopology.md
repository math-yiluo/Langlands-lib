# Continuity for the unramified comparison on the downstairs centralizer

This internal construction concerns a supplied `ParahoricBuildingData G` over any
nonarchimedean local field `F` in universe `u`. It bundles the actual map from the
rational points of its centralizer to `G(UnramifiedClosure F)` as a continuous
monoid homomorphism. The map is the centralizer inclusion followed by
`rationalExtend`; its application formula is definitional.

The source uses exactly `rationalPointTopology F P.centralizer.Z.X`. The upstairs
field uses `fixedFieldTopology F`, induced by `fixedFieldValued F`, and its group
uses the corresponding `rationalPointTopology`. The ambient group is affine by
the supplied affine structure morphism; the centralizer is affine because its
inclusion is a closed immersion.

The proof composes `continuous_rationalPointMap` for the actual centralizer
inclusion with `unramifiedRationalExtensionContinuousHom` from
`KPZeroTopologyDescent`. The latter proves continuity of the existing scalar
extension map from the continuous field inclusion. Consequently the double comap
of any open upstairs subgroup is open, by the continuous-preimage theorem. This
uses neither a different point topology nor an openness assumption about the
centralizer inside the ambient group.

The content is derived from those Library continuity theorems. It supplies the
topology transport needed by `UnramifiedComparisonOpenFieldStatement`; openness
of the upstairs Moy–Prasad group must still be proved separately.

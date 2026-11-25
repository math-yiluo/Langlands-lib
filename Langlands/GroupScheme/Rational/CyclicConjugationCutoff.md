# Intrinsic cyclic conjugation cutoffs on actual affine groups

Let an actual group scheme over an arbitrary commutative ring have any supplied affine coordinate presentation. `modelGroupIso` packages the proved group compatibility of the affine model as an actual group isomorphism.

`cyclicConjugationAction` is rank-one conjugation on the actual coefficient-point functor, expressed through that model. `cyclicConjugationAction_act` proves its precise formula: a unit acts by conjugation through the supplied cocharacter. The proof uses the existing rank-one formula on the model and the actual group isomorphism back to the original group. No additive compatibility is required of the affine chart.

`cyclicConjugationCutoff` defines the intrinsic cyclic cutoff on the original group, using this action and the positive integral tail at the supplied cutoff. `cyclicConjugationCutoff_one` proves that its first positive cutoff equals the actual dynamic contracting subgroup on every scheme test. It transports the arbitrary-ring first-cut equality through the proved model isomorphism. `cyclicConjugationCutoff_le_unipotent` shows that every later positive cutoff lies in that actual contracting subgroup by inclusion of the corresponding character tails.

There are no field, finite-type, smoothness, or reducedness hypotheses. The construction depends on a supplied affine presentation; independence of its membership follows from the separately available intrinsic-weight presentation comparison once actions are identified. This module does not identify root filtration terms or prove parabolic normality.

Provenance: internal transport of the proved arbitrary-ring first-cut theorem and intrinsic weight construction to actual affine groups in arbitrary coordinate presentations.

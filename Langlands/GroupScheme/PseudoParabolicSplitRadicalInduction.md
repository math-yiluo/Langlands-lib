# Dimension induction through the split ground-field radical

Author: Worker 1478.

This internal construction assembles the split-radical step of rational
lifting over every field `k : Type u`, at arbitrary universe `u`. It is
conditional on the named structural propositions and a residual lifting
case; it is not a proof of the unrestricted main target.

`SplitRadicalQuotientWithSection n` contains an actual smooth connected
affine group quotient of `G` with full scheme kernel `range n`, its actual
projection, and an actual scheme section with the exact right-inverse
equation. The section need not respect the group law. The definition
`SplitRadicalQuotientWithSection.ofStatements` constructs this data from
the existing `NormalSubgroupQuotientStatement` and
`SplitUnipotentAffineTorsorStatement`, for a supplied represented split
ground-field radical in a smooth connected affine ambient group. The
first proposition supplies an actual smooth affine quotient. The existing
split-unipotent quotient-section theorem supplies an actual section.
Scheme surjectivity of the projection descends connectedness from `G`.
Classical choice selects these data; no canonical quotient or section is
claimed, and neither structural proposition is proved here.

`dimension_lt` applies the existing nontrivial connected-kernel theorem to
any such package. When `range n` differs from bottom as a subgroup functor,
the quotient has strictly smaller `Lie.dimension` than `G`. The ambient
source must be affine and locally of finite type; the quotient's smoothness
and affineness are contained in the package. Nontriviality concerns all
relative scheme tests, not just rational or geometric points.

`liftingProperty` uses the package's actual section and the published
rational-lifting reduction to transfer the entire fixed-group property
from the quotient to `G`. It takes the quotient's fixed-group property and,
for every pseudo-parabolic subgroup of `G`, an actual pseudo-parabolic
subgroup in that same quotient with exact full preimage. This exact
preimage equality retains every relative scheme test. Every original
homogeneous quotient scheme `Q` and projection `q` remain the ones under
which rational lifting is concluded.

`PseudoParabolicSplitRadicalInduction.statement_of_trivial_split_radical`
performs strong induction on the finite dimension of the actual dual-number
identity kernel. Its inputs are the existing represented split-radical
existence proposition, the preceding normal-quotient and affine-torsor
propositions, pseudo-parabolic descent for every supplied quotient by a
split radical, and the fixed-group lifting property whenever a represented
split radical has bottom range. For each smooth connected affine group,
choose a radical representative. If its range is bottom, apply the residual
case. Otherwise construct the quotient with section, apply the induction
hypothesis using strict dimension decrease, and transfer the property
back along that actual section. This does not assume or claim that the
split radical of the quotient is trivial. The definitional fixed-group
equivalence converts the resulting all-group property to the exact
published rational-lifting target.

The provenance is internal: this module combines the existing normal-quotient
and affine-torsor interfaces, actual quotient-section construction, strict
Lie-dimension decrease, strong induction and rational-point transfer. Its
conclusion has no field-size, perfectness, reductivity or characteristic
restriction. The displayed structural propositions, exact subgroup descent,
and the residual trivial-split-radical lifting case remain explicit inputs
and must be discharged in a later unconditional proof. No proof of those
inputs or completion of the host task is asserted by this construction.

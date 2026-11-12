# Smoothness descends along cofiltered affine limits

This internal reduction uses the chart-independence theorem in
`SmoothMorphismCharts` and the published scheme theorem
`AffineLimit.relativeSmoothDescent`.

`EtaleMorphismChart.baseChange` constructs the entire base-changed square,
using the actual pulled-back schemes, their induced scheme map and the
restricted chart maps. `schemeBaseChangeArrowIso` reverses the order of the
pullback factors to identify this induced map with the convention used by the
scheme limit theorem. Hence `smooth_baseChange_iff` identifies smoothness of
the base-changed space map with smoothness of that scheme base change, for any
fixed étale square whose source chart is surjective.

`smooth_baseChangeMap_iff_exists_stage_of_chart` proves the limit equivalence
assuming this fixed square has a locally finitely presented, quasi-compact,
quasi-separated scheme map and a quasi-compact target structure map. Restrict
the diagram of affine bases to `Over i` to give it the original stage as its
base. The forgetful functor is initial in a cofiltered category, so the
whiskered cone is still limiting. Apply relative scheme smooth descent and
use the chart test in both directions. The reverse implication also follows
directly from the earlier stage-to-cone transport theorem.

The intermediate theorem retains the fixed chart's finiteness as explicit
hypotheses. The final `spaceLimitSmoothDescent` discharges them using
`exists_affine_finitePresentation_chart_square` from
`FinitePresentationChartSquares`: source and target charts are affine and
locally finitely presented over the affine base. The scheme map is locally
finitely presented because its composite with the locally finite type target
structure map is; its quasi-compactness and quasi-separatedness follow from
affineness. This proves the full smoothness conjunct
`SpaceLimitPropertyDescends (fun f => IsSmoothMorphism f)` under precisely the
published hypotheses. It does not prove the other seven conjuncts or the
full eight-property target.

The constructions and reduction are derived from the cited Library declarations
and their conventions; no outside source is used in this internal unit.

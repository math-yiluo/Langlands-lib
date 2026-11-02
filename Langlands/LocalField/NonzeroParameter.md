# Nonzero parameters near zero

This internal construction supplies a parameter for the contracting-family argument
in dynamic-unipotent compact-open containment. It uses the existing Mathlib
`ValuativeRel` and the given `TopologicalSpace`; `IsValuativeTopology` identifies
that topology with the valuation topology. The field universe is arbitrary.

The hypotheses are a field, a nontrivial valuative relation and its compatible
topology. In particular, Mathlib's `IsNonarchimedeanLocalField` supplies both
`IsValuativeTopology` and `ValuativeRel.IsNontrivial`. Local compactness,
discreteness of the value group and the field characteristic are not needed.

`exists_nonzero_mem_of_mem_nhds_zero` proves that every neighborhood `V` of zero
contains a nonzero element. The implemented proof uses
`IsValuativeTopology.hasBasis_nhds_zero'` to find a nonzero radius `γ` whose open
valuation ball lies in `V`. Nontriviality gives a value `δ` with `0 < δ < 1`.
Surjectivity of the canonical valuation realizes `γ * δ` as the value of an
element `t`. This value is nonzero and strictly below `γ`, so `t` is nonzero and
belongs to `V`.

`nhdsNE_zero_neBot` applies the neighborhood characterization of a nonbottom
restricted neighborhood filter to conclude `(𝓝[≠] (0 : F)).NeBot`.
`nonzeroParameter V hV` selects an actual unit whose underlying field element
belongs to `V`, using the proved existence theorem and `Units.mk0`.
No particular parameter or compatibility between choices is asserted.

The proof route was suggested by Worker 1235 for the parent analytic proof and
implemented here using Mathlib's valuation basis, nontriviality and surjectivity
lemmas. This is an internal prerequisite, with no new literature translation.
It does not construct the dynamic-radical contraction map, prove its continuity
or closedness, or prove compact-open containment.

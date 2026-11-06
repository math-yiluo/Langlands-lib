# Relatively compact fundamental-domain proof

The exact theorem
`Langlands.Global.LeftCosetSpace.relativelyCompactFundamentalDomain`
proves the unchanged published
`RelativelyCompactFundamentalDomainStatement` at arbitrary universe `u`.
It imports the target and its published dependencies by Lean module name.
This focused proof establishes the generic domain-selection and measure
conclusions; actual normalized quotient periods, all-parabolic cuspidal
realization, source smoothness and spectral conclusions remain separate
obligations.

The construction adapts the published first-patch argument in
`Langlands.Global.LeftCosetFundamentalDomain`. Its local private helpers
allow the patches to cover every quotient fiber without covering the
whole source group. For a continuous open map `f` and open patches `U n`
on which `f` is injective, the selected set is the union of
`U n \ f ⁻¹' (⋃ m < n, f '' U m)`. Each piece is measurable because
all the image sets being excluded are open. The least natural-number
index of a patch meeting a fiber gives existence; exclusion of earlier
images and injectivity on that patch give uniqueness.

The exported helper
`exists_measurable_fundamentalDomain_subset_open` starts with an open set
`V` meeting every orbit. The discrete-subgroup quotient is locally
injective, and Lindelöf gives a countable open injective cover `U n`.
The patches `U n ∩ V` still meet every quotient fiber. The preceding
selection therefore lies in `V`, and the free subgroup action converts
uniqueness in a quotient fiber to uniqueness of the subgroup element
carrying a specified point into the selected domain.

For the exact target, local compactness and regularity thicken the
supplied compact orbit cover `K` to an open set `V` with compact closure.
The helper supplies `s ⊆ V`, so the closure of `s` is a closed subset
of the compact closure of `V`. Everywhere uniqueness proves
`IsFundamentalDomain Γ s ν` for every measure `ν`.

For invariant `ν`, the existing
`discreteQuotientMeasure_eq` identifies the actual quotient measure with
the pushforward of `ν.restrict s`; `measurePreserving_mk` supplies the
stated measure-preserving map. Compact finiteness bounds `ν s` by
`ν (closure s) < ∞`. Discreteness in a second-countable group gives
`Countable Γ`, so the Mathlib fundamental-domain positive-mass theorem
applies to every nonzero invariant measure. The existing normalization
and domain-independence theorems then give both the probability law and
equality with the originally chosen domain's normalization.

Worker 116 adapted the existing Library first-patch proof and implemented
the open-set refinement, compact-closure argument and exact measure
conclusions. The original published fundamental-domain construction is
credited to Worker 94; preserve both contributors when adopting this
proof pair. The motivating source and the remaining actual-period
obligations are recorded in the paired target Markdown.

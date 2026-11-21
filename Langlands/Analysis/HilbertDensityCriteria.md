# Elementary generators and Hilbert space density

These are internal analysis lemmas used in the spectral family argument, proved from Mathlib's scalar smooth approximation, `Lp` induction, and orthogonal projection. They do not assume an automorphic Plancherel theorem.

## Elementary generators in `Lp` and finite products

`Langlands.Analysis.topologicalClosure_span_smooth_smul_eq_top` takes a finite-dimensional real normed space with its Borel measurable structure, a measure finite on compact sets, a complex normed target `E`, and `1 ≤ p < ∞`. If `D ⊆ E` has dense complex span, the `Lp E p μ` classes represented almost everywhere by \(x\mapsto c(x)h\), with \(h\in D\) and \(c\) smooth and compactly supported, have dense span.

Let \(C\) be the closed span of those classes. For a fixed \(h\in D\), the continuous linear map induced on `Lp` by \(a\mapsto ah\) carries the scalar smooth approximants to the desired generators. Thus the indicator of any measurable finite-measure set with constant value \(h\) also belongs to \(C\). `indicatorConstLpCLM` bundles the continuous linear dependence of the indicator class on its constant value. The inverse image of \(C\) under this map is a closed submodule containing \(D\), so the same indicator belongs to \(C\) for any constant. `Lp.induction` then uses these indicators, addition and closedness to show \(C=\top\).

`Langlands.Analysis.PiLp.topologicalClosure_span_single_eq_top` passes from a dense spanning set in each factor to the corresponding one-component generators in a finite `PiLp` product. The inverse image of the closed span under each continuous one-component inclusion is the full factor; each element is the finite sum of its one-component inclusions. `Langlands.Analysis.Submodule.topologicalClosure_span_eq_top_of_subset_closure` transfers an ambient closure inclusion to density inside a submodule, by the subtype topology and the map of a span under the inclusion. Its corollary `topologicalClosure_span_subtype_eq_top` applies this to the closed span itself.

## Inner product tests

`Langlands.Analysis.subset_topologicalClosure_span_of_inner_eq` works in a complete complex inner product space. Let \(L\) be a submodule, \(S\subseteq L\), and \(G\) a set with dense span. Suppose for each \(g\in G\) there is an \(s\in\operatorname{span} S\) with \(\langle\Theta,s\rangle=\langle\Theta,g\rangle\) for all \(\Theta\in L\). Then \(L\subseteq \overline{\operatorname{span}S}\). The proof projects \(\Theta\in L\) onto the closed span of \(S\). The difference lies in the closure of \(L\), so the pairing identity still holds for it by continuity. Since the difference is orthogonal to every such \(s\), it is orthogonal to the dense span of \(G\), hence zero. Closedness of \(L\) is not required.

`Langlands.Analysis.inner_map_map_eq_of_dense` upgrades an inner-product identity for a continuous linear map on pairs of generators to the whole space. For each of the two arguments the set where the identity holds is a closed submodule, so containing a dense spanning set suffices, first in one argument and then in the other.

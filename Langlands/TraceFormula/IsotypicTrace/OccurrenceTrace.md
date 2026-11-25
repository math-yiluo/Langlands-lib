# Traces of compressions to closures of local occurrences

Module `Langlands.TraceFormula.IsotypicTrace.OccurrenceTrace`. Internal to the reduction of
`GroupSchemeCuspidalIsotypicTraceFactorizationStatement` to one local occurrence.
Traces are the Library's `operatorTrace` and `IsTraceClass`.

## Results

* `operatorTrace_eq_linearMap_trace`: on a finite-dimensional Hilbert space, `operatorTrace A`
  equals `LinearMap.trace` of `A`. Proof: `operatorTrace_eq_sum_diagonal` in the standard
  orthonormal basis, compared with `LinearMap.trace_eq_matrix_trace` via
  `OrthonormalBasis.repr_apply_apply`.
* `operatorTrace_eq_trace_of_range`. Let `D` be trace class on a Hilbert space, `J : V → M` an
  injective linear map, and `V₀ ≤ V` finite-dimensional. Suppose every value of `D` lies in
  `J V₀` and `D (J v) = J (L v)` for `v ∈ V₀`, where `L` is an endomorphism of `V₀`. Then
  `operatorTrace D = LinearMap.trace L`. Proof: `compression_trace_of_range` reduces to the
  compression to `J V₀`. That compression is conjugate to `L` by
  `Submodule.equivMapOfInjective`, and `LinearMap.trace_conj'` finishes.
* `operatorTrace_eq_mul_tsum`. Let `E = ⨁ W i` be a Hilbert sum (`IsHilbertSum`) and `B` trace
  class. If `operatorTrace (P_{W i} ∘ B ∘ ι_{W i}) = c i * τ` for all `i`, then
  `operatorTrace B = τ * ∑' i, c i`. Proof: `hilbertSum_trace_hasSum` gives
  `HasSum (fun i => c i * τ) (tr B)`. If `τ = 0` both sides vanish. Otherwise divide by `τ` and
  obtain `HasSum c (tr B / τ)`. Mathlib's `tsum` is zero for a non-summable family, which is
  harmless here.
* `starProjection_closureRange_commute`: the projection onto the closure of the range of an
  occurrence commutes with the local action when the action preserves inner products.
* `operatorTrace_compression_occurrence`. Let `ρ` be admissible, `j` an injective occurrence with
  closure `W` of its range, `K` an open subgroup, and `B` trace class with all values fixed by
  `K`. Let `L` be an endomorphism of `V` with values in the `K`-fixed vectors, and suppose
  `P_W (B (j v)) = j (L v)` for all `v`. Then the trace of the compression of `B` to `W` is the
  trace of `L` on the `K`-fixed vectors (`FiniteRankEnd.onSubspace`). Values of the compression
  are `K`-fixed vectors of `W`, hence images of `K`-fixed vectors of `V`
  (`exists_fixed_preimage_of_mem_closure`). The result then follows from
  `operatorTrace_eq_trace_of_range`.

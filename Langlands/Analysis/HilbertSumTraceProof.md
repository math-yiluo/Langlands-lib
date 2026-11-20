# Traces along closed subspaces and Hilbert sums: proof

Module `Langlands.Analysis.HilbertSumTraceProof` proves the Library statement
`Langlands.Analysis.OperatorIdeals.HilbertSumTraceStatement` as the theorem

```lean
theorem hilbertSumTrace : HilbertSumTraceStatement.{u, v}
```

in namespace `Langlands.Analysis.OperatorIdeals`. Both universe parameters stay free. The
statement and its Markdown are unchanged. No hypotheses are added, and only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` are used.

## Notation

`E` is a complex Hilbert space: `NormedAddCommGroup`, `InnerProductSpace ℂ E` and
`CompleteSpace E`. `⟪x, y⟫` is Mathlib's `inner ℂ x y`. It is conjugate linear in `x` and
linear in `y`. For a submodule `W` with `[CompleteSpace W]`, `ι_W = W.subtypeL : W →L[ℂ] E` is
the inclusion and `P_W = W.orthogonalProjectionOnto : E →L[ℂ] W` is the orthogonal projection.
The compression of `B` to `W` is `P_W ∘L B ∘L ι_W`, written `P_W B ι_W`. `tr` is the Library's
`operatorTrace`. It is the diagonal sum in one chosen Hilbert basis.

## Library results used

All are imported by name through `Langlands.Analysis.OperatorTraceProof`.

- `operatorTraceCyclicity : OperatorTraceCyclicityStatement.{u, v}` (bounded rectangular
  cyclicity). For trace-class `A : E →L[ℂ] E`, `B : E →L[ℂ] F` and `C : F →L[ℂ] E`, both
  `(B ∘ A) ∘ C` and `A ∘ (C ∘ B)` are trace class, and they have the same `operatorTrace`.
- `operatorTraceBasis : OperatorTraceBasisStatement.{u, w}` (the basis formula). For trace-class
  `A` and any Hilbert basis `b`, the norms `‖⟪b k, A (b k)⟫‖` are summable and
  `operatorTrace A = traceIn b A = ∑' k, ⟪b k, A (b k)⟫`.
- `operatorTrace_zero`, which says that the zero operator has trace zero.

The proof does not use `traceClassIdeal`. The trace-class property of compressions comes from
the first conclusion of `operatorTraceCyclicity`.

## Lemmas in the module

### `isTraceClass_compression`

If `B` is trace class and `W` is complete, then `P_W B ι_W` is trace class. This is the first
conclusion of `operatorTraceCyclicity` with `F = W`, `A = B`, outer factors `P_W` and `ι_W`.
That conclusion is stated for `(P_W ∘ B) ∘ ι_W`, and `ContinuousLinearMap.comp_assoc` rewrites it
to `P_W ∘ (B ∘ ι_W)`.

### `compression_trace_of_range` (Part 1)

Let `S` be complete with `B x ∈ S` for all `x`. Trace-class membership is
`isTraceClass_compression`. For the trace there are two cyclicity steps.

1. `operatorTraceCyclicity` with `F = S`, `A = B` and outer factors `P_S` and `ι_S` gives
   `tr ((P_S B) ι_S) = tr (B (ι_S P_S))`.
2. Put `Q = ι_S ∘ P_S : E →L[ℂ] E`. Then `Q B = B`, because `B x ∈ S` and the projection fixes
   elements of `S` (`Submodule.orthogonalProjectionOnto_mem_subspace_eq_self`).
   `operatorTraceCyclicity` with `F = E`, `A = B`, outer factors `Q` and the identity gives
   `tr ((Q B) id) = tr (B (id Q))`. After removing the identities and rewriting `Q B = B`, this
   reads `tr B = tr (B Q)`.

Reassociating and combining the two equalities gives `tr (P_S B ι_S) = tr B`.

### `inner_compression_apply` and `hasSum_inner_compression`

For `x ∈ W` we have `⟪x, P_W (B x)⟫ = ⟪x, B x⟫`, by `simp` using Mathlib's inner product
lemmas for the orthogonal projection. Completeness of `E` is not needed here.

Let `b` be a Hilbert basis of `W` with any index type `κ : Type w`.
`operatorTraceBasis` on the Hilbert space `W`, applied to the trace-class compression, gives two
facts:

- the norms `‖⟪b k, B (b k)⟫‖` are summable;
- `tr (P_W B ι_W) = ∑' k, ⟪b k, B (b k)⟫`, after rewriting each diagonal term with
  `inner_compression_apply`.

Absolute summability in `ℂ` (`Summable.of_norm`) then gives
`HasSum (fun k => ⟪b k, B (b k)⟫) (tr (P_W B ι_W))`.

### `orthogonal_span_sigma_eq_bot`

Let `E` be the Hilbert sum of the complete subspaces `W i` (`IsHilbertSum`), and let `b i` be a
Hilbert basis of `W i` indexed by `κ i`. Then the orthogonal complement of the span of all the
vectors `b i k`, viewed in `E`, is `⊥`. Suppose `x` is orthogonal to every `b i k`.

- For each `i`, the functional `y ↦ ⟪x, y⟫` on `W i` is continuous. Its kernel is closed and
  contains the span of `b i`. That span is dense (`HilbertBasis.dense_span`), so `x` is
  orthogonal to all of `W i`.
- The Hilbert sum expands `x` as the unconditional sum of its components in the `W i`
  (`IsHilbertSum.hasSum_linearIsometryEquiv_symm` applied to `hW.linearIsometryEquiv x`).
  Applying the continuous functional `innerSL ℂ x` to this sum gives `⟪x, x⟫ = ∑ 0 = 0`.
  Hence `x = 0`.

### `hilbertSum_trace_hasSum` (Part 2 without the fixed-point clause)

Choose a Hilbert basis `b i` of each `W i` (`exists_hilbertBasis`, index type a subset `s i` of
`W i`). Put `e ⟨i, k⟩ = b i k` in `E`, indexed by `Σ i, s i`.

- `e` is orthonormal by `OrthogonalFamily.orthonormal_sigma_orthonormal`, applied to the
  orthogonal family `hW.OrthogonalFamily` and the orthonormality of each `b i`.
- With `orthogonal_span_sigma_eq_bot`, `HilbertBasis.mkOfOrthogonalEqBot` turns `e` into a
  Hilbert basis `bE` of `E`, and `HilbertBasis.coe_mkOfOrthogonalEqBot` gives `⇑bE = e`.
- `operatorTraceBasis` for `B` in `bE` gives summability of the norms `‖⟪e a, B (e a)⟫‖` over
  `Σ i, s i`. It also gives `HasSum (fun a => ⟪e a, B (e a)⟫) (tr B)`.
- For each `i`, `hasSum_inner_compression` gives
  `HasSum (fun k => ⟪b i k, B (b i k)⟫) (tr (P_{W i} B ι_{W i}))`.
  `HasSum.sigma` groups the sum over `Σ i, s i` by `i` and gives
  `HasSum (fun i => tr (P_{W i} B ι_{W i})) (tr B)`.
- For summability of the norms, `‖tr (P_{W i} B ι_{W i})‖ ≤ ∑' k, ‖⟪b i k, B (b i k)⟫‖`
  (`norm_tsum_le_tsum_norm`). The right side is summable in `i` because the nonnegative sigma
  family of norms is summable (`Summable.sigma`). `Summable.of_nonneg_of_le` concludes.

### `compression_eq_zero_of_ne`

Suppose `B` maps each `W i` into `W (τ i)` and `τ i ≠ i`. For `x ∈ W i`, `B x` lies in
`W (τ i)`. The subspace `W (τ i)` is orthogonal to `W i` (`OrthogonalFamily.isOrtho`, through
`Submodule.isOrtho_iff_le`), so `B x ∈ (W i)ᗮ`. Hence `P_{W i} (B x) = 0`
(`Submodule.orthogonalProjectionOnto_eq_zero_iff`), and the compression is the zero operator.

### `hilbertSumTrace`

Part 1 is `compression_trace_of_range`. In Part 2, trace-class membership of every compression
is `isTraceClass_compression`. Summability and `HasSum` come from `hilbertSum_trace_hasSum`. For
the fixed-point clause, `compression_eq_zero_of_ne` and `operatorTrace_zero` show that the family
`i ↦ tr (P_{W i} B ι_{W i})` has support inside `{i | τ i = i}`.
`hasSum_subtype_iff_of_support_subset` then transfers the `HasSum` over `ι` to the subtype
`{i // τ i = i}`.

## Scope

The proof works for arbitrary complete complex inner-product spaces and arbitrary index types.
It uses neither separability nor countability of the Hilbert bases. All sums are Mathlib's
unconditional `HasSum` and `Summable`. Part 2 groups the absolutely summable diagonal of `B` in
the combined Hilbert basis. It needs neither a spectral theorem nor any property of the
compressions beyond their basis formulas.

## Relation to the sources

This is an internal derivation from the Library's trace laws, not a proof transcribed from the
literature. The sources listed in the contract enter as follows.

- Getz–Hahn, *An Introduction to Automorphic Representations* (2024), Definition 9.1.1 and the
  paragraph after it (printed pp. 240–241). These define the trace of a trace-class operator as
  the diagonal sum in an orthonormal basis and state that it does not depend on the basis
  (Exercise 9.1). In the Library this is `operatorTrace` together with `operatorTraceBasis`. The
  proof uses the basis formula twice: on `E` in the combined basis, and on each summand.
  Getz–Hahn assume separable Hilbert spaces. The Library and this proof do not.
- Getz–Hahn, Corollary 9.1.3 (printed p. 241), decomposes `L²_cusp([G])` as a Hilbert direct sum
  of irreducible summands. Part 2 is the abstract Hilbert-space step that splits the trace of a
  trace-class operator along such a decomposition. This module proves nothing about automorphic
  representations.
- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
  nulle* (2011), II.6.6 (printed pp. 122–123). The spectral side of their comparison of the
  twisted and untwisted trace formulas is a sum of `tr (Π(φ) ∘ A_Π)` over the `σ`-stable
  cuspidal automorphic representations `Π`. The fixed-point clause is the abstract version of
  restricting that sum to `σ`-stable summands. An operator that maps each summand `W i` into
  `W (τ i)` has trace equal to the sum over the `τ`-fixed summands. Identifying the compressions
  with the operators `Π(φ) ∘ A_Π` is not part of this module.

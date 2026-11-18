# Traces along closed subspaces and Hilbert sums

Module `Langlands.Analysis.HilbertSumTraceStatement` defines the proposition
`Langlands.Analysis.OperatorIdeals.HilbertSumTraceStatement.{u, v}`. It describes the trace of
a trace-class operator on a complex Hilbert space in terms of its compression to a subspace
containing its range, or its compressions to the summands of a Hilbert sum.

## Notation from the Library and Mathlib

- `IsTraceClass B` (module `Langlands.Analysis.OperatorIdeals`) asks for a Hilbert basis `b` of
  `E` indexed by a subset of `E` in which the real parts of `⟪b i, M (b i)⟫` are summable.
  Here `M = sqrt(B B*)` is the Library's `leftModulus B`.
- `operatorTrace B` (module `Langlands.Analysis.OperatorTrace`) is the diagonal sum
  `∑' i, ⟪b i, B (b i)⟫` in one chosen Hilbert basis `b` of `E`. For a trace-class operator,
  `operatorTraceBasis` gives the same sum in every Hilbert basis and proves absolute
  summability of the diagonal terms.
- For a submodule `W` of `E`, `[CompleteSpace W]` expresses completeness in the induced norm,
  equivalently closedness in `E`. Mathlib supplies the continuous linear inclusion
  `W.subtypeL : W →L[ℂ] E` and orthogonal projection
  `W.orthogonalProjectionOnto : E →L[ℂ] W`. The compression of `B` to `W` is
  `W.orthogonalProjectionOnto ∘L B ∘L W.subtypeL : W →L[ℂ] W`, written `P_W B ι_W` below.
- `IsHilbertSum ℂ (fun i => W i) (fun i => (W i).subtypeₗᵢ)` says that the linear isometric
  inclusions `(W i).subtypeₗᵢ` are an orthogonal family and that the induced isometry from the
  external Hilbert sum to `E` is surjective. Thus the `W i` are pairwise orthogonal and their
  span is dense in `E`.

## Statement

`HilbertSumTraceStatement.{u, v}` is the conjunction of two parts.

1. Let `E : Type u` be a complex Hilbert space, `S` a submodule of `E` with
   `[CompleteSpace S]`, and `B : E →L[ℂ] E` a trace-class operator with `B x ∈ S` for every
   `x : E`. Then the compression `P_S B ι_S` is trace class and
   `operatorTrace (P_S B ι_S) = operatorTrace B`.
2. Let `E : Type u` be a complex Hilbert space, `ι : Type v` an arbitrary index type, and
   `W : ι → Submodule ℂ E` a family with `[∀ i, CompleteSpace (W i)]` such that `E` is the
   Hilbert sum of the `W i`. For each trace-class `B : E →L[ℂ] E` the following hold.

   - Every compression `P_{W i} B ι_{W i}` is trace class.
   - The family `i ↦ ‖operatorTrace (P_{W i} B ι_{W i})‖` is summable.
   - The traces sum to the ambient trace in
     `HasSum (fun i => operatorTrace (P_{W i} B ι_{W i})) (operatorTrace B)`.
   - For every map `τ : ι → ι` with `B x ∈ W (τ i)` for all `i` and all `x ∈ W i`, the
     traces of the compressions indexed by the fixed points of `τ` have the same sum,
     `HasSum (fun i : {i // τ i = i} => operatorTrace (P_{W i} B ι_{W i})) (operatorTrace B)`.

Mathlib's `HasSum` and `Summable` use unconditional sums over arbitrary index types, with
finite subsets ordered by inclusion.

## Proof sketch

The Library's `traceClassIdeal` gives trace-class membership of `P_S B ι_S` because the two
outer factors are bounded. Rectangular cyclicity (`operatorTraceCyclicity`) gives
`tr (P_S B ι_S) = tr (B Q)`, where `Q = ι_S P_S` is the orthogonal projection acting on `E`.
Cyclicity on `E` gives `tr (B Q) = tr (Q B) = tr B`, since the range assumption gives `Q B = B`.

Each compression to a summand is trace class by the same ideal property. Choose a Hilbert
basis `b_i` of each `W i` with index type `κ_i`. Pairwise orthogonality and density of the
span make their inclusions a Hilbert basis of `E`, indexed by `Σ i, κ_i`. The basis formula
for `B` gives an absolutely summable family of diagonal terms with sum `tr B`. In the group
of terms indexed by `i`, projecting `B (b_i j)` to `W i` preserves its inner product with
`b_i j`. The sum in this group is therefore the trace of the compression to `W i` by the same
basis formula. Its norm is bounded by the sum of the norms of its diagonal terms. Grouping the
absolutely summable family gives both summability of the norms of the resulting traces and
`HasSum` with sum `tr B`.

In the twisted form, if `τ i ≠ i`, then `B x ∈ W (τ i)` is orthogonal to `W i` for every
`x ∈ W i`. The compression to `W i` is zero and has trace zero. Removing those zero terms
preserves the sum, which yields the `HasSum` over the fixed-point subtype.

## Use and provenance

This proposition is derived from elementary operator theory for the Library's `operatorTrace`.
Getz–Hahn, *An Introduction to Automorphic Representations* (2024), define the Hilbert-basis
trace in Definition 9.1.1 and the following paragraph (printed pp. 240–241). Corollary 9.1.3
(printed p. 241) gives the Hilbert sum decomposition of `L²_cusp([G])` into irreducibles with
finite multiplicities. Equation (16.10) (printed p. 422) gives the sum
`∑_π m(π) tr π(f)`. Part 2 supplies the operator-theoretic passage from the trace of
`R_cusp(f)` to the traces on the irreducible summands, before grouping isomorphic summands.

Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
nulle* (2011), II.6.4 (printed p. 120) describe the action of `I_σ` on the irreducible cuspidal
summands. In II.6.6 (printed p. 123), the spectral side of their twisted comparison sums
`tr (Π(φ) ∘ A_Π)` over the `σ`-stable cuspidal representations. The fixed-point clause
captures the passage from the trace of `R(φ) ∘ I_σ` to the sum over those summands.

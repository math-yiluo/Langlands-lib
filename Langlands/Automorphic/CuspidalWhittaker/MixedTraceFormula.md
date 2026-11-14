# The trace on the mixed space in coordinates

Module `Langlands.Automorphic.CuspidalWhittaker.MixedTraceFormula`, namespace
`Langlands.Automorphic.CuspidalWhittaker`. Worker 174 wrote it for the proof of
`Langlands.Automorphic.CuspidalArchimedeanWhittakerFunctionalStatement` (Task 5996,
`e3f48d66-76bc-4321-a8ea-e25681c89d3f`, published under Task 5720).

Let `K` be a number field with `r₁` real and `r₂` complex places. The Library's
`mixedTrace K` (module `CuspidalWhittaker.AdelicCharacter`) is the `ℝ`-linear map on the
mixed space `ℝ^{r₁} × ℂ^{r₂}` defined on the lattice basis by the trace `Tr_{K/ℚ}`. The
standard additive character at the infinite places is `x ↦ exp(2π i · mixedTrace x)`. This
module writes `mixedTrace` in coordinates.

## Definition

`coordinateTrace K : mixedSpace K →ₗ[ℝ] ℝ` sends `x = (x_real, x_complex)` to
`∑_{v real} x_v + ∑_{w complex} 2 Re x_w` (`coordinateTrace_apply`). Provenance: internal; it
is the classical formula `Tr_{K/ℚ} = ∑_v [K_v : ℝ] Re ∘ σ_v` written on the mixed space.

## Results

- `trace_eq_sum_mult_re`: for `x ∈ K`, `Tr_{K/ℚ}(x) = ∑_w mult(w) · Re(w.embedding x)`, where
  `w` runs over the infinite places and `mult w` is `1` for real and `2` for complex `w`.
  Proof: Mathlib's `trace_eq_sum_embeddings` writes the trace as the sum of `σ x` over the
  complex embeddings `σ`. Group the embeddings by their place (`InfinitePlace.mk`). The
  embeddings of the place `w` are `w.embedding` and its conjugate, which have the same real
  part, and there are `mult w` of them (`card_filter_mk_eq`).
- `coordinateTrace_mixedEmbedding`: `coordinateTrace K (mixedEmbedding K x) = Tr_{K/ℚ}(x)`.
  Split the sum of the previous lemma into real and complex places
  (`Fintype.sum_subtype_add_sum_subtype`). At a real place the coordinate is the real
  embedding, and at a complex place it is `w.embedding x` with multiplicity `2`.
- `mixedTrace_eq_coordinateTrace`: `mixedTrace K = coordinateTrace K`. Both are `ℝ`-linear and
  agree on the lattice basis, which consists of mixed embeddings of an integral basis
  (`Basis.ext`, `Basis.constr_basis`, `latticeBasis_apply`).
- `mixedTrace_apply`: `mixedTrace K x = ∑_{v real} x_v + ∑_{w complex} 2 Re x_w`.
- `mixedTrace_single_real`: `mixedTrace K (Pi.single v s, 0) = s` for a real place `v`.
- `mixedTrace_single_complex`: `mixedTrace K (0, Pi.single v z) = 2 Re z` for a complex
  place `v`. Only the `v` term of the complex sum is nonzero (`Finset.sum_eq_single`).

The module uses `open scoped Classical` for the decidable equality of places in
`Pi.single`, as Mathlib's mixed space does.

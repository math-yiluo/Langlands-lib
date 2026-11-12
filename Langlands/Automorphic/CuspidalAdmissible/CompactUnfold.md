# Square integrals over compact sets

Module: `Langlands.Automorphic.CuspidalAdmissible.CompactUnfold`. Provenance: internal.

`exists_lintegral_compact_le S hn χ hχ hSχ hKc`: let `S` be a realization of positive rank with
unitary central character `χ` and `Kc ⊆ GL_n(𝔸)` compact. There is a finite constant `C` with

`∫_Kc |f|² d(matrixHaarMeasure) ≤ C · ∫_band |f|² d(quotientHaarMeasure)`

for every realized vector `f` (the band integral is `bandNorm S f`).

Proof: if `Kc` is empty take `C = 0`. Otherwise the determinant norm is continuous and
positive, so on `Kc` it lies in a closed interval `[m, M]` with `m > 0` (extreme values on a
compact set). For each `x`, `#{γ : γ x ∈ Kc}` is at most the number `Mk` of rational `γ` with
`γ Kc ∩ Kc ≠ ∅` (`encard_rational_mul_mem_le`), which is finite (`finite_rational_compact`).
The unfolding inequality `lintegral_le_mul_quotient` bounds the integral by `Mk` times the
quotient integral over `{m ≤ |det| ≤ M}`, and `exists_lintegral_closedBand_le` (module
`BandShift`) bounds that by `N` times the band integral; `C = Mk · N`.

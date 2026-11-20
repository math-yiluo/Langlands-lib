# Bounded operators from inner-product-preserving relations

Module `Langlands.Analysis.InnerProductGraphExtension` proves an elementary
Hilbert-space lemma used to construct the operators `M(w, λ) : H_P → H_{P'}`
on the imaginary axis from their unitarity on Lapid's `A^2_P`.

## Provenance

This is a standard functional-analytic fact, internal to the Library (no
literature citation): an isometric linear relation extends by continuity to the
closure of its domain and is then composed with the orthogonal projection onto
that closure. Arthur (2005, §7, p.34–35) uses it implicitly when he extends the
unitary operators `M(s, λ)` from the dense subspace `H_P^0` to `H_P`.

## Declarations

Let `H`, `H'` be complex inner product spaces.

- `inner_snd_eq_inner_fst_of_mem_span`: if a set `S ⊆ H × H'` satisfies
  `⟪s.2, t.2⟫ = ⟪s.1, t.1⟫` for all `s, t ∈ S`, then the same identity holds
  for all `γ, γ'` in the complex linear span of `S`. The proof is induction on
  the span in each variable, using sesquilinearity of the inner product.

- `exists_continuousLinearMap_of_inner_eq`: if moreover `H` and `H'` are
  complete, there is a continuous linear operator `T : H →L[ℂ] H'` with
  `T s.1 = s.2` for every `s ∈ S`.

## Proof of `exists_continuousLinearMap_of_inner_eq`

Let `Γ` be the span of `S` and `D ⊆ H` the closure of its image under the
first projection; `D` is closed, hence complete. The maps `e : Γ → D`,
`γ ↦ γ.1`, and `f : Γ → H'`, `γ ↦ γ.2`, are linear, and by the first lemma
(applied with `γ = γ'`) `‖f γ‖ = ‖e γ‖`. The range of `e` is dense in `D`:
its image in `H` is the first projection of `Γ`, whose closure is `D`.
Mathlib's `LinearMap.extendOfIsometry` gives a linear isometry `T₀ : D → H'`
with `T₀ (e γ) = f γ`. Then `T = T₀ ∘ proj_D`, where `proj_D` is the
orthogonal projection onto `D`, works: for `s ∈ S`, `s.1 ∈ D`, so
`proj_D s.1 = e s` and `T s.1 = f s = s.2`.

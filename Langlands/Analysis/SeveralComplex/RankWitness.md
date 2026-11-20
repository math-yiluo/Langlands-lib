# A holomorphic determinant witnessing the generic span of a holomorphic family

Module `Langlands.Analysis.SeveralComplex.RankWitness`, namespace
`Langlands.Analysis.SeveralComplex`.

`E` is a complex normed space, `F` a finite-dimensional complex normed space and `Λ` an arbitrary
index type.

## Results

- `differentiableOn_finset_prod_apply`: a finite product `z ↦ ∏_{i ∈ s} f i z` of functions
  `E → ℂ` that are complex differentiable on `U` is complex differentiable on `U`.
- `exists_det_witness` (**determinant witness for the generic span**). Let `U ⊆ E` be nonempty
  and `a : Λ → E → F` a family of maps that are complex differentiable on `U`. Then there exist
  `z₁ ∈ U`, a finite set `s₁ : Finset Λ` and `h : E → ℂ` complex differentiable on `U` with
  `h z₁ ≠ 0`, such that for every `z ∈ U` with `h z ≠ 0` and every `l : Λ`, the vector `a l z`
  lies in the span of `{a μ z | μ ∈ s₁}`.

No openness or connectedness of `U` is needed.

## Proof

- The product lemma is by induction on the finset.
- Witness: let `rk z` be the dimension of the span of all `a l z`. It is at most `finrank ℂ F`,
  so it attains its maximum on `U` at some `z₁` (`Nat.sSup_mem`). By
  `exists_linearIndependent'` there are an index type `κ` and an injective `ι : κ → Λ` such that
  the vectors `a (ι i) z₁` are linearly independent and span the same space `W₁` as all
  `a l z₁`. Then `κ` is finite (`LinearIndependent.finite`), and `s₁` is the image of `ι`. The
  coordinate functionals of the basis `Basis.span` of `W₁` extend to linear forms
  `φ_μ : F → ℂ` (`LinearMap.exists_extend`) with `φ_μ (a (ι l) z₁) = δ_{μ l}`.
  Put `h z = det (φ_μ (a (ι l) z))_{μ, l ∈ κ}`.
  - `h` is holomorphic: by `Matrix.det_apply'` it is a signed sum of products of the entries,
    and the entries are holomorphic (each `φ_μ` is a continuous linear form, since `F` is
    finite-dimensional).
  - `h z₁ = det 1 = 1`.
  - If `h z ≠ 0`, the columns of the matrix are linearly independent
    (`Matrix.linearIndependent_cols_of_det_ne_zero`). The columns are the images of the
    `a (ι l) z` under the linear map `y ↦ (φ_μ y)_μ`, so the `a (ι l) z` are linearly
    independent (`LinearIndependent.of_comp`). Their span therefore has dimension
    `card κ = rk z₁ ≥ rk z`. It is contained in the span of all `a l z`, so the two spans are
    equal (`Submodule.eq_of_le_of_finrank_le`).

## Provenance

Internal. Standard linear algebra (maximal rank is attained on the set where a minor does not
vanish), written as a supporting lemma for the proof of
`Langlands.Analysis.Meromorphic.MeromorphicContinuationAnalyticComplementStatement`
(Bernstein–Lapid, Theorem 3.3). There it is the first step of the induction in module
`PointwiseSpan`.

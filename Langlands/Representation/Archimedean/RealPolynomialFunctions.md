# Real polynomial functions on `ℂ^ι`

For a finite type `ι`, functions `(ι → ℂ) → ℂ` that are polynomials in the real coordinates
`v_k` and `conj (v_k)`, with a degree filtration and its calculus.

## Definitions

- `coord ι c v`: the coordinate `v k` for `c = (k, false)` and `conj (v k)` for `c = (k, true)`.
- `mono ι α`: the monomial `∏_c coord_c^{α c}`.
- `degLE ι d`: the complex span of the monomials of total degree `∑ α c ≤ d`.
- `DerivDeg d f`: `f` is real differentiable and its derivative along every vector field all of
  whose coordinates lie in `degLE ι e` lies in `degLE ι (d + e)`.
- `swapEquiv`: the involution of `ι × Bool` exchanging the two coordinates of each `k`.

## Results

- `degLE_mono`, `one_mem_degLE`, `const_mem_degLE`, `coord_mem_degLE`, `mono_mul`.
- `mul_mem_degLE`: degrees add under products; `pow_mem_degLE`, `prod_mem_degLE`.
- `finrank_degLE_le`: `finrank (degLE ι d) ≤ (d + 1)^{|ι × Bool|}`; `degLE_finiteDimensional`.
- `derivDeg_of_mem`, `fderiv_apply_mem_degLE`: if `f ∈ degLE ι d` and every coordinate of `W`
  lies in `degLE ι e`, then `v ↦ Df(v)[W v]` lies in `degLE ι (d + e)` (proved for monomials by
  the product rule, `DerivDeg.mul`, and extended by linearity).
- `conj_mem_degLE`: `degLE` is stable under complex conjugation of values (via `swapEquiv`).
- `comp_mem_degLE`: if every coordinate of `W : (ι' → ℂ) → (ι → ℂ)` has degree `≤ e`, then
  `P ∘ W` has degree `≤ d e` for `P` of degree `≤ d`; `coord_comp_mem_degLE` reduces the
  hypothesis to the holomorphic coordinates `v ↦ W v k`.

## Provenance

Internal infrastructure of Task 7064 for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.

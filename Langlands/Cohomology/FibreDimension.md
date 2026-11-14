# Fibre dimensions of modules and of base-changed complexes

Authors: Worker 5705.

The module `Langlands.Cohomology.FibreDimension` (namespace
`Langlands.Cohomology.FibreDimension`) is the commutative-algebra half of the proof of
`ProperFlatFibreCohomologySemicontinuityStatement` (module
`Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityProof`). It shows how
the dimensions of the homology of `K ⊗_R k` vary with a ring map `R → k` to a field, for a bounded
complex `K` of finite projective `R`-modules. This is the algebra in D. Mumford, *Abelian
Varieties*, Chapter II, §5, proof of the Corollary on p.50 (literature id
`mumford-abelian-varieties-chapter-ii-scan`). The module contains helper lemmas only; it adds no
statement to the Library.

## Fibre dimensions of modules

- `fibreDim M p` is `dim_{κ(p)} κ(p) ⊗_R M` for a prime `p` of `R` (Mathlib's
  `Ideal.ResidueField`).
- `isOpen_setOf_fibreDim_le`: for a finite module `M`, `{p | fibreDim M p ≤ d}` is open. Choose
  `x_1, …, x_r` in `M` whose images form a basis of `κ(p) ⊗ M`, and let `N` be their span. Then
  `κ(p) ⊗ (M ⧸ N) = 0`, so `p` lies outside the closed support of `M ⧸ N`. At every prime `q`
  outside that support, the images of the `x_i` span `κ(q) ⊗ M` (right exactness of the tensor
  product), so `fibreDim M q ≤ r`.
- `kerPrime φ` is the prime `ker φ` of a ring map `φ : R → k` to a field.
  `finrank_tensor_eq_fibreDim` (and `finrank_tensor_eq_fibreDim'` for an `R`-algebra `k`):
  `dim_k k ⊗_R M = fibreDim M (ker φ)`. The map `φ` factors through `κ(ker φ)`
  (`Ideal.ResidueField.lift`), and dimensions are invariant under field extension
  (`AlgebraTensorModule.cancelBaseChange`, `Module.finrank_baseChange`).
- `isLocallyConstant_fibreDim`: for `M` finite projective, `fibreDim M` is Mathlib's
  `Module.rankAtStalk`, which is locally constant.
- `finrank_range_baseChange_add`: for a linear map `d : M → N` with `N` finite,
  `rk(d ⊗ k) + fibreDim(N ⧸ im d)(ker φ) = dim_k (k ⊗ N)`. Base change keeps
  `M → N → N ⧸ im d → 0` exact (`lTensor_exact`), so the cokernel of `d ⊗ k` is
  `k ⊗ (N ⧸ im d)`.

## Complexes of vector spaces

For a cochain complex `C` of `k`-vector spaces indexed by `ℤ`, `rankD C i j` is the rank of the
differential `C.d i j`.

- `finrank_homology_add`: for a short complex `S` of vector spaces with `S.X₂` finite-dimensional,
  `dim H(S) + rk f + rk g = dim S.X₂` (via Mathlib's `ShortComplex.moduleCatHomologyIso`).
- `finrank_homology_add_rankD`: `dim Hⁿ(C) + rk d^{n-1} + rk dⁿ = dim Cⁿ`, by the previous lemma
  for `C.sc' (n - 1) n (n + 1)` and `HomologicalComplex.homologyIsoSc'`.
- `sum_negOnePow_finrank_homology`: if every `Cⁿ` is finite-dimensional and `C` vanishes in the
  degrees `a - 1` and `a + N`, then
  `∑_{i < N} (-1)ⁱ dim H^{a+i}(C) = ∑_{i < N} (-1)ⁱ dim C^{a+i}`. The rank terms telescope
  (`sum_range_negOnePow_mul_add`). The boundary ranks vanish because the source of `d^{a-1}` and
  the target of `d^{a+N-1}` are zero.

## Base change of a complex of finite modules

Let `K` be a cochain complex of `R`-modules indexed by `ℤ` and `φ : R →+* k` a ring map to a
field. `ModuleComplex.baseChange φ` is the Library's degreewise extension of scalars, so the
terms of `K ⊗_R k` are `k ⊗_R Kⁿ` and the differentials are base changes of those of `K`. Put
`P = ker φ`.

- `finrank_baseChange_X`: `dim_k (k ⊗ Kⁿ) = fibreDim Kⁿ P`.
- `rankD_baseChange_add`: `rk(d ⊗ k) + fibreDim(K^j ⧸ im d)(P) = fibreDim K^j P` for
  `d = K.d i j`.
- **Dimension formula** (`finrank_homology_baseChange`, `finrank_homology_baseChange_eq`): if
  every term of `K` is finite, then `dim_k Hⁿ(K ⊗_R k) = homologyDim K n P`, where
  `homologyDim K n p = c_{n-1}(p) + c_n(p) - e_{n+1}(p)` (in `ℤ`), with `c_m` the fibre dimension
  of the cokernel `K^{m+1} ⧸ im dᵐ` and `e_m` that of `Kᵐ`. This combines
  `finrank_homology_add_rankD` for `K ⊗ k` with `rankD_baseChange_add` for `d^{n-1}` and `dⁿ`.
- **Upper semicontinuity** (`isOpen_setOf_homologyDim_lt`): if the terms of `K` are finite and
  `K^{n+1}` is projective, then `{p | homologyDim K n p < r}` is open. Near a point `p₀`, the
  cokernel dimensions `c_{n-1}`, `c_n` are at most their values at `p₀`
  (`isOpen_setOf_fibreDim_le`) and `e_{n+1}` is constant (`isLocallyConstant_fibreDim`).
- **Euler characteristic.** `isLocallyConstant_sum_fibreDim`: for `K` with finite projective
  terms, `p ↦ ∑_{i < N} (-1)ⁱ fibreDim K^{a+i} p` is locally constant (finite sums of locally
  constant functions are locally constant, `isLocallyConstant_finsetSum`).
  `sum_negOnePow_finrank_homology_baseChange`: if `K` vanishes in degrees `a - 1` and `a + N`, then
  `∑_{i < N} (-1)ⁱ dim_k H^{a+i}(K ⊗ k) = ∑_{i < N} (-1)ⁱ fibreDim K^{a+i} P`
  (`sum_negOnePow_finrank_homology` for `K ⊗ k`).

All lemmas are proved in full; the module uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

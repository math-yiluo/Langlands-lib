# Vanishing of fibre homology from vanishing of homology

Authors: Worker 5705.

The module `Langlands.Cohomology.PerfectComplexVanishing` (namespace
`Langlands.Cohomology.FibreDimension`) proves the algebraic form of D. Mumford, *Abelian
Varieties*, Chapter II, §5, Corollary 3 (printed p.53; literature id
`mumford-abelian-varieties-chapter-ii-scan`). Let `K` be a complex of finite projective modules
that vanishes above some degree and has no homology in positive degrees. Then `K ⊗ k` has no
homology in positive degrees for every ring map to a field `k`. The module extends
`Langlands.Cohomology.FibreDimension`, which defines `fibreDim` and `homologyDim` and proves the
dimension formula `dim_k Hⁿ(K ⊗ k) = homologyDim K n (ker φ)`.

## Lemmas on modules

- `fibreDim_congr`: fibre dimensions are invariant under linear equivalences.
- `exists_splitEquiv`: if `M ⧸ N` is projective, there is `M ≃ N × (M ⧸ N)` compatible with the
  inclusion and the projection. This is Mathlib's `Function.Exact.splitSurjectiveEquiv` applied to
  a section obtained from `Module.projective_lifting_property`.
- `projective_of_projective_quotient`: a submodule with projective quotient of a projective module
  is projective (a direct summand, `Module.Projective.of_split`).
- `fibreDim_eq_add_of_projective_quotient`: for `M` finite and `M ⧸ N` projective,
  `fibreDim M p = fibreDim N p + fibreDim (M ⧸ N) p`. The splitting gives
  `κ(p) ⊗ M ≃ (κ(p) ⊗ N) × (κ(p) ⊗ (M ⧸ N))` (`TensorProduct.prodRight`), and dimensions add
  (`Module.finrank_prod`). The submodule `N` is finite because it is a direct summand.

## Complexes

Let `K` be a cochain complex of `R`-modules indexed by `ℤ`.

- `range_eq_ker_of_isZero_homology`: if `Hⁱ(K) = 0`, then `im d^{i-1} = ker dⁱ`
  (`HomologicalComplex.exactAt_iff'`, `ShortComplex.moduleCat_exact_iff_range_eq_ker`).
  The indices are passed with equations `j + 1 = i` and `i + 1 = k`.
- `cokerEquivRange`: if `Hⁱ(K) = 0`, the cokernel of `d^{i-1}` is isomorphic to the image of `dⁱ`
  (first isomorphism theorem).
- `projective_coker_step`, `projective_coker`: let the terms of `K` be projective, `K` vanish above
  `b`, and `Hⁱ(K) = 0` for `i > 0`. Then the cokernel `K^{j+1} ⧸ im dʲ` is projective for all
  `j ≥ 0`. The proof is a descending induction. Above `b` the cokernel is zero. If the cokernel
  of `dⁱ` is projective and `Hⁱ = 0`, the cokernel of `d^{i-1}` is isomorphic to the image of
  `dⁱ`, a direct summand of `K^{i+1}` (`projective_of_projective_quotient`).
- `homologyDim_eq_zero_of_isZero_homology`: under the same hypotheses with finite terms,
  `homologyDim K i p = 0` for every `i > 0` and every prime `p`. Here
  `homologyDim K i p = c_{i-1}(p) + c_i(p) - e_{i+1}(p)`. The cokernel of `d^{i-1}` is the image of
  `dⁱ` (`cokerEquivRange`), and `0 → im dⁱ → K^{i+1} → coker dⁱ → 0` has projective cokernel, so
  `c_{i-1} + c_i = e_{i+1}` (`fibreDim_eq_add_of_projective_quotient`). With the dimension formula
  of `FibreDimension` this gives `Hⁱ(K ⊗ k) = 0`.

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

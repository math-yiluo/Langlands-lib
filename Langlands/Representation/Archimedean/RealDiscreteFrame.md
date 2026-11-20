# Frame vectors and the scalar step

Lean module: `Langlands.Representation.Archimedean.RealDiscreteFrame`. Author: Worker 380, for
Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), as part of the proof of
`Langlands.Archimedean.RealTiedDiscreteSeparatedScalarCommutantStatement` (the chain ends in
`RealDiscreteSeparatedProof`). All declarations are in the namespace
`Langlands.Archimedean.RealDiscreteFrame`.

## Purpose and provenance

The module proves no statement of record. Its main theorem `hasScalarCommutant_of_frame` is an
abstract form of the scalar step of the minimal-`K`-type argument. A vector of the minimal type
is replaced here by a finite family of "frame vectors": products of an `O(n)`-fixed vector with
minors of `g U` for a fixed complex matrix `U`. The theorem reduces the scalar commutant to
linear relations between the values at `1` of `O(n)`-equivariant images of the frame vectors.
All declarations are internal. Cauchy–Binet is the Library lemma `MatrixMinor.minor_mul`
(module `Langlands.LinearAlgebra.MatrixMinor`).

## Notation

* `minor X A B` (Library `MatrixMinor`): the determinant of the submatrix of `X` with rows `A`
  and columns `B` in increasing order; it is `0` when `|A| ≠ |B|`.
* `cmat g`, `kmat k`: the complex matrices of `g ∈ GL_n(ℝ)` and `k ∈ O(n)`.
* `IsMinorShift n ps qs R`, `mulProd hsh C` (module `RealDiscreteMinorCyclic`):
  `mulProd hsh C T = T · ∏_j minorG (R j) (C j)`.
* `ev`, `IsKEquivariant`, `rot` (module `RealDiscreteScalarFunctional`).
* `HasScalarCommutant n ds` (Library `RealTemperedCommutantReduction`): every endomorphism of
  `KF n ds` commuting with `O(n)` and with the Lie algebra is a scalar.

## Declarations

* `sum_minor_mul_minor`, `prod_minor_mul`: Cauchy–Binet summed over all column sets,
  `Σ_C minor X A C · minor Y C B = minor (X Y) A B` (terms with `|C| ≠ |A|` vanish), and its
  product form over `j ∈ Fin N` (`Finset.prod_univ_sum`).
* `swap_lt_swap`, `minor_submatrix_swap`: if `D` does not contain both `p` and `p + 1`, the
  transposition of `p, p + 1` preserves the order of `D`, so swapping these two columns of `X`
  replaces `minor X A D` by `minor X A (swap D)`.
* `minorG_eq`, `cmat_mul_toUnits`, `apply_mul_toUnits`: `minorG A B g = minor (cmat g) A B`,
  `cmat (g k) = cmat g · kmat k`, and an `O(n)`-fixed `T` satisfies `T(g k) = T(g)`.
* `frameVec hsh T U D = Σ_{D'} (∏_j minor U (D'_j) (D_j)) • mulProd hsh D' T`. By
  `prod_minor_mul`, `frameVec_apply` gives its value `T(g) · ∏_j minor (cmat g · U) (R_j) (D_j)`.
* `rep_frameVec_apply`, `rep_frameVec`: for `T` fixed by `O(n)` and `U V = 1`,
  `R(k) u_D = Σ_{D'} (∏_j minor (V · kmat k · U) (D'_j) (D_j)) • u_{D'}`. Proof: compare values,
  writing `cmat g · kmat k · U = (cmat g · U) · (V · kmat k · U)` and using `prod_minor_mul`.
* `mulProd_eq_sum_frameVec`: `mulProd hsh D T = Σ_{D'} (∏_j minor V (D'_j) (D_j)) • u_{D'}`
  (the same computation with `cmat g = (cmat g · U) · V`).
* `rep_frameVec_diagonal`: if `kmat k · U = U · diag(μ)`, then
  `R(k) u_D = (∏_j ∏_{i ∈ D_j} μ_i) • u_D`.
* `rep_frameVec_perm`: if `kmat k · U` is `U` with its columns permuted by `σ` and this moves
  each `D_j` to `D'_j` in every minor, then `R(k) u_D = u_{D'}`.
* `ev_frameVec_eq_zero_of_rotation` (**rotation vanishing**): if
  `kmat (rot n p θ) · U = U · diag(e^{i c_l θ})` for all `θ`, the block of `ds` at position `p`
  is the induction block of `d`, and `|Σ_j Σ_{l ∈ D_j} c_l| ≤ |d.weight|`, then
  `ev (L u_D) = 0` for every equivariant `L`. Proof: `rep_frameVec_diagonal` makes `u_D` a
  rotation eigenvector of weight `Σ_j Σ_{l ∈ D_j} c_l`; apply `ev_eq_zero_of_rotation`.
* `ev_frameVec_sign` (**sign relation**): if `s` is the diagonal sign matrix of `a` and
  `kmat s · U = U · diag(μ)`, then
  `(∏_j ∏_{l ∈ D_j} μ_l) · ev (L u_D) = χ_ds(a) · ev (L u_D)`
  (`rep_frameVec_diagonal` and `ev_rep_sign`).
* `ev_frameVec_flip` (**flip relation**): under the hypotheses of `rep_frameVec_perm` for a sign
  matrix `s` of `a`, `ev (L u_{D'}) = χ_ds(a) · ev (L u_D)`.
* `hasScalarCommutant_of_frame` (**scalar step**). Hypotheses: `T ∈ KF n ps` is fixed by `O(n)`
  and generates `KF n ps` under the Lie algebra; `U V = 1`; `Φ : KF n qs → KF n ds` is a
  surjective `(𝔤, K)`-intertwiner; and there are scalars `ε_D` and an index `D₀` with
  `ev (L u_D) = ε_D · ev (L u_{D₀})` for every `O(n)`-equivariant `L : KF n qs → KF n ds` and
  every `D`. Conclusion: `HasScalarCommutant n ds`.

  Proof. Let `E` commute with `O(n)` and the Lie algebra. By `rep_frameVec`, the translates of
  each `u_D` are combinations of frame vectors. So `exists_smul_family` (module
  `RealDiscreteScalarFunctional`, applied to `Φ` and the family `u`) gives one scalar `a` with
  `E (Φ u_D) = a Φ u_D` for all `D`. By `mulProd_eq_sum_frameVec`, also
  `E (Φ (mulProd hsh D T)) = a Φ (mulProd hsh D T)`. The eigenspace `ker (E − a)` is
  Lie-stable, so its preimage under `Φ` is a Lie-stable subspace of `KF n qs` containing every
  `mulProd hsh D T`. It is `⊤` by `eq_top_of_cyclic` (module `RealDiscreteMinorCyclic`). Since
  `Φ` is surjective, `E = a` on `KF n ds`.

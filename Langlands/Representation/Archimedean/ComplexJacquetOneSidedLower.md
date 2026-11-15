# One-sided nonvanishing for the opposite nilradical

Module `Langlands.Representation.Archimedean.ComplexJacquetOneSidedLower`. It imports
`Langlands.Representation.Archimedean.ComplexJacquetOneSided`.

## Setting

The binders and hypotheses are those of the Library's `ComplexJacquetModuleFiniteStatement`
(module `ComplexJacquetReduction`) and of `ComplexJacquetOneSidedStatement` (module
`ComplexJacquetOneSided`). They range over:
- every `n : ℕ` and every complex vector space `V : Type uV`;
- every `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V`;
- every `π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V`.

The hypotheses are `IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and
`IsAdmissibleGKModule ρ`.

`ComplexJacquetFinite.ee π i p q` (Library module `ComplexJacquetFinite`) is the action of the
matrix unit `E_pq` in factor `i : Fin 2` of `𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. That product is identified with
`𝔤𝔩_n(ℂ) ⊗_ℝ ℂ` by `z ⊗ X ↦ (zX, zX̄)`. Write `E^{(0)}_pq = ee π 0 p q`; it is the ℂ-linear part
of the action.

## Statement

`ComplexJacquetOneSidedLowerStatement`: under the hypotheses above,

`Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), q < p ∧ ComplexJacquetFinite.ee π 0 p q v = w} ≠ ⊤`.

In words: the vectors `E^{(0)}_pq v` with `q < p` span a proper subspace `𝔫⁻^{(0)} V` of `V`.
Here `𝔫⁻^{(0)}` is the strictly lower triangular nilradical acting through the first factor only.
The statement differs from `ComplexJacquetOneSidedStatement` only in the condition `q < p` in
place of `p < q`.

Provenance: this statement is internal. It is a reformulation of the nonvanishing half of
Casselman's theorem, Wallach 1979, 4.14(1) (`V ≠ 𝔫V`), recorded in the Library as
`ComplexJacquetModuleNonzeroStatement` (module `ComplexJacquetFinite`). The module proves it
**equivalent** to `ComplexJacquetOneSidedStatement` (`complexJacquetOneSided_iff_lower`). That
statement is in turn proved equivalent to `ComplexJacquetModuleNonzeroStatement` in module
`ComplexJacquetOneSided` (`complexJacquetModuleNonzero_iff_oneSided`). So the lower statement
asserts exactly the literature's nonvanishing. It is introduced as an alternative target, for a
proof that naturally yields `V ≠ 𝔫⁻V` for one factor. This module does **not** prove it.

## Results

- `complexJacquetOneSided_iff_lower : ComplexJacquetOneSidedStatement.{uV} ↔
  ComplexJacquetOneSidedLowerStatement.{uV}`.
- `complexJacquetModuleFinite_of_oneSidedLower : ComplexJacquetOneSidedLowerStatement.{uV} →
  ComplexJacquetModuleFiniteStatement.{uV}`. It composes the equivalence with the
  `complexJacquetModuleFinite_of_oneSided` of module `ComplexJacquetOneSided`.

Both use only `propext`, `Classical.choice` and `Quot.sound`.

## Proof

The auxiliary results are in namespace `Langlands.Archimedean.ComplexJacquetFinite`, section
`Lower`. The route is ours: conjugation by the longest Weyl group element `w₀`, which lies in
`U(n)`.

### 1. The matrix `w₀`

- `revMat n` is the antidiagonal permutation matrix: `(w₀)_ij = 1` if `j = Fin.rev i = n − 1 − i`,
  and `0` otherwise (`revMat_apply`).
- `revMat_mul_apply`: `(w₀ A)_ij = A_{rev i, j}`. `mul_star_revMat_apply`:
  `(A w₀*)_ij = A_{i, rev j}`.
- `revMat_mul_star`: `w₀ w₀* = 1`. `revMat_mul_revMat`: `w₀ w₀ = 1`.
- `revMat_mul_single_mul`: `w₀ E_pq w₀* = E_{rev p, rev q}`, by the two entry formulas.
- `revUnit n` is `w₀` as an element of `Matrix.unitaryGroup (Fin n) ℂ`, and
  `revUnit_mul_self : w₀ w₀ = 1` there.

### 2. Conjugating the first-factor action

- `sideJacquetLower π i` is `𝔫⁻^{(i)} V`, the span of the `E^{(i)}_pq v` with `q < p`. The
  statement says `sideJacquetLower π 0 ≠ ⊤`, unfolded. (`sideJacquet π i`, from module
  `ComplexJacquetOneSided`, is the span with `p < q`.)
- `rho_rev_ee`: `ρ(w₀) (E^{(0)}_pq v) = E^{(0)}_{rev p, rev q} (ρ(w₀) v)`. The Library's
  `ComplexGenericLarge.rho_mul_pi` turns the fourth clause of `IsComplexGKModule` into
  `ρ(k) π(x) = π((1 ⊗ k) x (1 ⊗ k*)) ρ(k)`. Apply it with `k = w₀` and
  `x = tensorEquiv.symm (E_pq, 0)`, the element with `ee π 0 p q = π(x)`. Under `tensorEquiv`,
  `(1 ⊗ k) x (1 ⊗ k*)` becomes `(w₀ E_pq w₀*, 0)`, since `tensorEquiv (1 ⊗ k) = (k, k̄)` and the
  second component of `x` is `0`. This is `(E_{rev p, rev q}, 0)` by `revMat_mul_single_mul`.
- `rho_rev_rev`: `ρ(w₀) ρ(w₀) x = x`, from `revUnit_mul_self`.
- `rho_rev_mem_lower` and `rho_rev_mem_upper`: `ρ(w₀)` maps `𝔫^{(0)} V` into `𝔫⁻^{(0)} V` and
  `𝔫⁻^{(0)} V` into `𝔫^{(0)} V`. This is induction over the spanning sets with `rho_rev_ee`,
  since `p < q ↔ rev q < rev p` (`Fin.rev_lt_rev`).
- `sideJacquet_eq_top_iff_lower`: `𝔫^{(0)} V = V ↔ 𝔫⁻^{(0)} V = V`. Write any `x` as
  `ρ(w₀)(ρ(w₀) x)` and apply the previous item.

### 3. Final statements (namespace `Langlands.Archimedean`)

- `complexJacquetOneSided_iff_lower` applies `sideJacquet_eq_top_iff_lower` to each module
  under the common hypotheses.
- `complexJacquetModuleFinite_of_oneSidedLower` composes it with
  `complexJacquetModuleFinite_of_oneSided`.

## Sources

- Wallach, *Representations of reductive Lie groups* (Corvallis 1979), 4.14(1), printed p. 77
  (PDF p. 80): `V ≠ 𝔫V`. The one-sided lower reformulation and its proof are ours.
- `ComplexGenericLarge.rho_mul_pi`, `tensorEquiv`, `pairHom` and `prodAction` are imported from
  the Library module `ComplexGenericLargeReduction`; `ee`, `unitPair` from `ComplexJacquetFinite`;
  `sideJacquet`, `ee_mem_sideJacquet` and `complexJacquetModuleFinite_of_oneSided` from
  `ComplexJacquetOneSided`.

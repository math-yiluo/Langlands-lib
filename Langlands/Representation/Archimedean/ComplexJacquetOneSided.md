# Nonvanishing of the Jacquet module from one-sided nonvanishing

Module `Langlands.Representation.Archimedean.ComplexJacquetOneSided`.

## Setting

The binders are those of the Library's `ComplexJacquetModuleFiniteStatement` (module
`ComplexJacquetReduction`). They range over:
- every `n : ℕ` and every complex vector space `V : Type uV`;
- every `ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) V`;
- every `π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ V`.

The hypotheses are `IsComplexGKModule n ρ π`, `IsIrreducibleGKModule ρ π` and
`IsAdmissibleGKModule ρ`.

The Library module `ComplexJacquetFinite` defines `ComplexJacquetFinite.ee π i p q`, for
`i : Fin 2`. This is the action of the matrix unit `E_pq` in factor `i` of
`𝔤𝔩_n(ℂ) × 𝔤𝔩_n(ℂ)`. That product is identified with `𝔤𝔩_n(ℂ) ⊗_ℝ ℂ` by
`z ⊗ X ↦ (zX, zX̄)`. Concretely,

`π(1 ⊗ X) = Σ_{p,q} (X_pq · ee π 0 p q + conj(X_pq) · ee π 1 p q)` (`pi_eq_sum` below).

So `ee π 0` is the ℂ-linear ("holomorphic") part of the action and `ee π 1` the conjugate-linear
part. Write `E^{(i)}_pq = ee π i p q`. The two families commute with each other, and each one
satisfies the `𝔤𝔩_n` relations.

## Statement

`ComplexJacquetOneSidedStatement`: under the hypotheses above,

`Submodule.span ℂ {w | ∃ (p q : Fin n) (v : V), p < q ∧ ComplexJacquetFinite.ee π 0 p q v = w} ≠ ⊤`.

In words: the vectors `E^{(0)}_pq v` with `p < q` span a proper subspace `𝔫^{(0)} V` of `V`. Here
`𝔫^{(0)}` is the strictly upper triangular nilradical acting through the first factor only.

Provenance: this statement is internal. It is a reformulation of the nonvanishing half of
Casselman's theorem, Wallach 1979, 4.14(1) (`V ≠ 𝔫V`), which the Library records as the second
conjunct of `ComplexJacquetModuleFiniteStatement` and as `ComplexJacquetModuleNonzeroStatement`
(module `ComplexJacquetFinite`). The module proves that it is **equivalent** to
`ComplexJacquetModuleNonzeroStatement`:
- `complexJacquetModuleNonzero_of_oneSided`: the one-sided statement implies `𝔫V ≠ V`. This is
  the main content of the module.
- `complexJacquetOneSided_of_nonzero`: conversely, `𝔫V ≠ V` implies the one-sided statement,
  because `𝔫^{(0)} V ⊆ 𝔫V` (`ComplexJacquetFinite.sideJacquet_le`, from the Library's `ee_up`).

It is introduced as a target for a proof of nonvanishing that only needs one of the two
commuting `𝔤𝔩_n`-actions. This module does **not** prove it.

## Results

- `complexJacquetModuleNonzero_of_oneSided : ComplexJacquetOneSidedStatement.{uV} →
  ComplexJacquetModuleNonzeroStatement.{uV}`.
- `complexJacquetOneSided_of_nonzero : ComplexJacquetModuleNonzeroStatement.{uV} →
  ComplexJacquetOneSidedStatement.{uV}`.
- `complexJacquetModuleNonzero_iff_oneSided`: the equivalence of the two.
- `complexJacquetModuleFinite_of_oneSided : ComplexJacquetOneSidedStatement.{uV} →
  ComplexJacquetModuleFiniteStatement.{uV}`. It combines the first result with the Library's
  `complexJacquetModuleFinite_of_nonzero`, which supplies the unconditional finiteness half.

All of these use only `propext`, `Classical.choice` and `Quot.sound`.

## Proof

Everything except the final statements is in namespace
`Langlands.Archimedean.ComplexJacquetFinite`. The route is ours; Wallach 1979 only refers to
proofs elsewhere.

### 1. One-sided subspaces (section `Side`)

- `sideJacquet π i` is `𝔫^{(i)} V`, the span of the `E^{(i)}_pq v` with `p < q`.
  `ComplexJacquetOneSidedStatement` says `sideJacquet π 0 ≠ ⊤`, unfolded.
- `commute_ee_of_ne`: the two families commute, because `unitPair i a b * unitPair j c d = 0`
  for `i ≠ j` (`unitPair_mul_of_ne`).
- `sideJacquet_diag`: `𝔫^{(i)} V` is stable under `E^{(i)}_aa`. This follows from
  `[E_aa, E_pq] = δ_ap E_aq − δ_qa E_pa`, which is again strictly upper triangular for `p < q`.
- `sideJacquet_other`: `𝔫^{(i)} V` is stable under every `E^{(j)}_ab` with `j ≠ i`.
- `prodAction_eq_sum` and `pi_eq_sum` give the expansion of `π(1 ⊗ X)` displayed above.
- `complexJacquetSubspace_le_sup`: `𝔫V ⊆ 𝔫^{(0)} V + 𝔫^{(1)} V`. In the expansion, every term
  with `p ≥ q` vanishes for strictly upper triangular `X`.
- `upper_stable_of_ee`: a subspace stable under every `E^{(i)}_pq` with `p ≤ q` is stable under
  `π(1 ⊗ X)` for every upper triangular `X`.
- `sideAct π i` is the action of `ℂ[x_1, …, x_n]` sending `x_a` to `E^{(i)}_aa`, namely the
  Library's `diagAct π` composed with a renaming of variables.
- `sideAnn π i N` is the ideal of polynomials `f` with `sideAct π i f V ⊆ N`.
- `side_psum_close`: let `N` contain every `E^{(i)}_ab v` with `a < b` and be stable under the
  `E^{(i)}_aa`. Then, modulo `sideAnn π i N`, each power sum `p_b` (`1 ≤ b ≤ n`) is congruent to
  a polynomial of degree `< b`. This is the Library's argument (`trace_scalar`, `diag_pow`)
  restricted to factor `i`.
- `sideAct_mem_sideBox_sup`: under the same hypotheses, `sideAct π i f w` lies in
  `sideBox π i W + N` for all `f` and all `w ∈ W`. Here `sideBox π i W` is the finite sum of
  the images of `W` under the box monomials (`finiteDimensional_sideBox`). The proof uses the
  Library's `xpow_close` and `mem_boxSpan_sup`.

### 2. Generalized eigenspaces and quotients (sections `Eigen`, `Quot`)

- `mem_maxGenEigenspace_shift`: if `T R = R T + h R`, then `R` maps the generalized
  `μ`-eigenspace of `T` into the generalized `(μ + h)`-eigenspace.
- `mem_iSup_of_maps`: suppose a map sends each `F μ` with `s μ` into `G (g μ)`, and `s μ`
  implies `t (g μ)`. Then it maps `⨆_{s μ} F μ` into `⨆_{t μ} G μ`.
- `mapQ_commute` and `mapQ_shift`: commutation and the shift relation pass to the operators
  induced on a quotient `M ⧸ N` (`Submodule.mapQ`).

### 3. The reduction (section `Reduction`)

- `weightOp π` is `T = −Σ_a a · E^{(1)}_aa`, with `a` the 0-based index.
  - `weightOp_comm` and `weightOp_ee_apply`: `[T, E^{(1)}_pq] = (q − p) E^{(1)}_pq`.
  - `weightOp_commute`: `T` commutes with every `E^{(i)}_aa`.
  - `weightOp_mem_sideJacquet`: `T` preserves `𝔫^{(0)} V`.
- `diag_sub_mem`: on a `U(n)`-stable subspace `W`, `E^{(0)}_aa − E^{(1)}_aa` acts. It equals
  `−i · π(1 ⊗ i E_aa)`, and `i E_aa` is skew-Hermitian, so the Library's `skew_stable` applies.
- `sideSpan π W` is the span of the vectors `sideAct π 0 f w`, `w ∈ W`.
  - `le_sideSpan`: it contains `W`.
  - `ee_one_mem_sideSpan`: it is stable under `E^{(1)}_aa`, since
    `E^{(1)}_aa ψ₀(f) w = ψ₀(f x_a) w − ψ₀(f)(E^{(0)}_aa − E^{(1)}_aa) w`.

**Main theorem** `jacquet_ne_top_of_sideJacquet_ne_top`: if `𝔫^{(0)} V ≠ V`, then `𝔫V ≠ V`.
Let `N = 𝔫^{(0)} V` and `Q = V ⧸ N`.

1. Pick `v₀ ≠ 0` and let `W = FiniteVectors.orbitSpan ρ v₀`. It is finite-dimensional, by the
   first clause of `IsComplexGKModule`, and `U(n)`-stable. By the Library's
   `upperClosure_eq_top` (irreducibility), every subspace containing `W` and stable under all
   `E^{(i)}_pq` with `p ≤ q` is `V` (`hfill`).
2. `T` preserves `N`, so it induces `T_Q` on `Q`. Let `Y` be the image of `sideSpan π W` in
   `Q`.
   - `Y` is `T_Q`-stable, by `ee_one_mem_sideSpan`.
   - `Y` is finite-dimensional. By `sideAct_mem_sideBox_sup` with `i = 0` and the subspace `N`,
     `sideSpan π W ⊆ sideBox π 0 W + N`.
   - `Y ≠ 0`. Otherwise `W ⊆ N`. But `N` is stable under all `E^{(i)}_pq` with `p ≤ q`:
     `E^{(0)}_pq` with `p < q` maps `V` into `N`, and `sideJacquet_diag` and
     `sideJacquet_other` cover the rest. So `N = V` by step 1, a contradiction.
3. Let `μ₀` be an eigenvalue of `T_Q|_Y` with minimal real part; there are finitely many
   (`Module.End.finite_hasEigenvalue`). Define `Q_≥` (resp. `Q_>`) as the sum of the generalized
   eigenspaces of `T_Q` on `Q` with eigenvalue `μ`, `Re μ ≥ Re μ₀` (resp. `>`).
   - `Y ⊆ Q_≥`. The finite-dimensional space `Y` is the sum of the generalized eigenspaces of
     `T_Q|_Y` (`Module.End.iSup_maxGenEigenspace_eq_top`). Each nonzero one belongs to an
     eigenvalue, hence has real part `≥ Re μ₀`.
4. The preimage of `Q_≥` in `V` is `V`. It contains `W` by step 3, and it is stable under all
   `E^{(i)}_pq` with `p ≤ q`:
   - `E^{(0)}_pq` with `p < q` maps into `N`, which maps to `0`;
   - `E^{(0)}_aa` and `E^{(1)}_aa` commute with `T`, so they preserve generalized eigenspaces
     (`Module.End.mapsTo_maxGenEigenspace_of_comm`);
   - `E^{(1)}_pq` with `p < q` shifts eigenvalues by `q − p > 0`, so it maps `Q_≥` into
     `Q_> ⊆ Q_≥` (`hshift`).

   Then step 1 applies.
5. Suppose `𝔫V = V`. By `complexJacquetSubspace_le_sup`, `V = N + 𝔫^{(1)} V`. Every generator
   `E^{(1)}_pq v` of `𝔫^{(1)} V` maps into `Q_>` by step 4 and `hshift`. Hence `Q = Q_>`.
6. Take an eigenvector `y₀ ≠ 0` of `T_Q|_Y` for `μ₀`. It lies in the generalized
   `μ₀`-eigenspace of `T_Q` and, by step 5, in `Q_> ⊆ ⨆_{μ ≠ μ₀}` (generalized eigenspaces).
   These are independent (`Module.End.independent_maxGenEigenspace`), so `y₀ = 0`, a
   contradiction.

### 4. Final statements (namespace `Langlands.Archimedean`)

- `complexJacquetModuleNonzero_of_oneSided` applies the main theorem.
- `complexJacquetOneSided_of_nonzero` uses `sideJacquet_le`.
- `complexJacquetModuleNonzero_iff_oneSided` combines the two.
- `complexJacquetModuleFinite_of_oneSided` composes with `complexJacquetModuleFinite_of_nonzero`.

## Sources

- Wallach, *Representations of reductive Lie groups* (Corvallis 1979), 4.14(1), printed p. 77
  (PDF p. 80): `V ≠ 𝔫V`. The one-sided reformulation and the reduction proof are ours.
- The finiteness machinery (`diag_pow`, `trace_scalar`, `xpow_close`, `mem_boxSpan_sup`,
  `skew_stable`, `upperClosure_eq_top`) is imported from the Library module
  `ComplexJacquetFinite`.

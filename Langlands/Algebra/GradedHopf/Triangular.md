# Triangularizing graded matrix coefficients by fixed vectors

Author: Worker 1419 designed and implemented this module and wrote this note, as part of
task `90ffbd89-a3dd-4baa-84ba-332896bbbd17` (split unipotence from the absence of zero Lie
weights). It is linear algebra over a field `k` for square matrices of elements of a
commutative `k`-bialgebra `A`. Everything is in namespace
`Langlands.Algebra.GradedHopf.Triangular`.

The main theorem `exists_unitriangular_conj` is the graded form of a standard fact: if every
nonzero finite-dimensional comodule has a nonzero fixed vector, then every matrix of
coefficients becomes upper unitriangular after a change of basis. The grading by `ℤ` comes
along: the new basis consists of homogeneous vectors.

## Provenance

This is internal infrastructure for the proof of
`RelativeRoot.TorusActionSplitUnipotenceStatement`. The ungraded statement is the standard
argument that a unipotent representation is triangularizable: take a fixed line and
induct on the quotient. It appears in standard texts on affine group schemes; no source
states the graded, matrix-coefficient form proved here, so none is cited. The Lean proof
is self-contained and works with matrices only; it does not use comodules.

## Weight-compatible scalar matrices (`section Compat`)

- `Compat w w' P` for `P : Matrix m n k`, `w : m → ℤ` and `w' : n → ℤ`: every nonzero entry
  `P i j` has `w i = w' j`. These are the base changes that respect a grading.
- `Compat.mul`: compatible matrices compose (`Compat w w' P → Compat w' w'' P' →
  Compat w w'' (P * P')`). A nonzero entry of `P * P'` needs a nonzero product
  `P i l * P' l j`.
- `Compat.of_mul_eq_one`: if `P * Q = 1` and `Q * P = 1` and `Compat w w' P`, then
  `Compat w' w Q`. Proof: `P` commutes with the diagonal projections onto each weight
  (`diag(w = d) * P = P * diag(w' = d)`). Conjugating by `P` shows that `Q` commutes with
  them too, which forces the entries of `Q` between different weights to vanish.

## Change of basis (`section Conj`)

From here on `A` is a commutative ring with `[Bialgebra k A]`, and `n` is a finite type
with decidable equality.

- `conj Q P a = Q.map (algebraMap k A) * a * P.map (algebraMap k A)` for scalar matrices
  `Q P : Matrix n n k` and `a : Matrix n n A`.
- `conj_apply`: `conj Q P a i j = ∑ l, ∑ m, (Q i l * P m j) • a l m`.
- `conj_conj`: `conj Q₂ P₂ (conj Q₁ P₁ a) = conj (Q₂ * Q₁) (P₁ * P₂) a`.
- `conj_one_one`: `conj 1 1 a = a`.
- `map_algebraMap_map`: applying a `k`-algebra map `φ : A →ₐ[k] B` to the entries of
  `M.map (algebraMap k A)` gives `M.map (algebraMap k B)`.
- `adjoin_conj`: if `P * Q = 1` and the entries of `a` generate `A` as a `k`-algebra, then so
  do the entries of `conj Q P a`. Each entry of `a = conj P Q (conj Q P a)` is a
  `k`-linear combination of entries of `conj Q P a`.

## Matrix coefficients (`section Corep`)

- `IsCorep k a` for `a : Matrix n n A` is the conjunction of
  `a.map (Bialgebra.comulAlgHom k A) = a.map includeLeft * a.map includeRight` (in
  `Matrix n n (A ⊗[k] A)`) and `a.map (Bialgebra.counitAlgHom k A) = 1`.
- `isCorep_iff`: `IsCorep k a` holds iff
  `∀ i j, Coalgebra.comul (a i j) = ∑ l, a i l ⊗ₜ[k] a l j` and
  `∀ i j, Coalgebra.counit (a i j) = if i = j then 1 else 0`.
- `IsCorep.conj`: if `IsCorep k a` and `P * Q = 1`, then `IsCorep k (conj Q P a)`. The
  comultiplication is an algebra map, so it fixes scalar matrices. Then
  `Q a P ↦ Q (a ⊗ 1) (1 ⊗ a) P = (Q (a ⊗ 1) P) (Q (1 ⊗ a) P)` uses `P * Q = 1`, and the
  counit gives `Q * P = 1` (from `mul_eq_one_comm`).
- `IsCorep.submatrix_succ`: for `a` indexed by `Fin (n + 1)` with `IsCorep k a` and
  `a i.succ 0 = 0` for all `i`, the submatrix `a.submatrix Fin.succ Fin.succ` (delete the
  first row and column) satisfies `IsCorep k`. The term `l = 0` in
  `Δ(a i.succ j.succ)` vanishes.

## Grading (`section Graded`)

Let `𝒜 : ℤ → Submodule k A`.

- `IsGraded 𝒜 w a` for weights `w : n → ℤ`: `a i j ∈ 𝒜 (w j - w i)` for all `i j`.
- `IsGraded.conj`: if `IsGraded 𝒜 w a`, `Compat w w' P` and `Compat w' w Q`, then
  `IsGraded 𝒜 w' (conj Q P a)`. In `conj_apply`, a nonzero coefficient `Q i l * P m j`
  forces `w' i = w l` and `w m = w' j`.
- `exists_homogeneous_fixed` (now with `[GradedAlgebra 𝒜]`): if `IsGraded 𝒜 w a`, `v ≠ 0`
  and `∑ j, v j • a i j = v i • 1` for all `i`, then some `v' ≠ 0` with the same fixed-vector
  equation is supported in a single weight `d` (`v' j ≠ 0 → w j = d`). Take `j₀` with
  `v j₀ ≠ 0` and let `v'` keep the entries of `v` of weight `w j₀`. Projecting the `i`-th
  equation to degree `w j₀ - w i` gives the equation for `v'`, since `1` has degree `0`.

## The induction step (`section Step`)

Fix `v : Fin (n + 1) → k` and `i₀` with `v i₀ ≠ 0`.

- `stepP v i₀`: its column `0` is `v`; its column `j ≠ 0` is the standard basis vector at
  `Equiv.swap 0 i₀ j`. So the columns are `v` and all standard basis vectors except the
  `i₀`-th.
- `stepQ v i₀`: an explicit inverse. Row `0` is `(v i₀)⁻¹` at `i₀`. Row `j ≠ 0` is the
  standard basis vector at `Equiv.swap 0 i₀ j` minus `(v i₀)⁻¹ * v (Equiv.swap 0 i₀ j)` at
  `i₀`.
- `stepQ_mul_stepP`: `stepQ v i₀ * stepP v i₀ = 1` when `v i₀ ≠ 0` (computation by cases).
- `compat_stepP`: if `v` is supported in weight `d`, then
  `Compat w (w ∘ Equiv.swap 0 i₀) (stepP v i₀)`; the new weight of index `0` is `w i₀ = d`.
- `conj_stepP_apply_zero`: if `Q * stepP v i₀ = 1` and `v` is a fixed vector of `a`, then the
  column `0` of `conj Q (stepP v i₀) a` is the first standard basis vector: its entries are
  `1` at `0` and `0` elsewhere. Column `0` of `a * stepP` is `a v = v · 1`, and
  `Q v = Q (stepP e₀) = e₀`.

## Block matrices (`section Extend`)

- `ext1 P` for `P : Matrix (Fin n) (Fin n) k` is the block-diagonal matrix of size `n + 1`
  with blocks `1` and `P`; `ext1_zero_zero`, `ext1_zero_succ`, `ext1_succ_zero` and
  `ext1_succ_succ` give its entries.
- `ext1_mul`: `ext1 P * ext1 Q = ext1 (P * Q)`; `ext1_one`: `ext1 1 = 1`.
- `compat_ext1`: `Compat (w ∘ Fin.succ) w' P → Compat w (Fin.cons (w 0) w') (ext1 P)`.
- `conj_ext1`: if column `0` of `b` is the first standard basis vector, then
  `conj (ext1 Q) (ext1 P) b` has entry `1` at `(0, 0)` and `0` at `(i.succ, 0)`, and its lower
  right block is `conj Q P (b.submatrix Fin.succ Fin.succ)`.

## The main theorem (`section Main`)

Let `𝒜 : ℤ → Submodule k A` with `[GradedAlgebra 𝒜]`.

- `IsUnitriangular b` for `b : Matrix (Fin n) (Fin n) A`: `b i i = 1` for all `i` and
  `b i j = 0` whenever `j < i`.
- `exists_unitriangular_conj 𝒜 hfix`: the hypothesis `hfix` says that every
  `b : Matrix (Fin (m + 1)) (Fin (m + 1)) A` with `IsCorep k b` has a nonzero `v` with
  `∑ j, v j • b i j = v i • 1` for all `i`. The conclusion: for all `n`, `w : Fin n → ℤ` and
  `a` with `IsCorep k a` and `IsGraded 𝒜 w a`, there are `w' : Fin n → ℤ` and
  `P Q : Matrix (Fin n) (Fin n) k` with `P * Q = 1`, `Compat w w' P` and
  `IsUnitriangular (conj Q P a)`.

Proof by induction on `n`. For `n = 0` take `P = Q = 1`. For `n + 1`: `hfix` and
`exists_homogeneous_fixed` give a fixed vector `v ≠ 0` supported in one weight. Choose `i₀`
with `v i₀ ≠ 0` and conjugate by `stepP v i₀` and `stepQ v i₀`. The result `b` satisfies
`IsCorep` (`IsCorep.conj`) and is graded for `w ∘ Equiv.swap 0 i₀` (`compat_stepP`,
`Compat.of_mul_eq_one`, `IsGraded.conj`). Its column `0` is the first standard basis vector
(`conj_stepP_apply_zero`). Its lower right block satisfies `IsCorep`
(`IsCorep.submatrix_succ`) and is graded, so the induction hypothesis gives `w₂`, `P'`, `Q'`.
The final change of basis is `P = stepP v i₀ * ext1 P'` and `Q = ext1 Q' * stepQ v i₀`, with
weights `Fin.cons (w i₀) w₂`. `conj_conj` and `conj_ext1` show the result is upper
unitriangular.

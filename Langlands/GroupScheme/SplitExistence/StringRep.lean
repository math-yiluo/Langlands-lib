import Langlands.GroupScheme.SplitExistence.WeylModule
import Mathlib.Logic.Equiv.Sum
import Mathlib.Tactic.Module

/-!
# Representations of `SL₂` assembled from root strings

Fix `α : X` and an additive map `pair : X →+ ℤ` (standing for `⟨·, α^∨⟩`). A *string
decomposition* of a finite family of weights `ω : C → X` is an equivalence
`C ≃ Σ k : K, Fin (len k + 1)` such that the `k`-th block is an unbroken `α`-string
`ω k₀, ω k₀ + α, …, ω k₀ + len k • α` with `⟨ω k₀, α^∨⟩ = -len k ≤ 3`. On such a family the
blockwise representations `gam (len k)` assemble to a representation `rep` of `2 × 2`
matrices, with divided powers `E k`, `F k` of the raising and lowering operators.

String decompositions are closed under finite sums and sigma types, and every family with
injective weights whose `α`-strings are unbroken of length at most `3` has one.
-/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

variable {X : Type*} [AddCommGroup X] (α : X) (pair : X →+ ℤ)

/-- A decomposition of a family of weights `ω : C → X` into unbroken `α`-strings of length at
most `3`. The block `k` is the string `ω (eqv.symm ⟨k, j⟩) = ω (eqv.symm ⟨k, 0⟩) + j • α`,
`j = 0, …, len k`, whose bottom weight pairs to `-len k` with `α^∨`. -/
structure StringDecomp (C : Type u) (ω : C → X) where
  /-- The index type of the strings. -/
  K : Type u
  [fintypeK : Fintype K]
  [decEqK : DecidableEq K]
  /-- The length of each string (one less than its number of weights). -/
  len : K → ℕ
  len_le : ∀ k, len k ≤ 3
  /-- The identification of the index type with the disjoint union of the strings. -/
  eqv : C ≃ Σ k : K, Fin (len k + 1)
  weight_eq : ∀ k (j : Fin (len k + 1)),
    ω (eqv.symm ⟨k, j⟩) = ω (eqv.symm ⟨k, 0⟩) + (j : ℕ) • α
  pair_bot : ∀ k, pair (ω (eqv.symm ⟨k, 0⟩)) = -(len k : ℤ)

attribute [instance] StringDecomp.fintypeK StringDecomp.decEqK

namespace StringDecomp

variable {α pair} {C : Type u} {ω : C → X} (S : StringDecomp α pair C ω)

/-- The action of a `2 × 2` matrix `g` on the span of the family: `gam (len k) g` on the
`k`-th string. -/
def rep {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) : Matrix C C R :=
  (blockDiagonal' fun k => gam (S.len k) g).submatrix S.eqv S.eqv

/-- The `k`-th divided power of the raising operator. -/
def E (k : ℕ) : Matrix C C ℤ :=
  (blockDiagonal' fun k' => gamE (S.len k') k).submatrix S.eqv S.eqv

/-- The `k`-th divided power of the lowering operator. -/
def F (k : ℕ) : Matrix C C ℤ :=
  (blockDiagonal' fun k' => gamF (S.len k') k).submatrix S.eqv S.eqv

variable {R : Type*} [CommRing R]

theorem rep_mul [Fintype C] (g h : Matrix (Fin 2) (Fin 2) R) :
    S.rep (g * h) = S.rep g * S.rep h := by
  rw [rep, rep, rep, submatrix_mul_equiv, ← blockDiagonal'_mul]
  simp only [gam_mul]

theorem rep_one [DecidableEq C] : S.rep (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
  simp only [rep, gam_one]
  rw [show (blockDiagonal' fun k => (1 : Matrix (Fin (S.len k + 1)) (Fin (S.len k + 1)) R)) = 1
    from blockDiagonal'_one, submatrix_one_equiv]

theorem rep_map {R' : Type*} [CommRing R'] (f : R →+* R') (g : Matrix (Fin 2) (Fin 2) R) :
    (S.rep g).map f = S.rep (g.map f) := by
  rw [rep, rep, ← submatrix_map, blockDiagonal'_map _ _ f.map_zero]
  simp only [gam_map]

theorem E_zero [DecidableEq C] : S.E 0 = 1 := by
  simp only [E, gamE_zero]
  rw [show (blockDiagonal' fun k => (1 : Matrix (Fin (S.len k + 1)) (Fin (S.len k + 1)) ℤ)) = 1
    from blockDiagonal'_one, submatrix_one_equiv]

theorem F_zero [DecidableEq C] : S.F 0 = 1 := by
  simp only [F, gamF_zero]
  rw [show (blockDiagonal' fun k => (1 : Matrix (Fin (S.len k + 1)) (Fin (S.len k + 1)) ℤ)) = 1
    from blockDiagonal'_one, submatrix_one_equiv]

theorem E_mul [Fintype C] (a b : ℕ) :
    S.E a * S.E b = ((a + b).choose a : ℤ) • S.E (a + b) := by
  rw [E, E, E, submatrix_mul_equiv, ← blockDiagonal'_mul]
  simp only [gamE_mul]
  exact congrArg (fun M => M.submatrix S.eqv S.eqv)
    (blockDiagonal'_smul (((a + b).choose a : ℕ) : ℤ) fun k => gamE (S.len k) (a + b))

theorem F_mul [Fintype C] (a b : ℕ) :
    S.F a * S.F b = ((a + b).choose a : ℤ) • S.F (a + b) := by
  rw [F, F, F, submatrix_mul_equiv, ← blockDiagonal'_mul]
  simp only [gamF_mul]
  exact congrArg (fun M => M.submatrix S.eqv S.eqv)
    (blockDiagonal'_smul (((a + b).choose a : ℕ) : ℤ) fun k => gamF (S.len k) (a + b))

theorem E_eq_zero {k : ℕ} (hk : 3 < k) : S.E k = 0 := by
  simp only [E, gamE_eq_zero (lt_of_le_of_lt (S.len_le _) hk)]
  rw [show (blockDiagonal' fun k' => (0 : Matrix (Fin (S.len k' + 1)) (Fin (S.len k' + 1)) ℤ)) = 0
    from blockDiagonal'_zero, submatrix_zero]
  rfl

theorem F_eq_zero {k : ℕ} (hk : 3 < k) : S.F k = 0 := by
  simp only [F, gamF_eq_zero (lt_of_le_of_lt (S.len_le _) hk)]
  rw [show (blockDiagonal' fun k' => (0 : Matrix (Fin (S.len k' + 1)) (Fin (S.len k' + 1)) ℤ)) = 0
    from blockDiagonal'_zero, submatrix_zero]
  rfl

theorem rep_upper {N : ℕ} (hN : 3 < N) (s : R) :
    S.rep !![1, s; 0, 1] = ∑ k ∈ Finset.range N, s ^ k • (S.E k).map (Int.castRingHom R) := by
  ext r c
  simp only [rep, E, submatrix_apply, Matrix.sum_apply, smul_apply, map_apply,
    blockDiagonal'_apply]
  by_cases h : (S.eqv r).1 = (S.eqv c).1
  · simp only [h, dite_true]
    rw [gam_upper (S.len_le _) (lt_of_le_of_lt (S.len_le _) hN), Matrix.sum_apply]
    simp
  · simp [h]

theorem rep_lower {N : ℕ} (hN : 3 < N) (s : R) :
    S.rep !![1, 0; s, 1] = ∑ k ∈ Finset.range N, s ^ k • (S.F k).map (Int.castRingHom R) := by
  ext r c
  simp only [rep, F, submatrix_apply, Matrix.sum_apply, smul_apply, map_apply,
    blockDiagonal'_apply]
  by_cases h : (S.eqv r).1 = (S.eqv c).1
  · simp only [h, dite_true]
    rw [gam_lower (S.len_le _) (lt_of_le_of_lt (S.len_le _) hN), Matrix.sum_apply]
    simp
  · simp [h]

/-- The weight of the `j`-th member of the `k`-th string. -/
theorem weight_symm (k : S.K) (j : Fin (S.len k + 1)) :
    ω (S.eqv.symm ⟨k, j⟩) = ω (S.eqv.symm ⟨k, 0⟩) + (j : ℕ) • α :=
  S.weight_eq k j

theorem weight_apply (d : C) :
    ω d = ω (S.eqv.symm ⟨(S.eqv d).1, 0⟩) + ((S.eqv d).2 : ℕ) • α := by
  conv_lhs => rw [← S.eqv.symm_apply_apply d]
  exact S.weight_eq _ _

theorem pair_apply (hα : pair α = 2) (d : C) :
    pair (ω d) = 2 * ((S.eqv d).2 : ℕ) - (S.len (S.eqv d).1 : ℤ) := by
  rw [S.weight_apply d, map_add, S.pair_bot, map_nsmul, hα, nsmul_eq_mul]
  ring

theorem exists_of_blockDiagonal'_ne_zero {f : S.K → ℕ}
    {M : ∀ k, Matrix (Fin (f k + 1)) (Fin (f k + 1)) R} {x y : Σ k, Fin (f k + 1)}
    (h : blockDiagonal' M x y ≠ 0) :
    ∃ k a b, x = ⟨k, a⟩ ∧ y = ⟨k, b⟩ ∧ M k a b ≠ 0 := by
  rcases x with ⟨k, a⟩
  rcases y with ⟨k', b⟩
  by_cases hk : k = k'
  · subst hk
    exact ⟨k, a, b, rfl, rfl, by simpa using h⟩
  · exact absurd (blockDiagonal'_apply_ne M a b hk) h

theorem E_ne_zero {k : ℕ} {r c : C} (h : S.E k r c ≠ 0) : ω r = ω c + k • α := by
  simp only [E, submatrix_apply] at h
  obtain ⟨k', a, b, hr, hc, h⟩ := S.exists_of_blockDiagonal'_ne_zero h
  have hab := gamE_ne_zero h
  rw [S.weight_apply r, S.weight_apply c, hr, hc, add_assoc, ← add_smul, ← hab]

theorem F_ne_zero {k : ℕ} {r c : C} (h : S.F k r c ≠ 0) : ω r + k • α = ω c := by
  simp only [F, submatrix_apply] at h
  obtain ⟨k', a, b, hr, hc, h⟩ := S.exists_of_blockDiagonal'_ne_zero h
  have hab := gamF_ne_zero h
  rw [S.weight_apply r, S.weight_apply c, hr, hc, add_assoc, ← add_smul, ← hab]

theorem rep_weyl_ne_zero (hα : pair α = 2) {r c : C}
    (h : S.rep (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) R) r c ≠ 0) :
    ω r = ω c - pair (ω c) • α := by
  simp only [rep, submatrix_apply] at h
  obtain ⟨k', a, b, hr, hc, h⟩ := S.exists_of_blockDiagonal'_ne_zero h
  have hab := gam_weyl_ne_zero (S.len_le _) h
  rw [S.pair_apply hα c, S.weight_apply r, S.weight_apply c, hr, hc]
  simp only
  rw [add_sub_assoc, add_right_inj, ← natCast_zsmul, ← natCast_zsmul, ← sub_smul]
  congr 1
  omega

theorem rep_diag [DecidableEq C] (t u : R) :
    S.rep !![t, 0; 0, u] =
      diagonal fun d => t ^ ((S.eqv d).2 : ℕ) * u ^ (S.len (S.eqv d).1 - (S.eqv d).2) := by
  simp only [rep, gam_diag (S.len_le _)]
  rw [blockDiagonal'_diagonal, submatrix_diagonal_equiv]
  rfl

/-- The bracket of the raising and lowering operators is the diagonal matrix of the pairings
with `α^∨`. -/
theorem E_one_mul_F_one_sub [Fintype C] [DecidableEq C] (hα : pair α = 2) :
    S.E 1 * S.F 1 - S.F 1 * S.E 1 = diagonal fun d => pair (ω d) := by
  rw [E, F, submatrix_mul_equiv, submatrix_mul_equiv,
    show ∀ A B : Matrix (Σ k : S.K, Fin (S.len k + 1)) (Σ k : S.K, Fin (S.len k + 1)) ℤ,
      A.submatrix S.eqv S.eqv - B.submatrix S.eqv S.eqv = (A - B).submatrix S.eqv S.eqv
      from fun _ _ => rfl,
    ← blockDiagonal'_mul, ← blockDiagonal'_mul, ← blockDiagonal'_sub]
  have : ((fun k => gamE (S.len k) 1 * gamF (S.len k) 1) -
      fun k => gamF (S.len k) 1 * gamE (S.len k) 1) =
      fun k => diagonal fun r : Fin (S.len k + 1) => 2 * (r : ℤ) - S.len k := by
    funext k
    exact gamE_one_mul_gamF_one_sub (S.len_le k)
  rw [this, blockDiagonal'_diagonal, submatrix_diagonal_equiv]
  congr 1
  funext d
  simp only [Function.comp_apply, S.pair_apply hα d]

theorem rep_diag_units [DecidableEq C] (hα : pair α = 2) (t : Rˣ) :
    S.rep !![(t : R), 0; 0, ((t⁻¹ : Rˣ) : R)] = diagonal fun d => ((t ^ pair (ω d) : Rˣ) : R) := by
  rw [S.rep_diag]
  congr 1
  funext d
  rw [S.pair_apply hα d]
  have hlt := (S.eqv d).2.isLt
  generalize ((S.eqv d).2 : ℕ) = j at hlt ⊢
  generalize S.len (S.eqv d).1 = m at hlt ⊢
  obtain ⟨l, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_lt_succ hlt)
  rw [Nat.add_sub_cancel_left,
    show 2 * (j : ℤ) - ((j + l : ℕ) : ℤ) = (j : ℤ) - (l : ℤ) by push_cast; ring,
    zpow_sub, zpow_natCast, zpow_natCast, Units.val_mul, ← inv_pow, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val]

/-- The entries of the divided powers of the raising operator. -/
theorem E_apply (k : ℕ) (r c : C) :
    S.E k r c = if (S.eqv r).1 = (S.eqv c).1 ∧ ((S.eqv c).2 : ℕ) + k = (S.eqv r).2 then
      (((S.eqv r).2 : ℕ).choose k : ℤ) else 0 := by
  simp only [E, submatrix_apply]
  generalize S.eqv r = x
  generalize S.eqv c = y
  rcases x with ⟨k₁, a⟩
  rcases y with ⟨k₂, b⟩
  by_cases h : k₁ = k₂
  · subst h
    simp [gamE]
  · simp [h, blockDiagonal'_apply_ne]

/-- The entries of the divided powers of the lowering operator. -/
theorem F_apply (k : ℕ) (r c : C) :
    S.F k r c = if (S.eqv r).1 = (S.eqv c).1 ∧ ((S.eqv r).2 : ℕ) + k = (S.eqv c).2 then
      ((S.len (S.eqv r).1 - (S.eqv r).2 : ℕ).choose k : ℤ) else 0 := by
  simp only [F, submatrix_apply]
  generalize S.eqv r = x
  generalize S.eqv c = y
  rcases x with ⟨k₁, a⟩
  rcases y with ⟨k₂, b⟩
  by_cases h : k₁ = k₂
  · subst h
    simp [gamF]
  · simp [h, blockDiagonal'_apply_ne]

/-! ### Sums and sigma types of string decompositions -/

/-- Rewriting `f a = f b` to `a = b` in the condition of an `if`, for injective `f`, with
arbitrary decidability instances. -/
theorem ite_and_congr_of_injective {A B Γ : Type*} {f : A → B} (hf : Function.Injective f)
    {a b : A} {P : Prop} {_ : Decidable (f a = f b ∧ P)} {_ : Decidable (a = b ∧ P)} (x y : Γ) :
    (if f a = f b ∧ P then x else y) = if a = b ∧ P then x else y :=
  if_congr (and_congr_left' hf.eq_iff) rfl rfl

section Sum

variable {C₁ C₂ : Type u} {ω₁ : C₁ → X} {ω₂ : C₂ → X}

/-- The disjoint union of two string decompositions. -/
def sum (S₁ : StringDecomp α pair C₁ ω₁) (S₂ : StringDecomp α pair C₂ ω₂) :
    StringDecomp α pair (C₁ ⊕ C₂) (Sum.elim ω₁ ω₂) where
  K := S₁.K ⊕ S₂.K
  len := Sum.elim S₁.len S₂.len
  len_le := by rintro (k | k); exacts [S₁.len_le k, S₂.len_le k]
  eqv := (Equiv.sumCongr S₁.eqv S₂.eqv).trans
    (Equiv.sumSigmaDistrib fun k => Fin (Sum.elim S₁.len S₂.len k + 1)).symm
  weight_eq := by rintro (k | k) j; exacts [S₁.weight_eq k j, S₂.weight_eq k j]
  pair_bot := by rintro (k | k); exacts [S₁.pair_bot k, S₂.pair_bot k]

variable (S₁ : StringDecomp α pair C₁ ω₁) (S₂ : StringDecomp α pair C₂ ω₂)

theorem sum_len_inl (k : S₁.K) : (S₁.sum S₂).len (Sum.inl k) = S₁.len k := rfl

theorem sum_len_inr (k : S₂.K) : (S₁.sum S₂).len (Sum.inr k) = S₂.len k := rfl

theorem sum_eqv_inl (r : C₁) :
    (S₁.sum S₂).eqv (Sum.inl r) = ⟨Sum.inl (S₁.eqv r).1, (S₁.eqv r).2⟩ := rfl

theorem sum_eqv_inr (r : C₂) :
    (S₁.sum S₂).eqv (Sum.inr r) = ⟨Sum.inr (S₂.eqv r).1, (S₂.eqv r).2⟩ := rfl

theorem sum_E (k : ℕ) : (S₁.sum S₂).E k = fromBlocks (S₁.E k) 0 0 (S₂.E k) := by
  ext (r | r) (c | c) <;> simp [E_apply, sum_eqv_inl, sum_eqv_inr] <;>
    first
      | exact ite_and_congr_of_injective Sum.inl_injective _ _
      | exact ite_and_congr_of_injective Sum.inr_injective _ _

theorem sum_F (k : ℕ) : (S₁.sum S₂).F k = fromBlocks (S₁.F k) 0 0 (S₂.F k) := by
  ext (r | r) (c | c) <;> simp [F_apply, sum_eqv_inl, sum_eqv_inr, sum_len_inl, sum_len_inr] <;>
    first
      | exact ite_and_congr_of_injective Sum.inl_injective _ _
      | exact ite_and_congr_of_injective Sum.inr_injective _ _

end Sum

section Sigma

variable {W : Type u} [Fintype W] [DecidableEq W] {D : W → Type u} {ν : ∀ w, D w → X}

/-- The disjoint union of a finite family of string decompositions. -/
def sigma (T : ∀ w, StringDecomp α pair (D w) (ν w)) :
    StringDecomp α pair (Σ w, D w) (fun d => ν d.1 d.2) where
  K := Σ w, (T w).K
  len k := (T k.1).len k.2
  len_le k := (T k.1).len_le k.2
  eqv := (Equiv.sigmaCongrRight fun w => (T w).eqv).trans
    (Equiv.sigmaAssoc fun w (k : (T w).K) => Fin ((T w).len k + 1)).symm
  weight_eq k j := (T k.1).weight_eq k.2 j
  pair_bot k := (T k.1).pair_bot k.2

variable (T : ∀ w, StringDecomp α pair (D w) (ν w))

theorem sigma_len (k : (sigma T).K) : (sigma T).len k = (T k.1).len k.2 := rfl

theorem sigma_eqv (w : W) (r : D w) :
    (sigma T).eqv ⟨w, r⟩ = ⟨⟨w, ((T w).eqv r).1⟩, ((T w).eqv r).2⟩ := rfl

theorem sigma_E (k : ℕ) : (sigma T).E k = blockDiagonal' fun w => (T w).E k := by
  ext ⟨w, r⟩ ⟨w', c⟩
  by_cases h : w = w'
  · subst h
    rw [blockDiagonal'_apply_eq, E_apply, E_apply, sigma_eqv, sigma_eqv]
    exact ite_and_congr_of_injective sigma_mk_injective _ _
  · rw [blockDiagonal'_apply_ne _ _ _ h, E_apply, sigma_eqv, sigma_eqv]
    exact ite_eq_right_iff.2 fun h' => absurd (congrArg Sigma.fst h'.1) h

theorem sigma_F (k : ℕ) : (sigma T).F k = blockDiagonal' fun w => (T w).F k := by
  ext ⟨w, r⟩ ⟨w', c⟩
  by_cases h : w = w'
  · subst h
    rw [blockDiagonal'_apply_eq, F_apply, F_apply, sigma_eqv, sigma_eqv]
    exact ite_and_congr_of_injective sigma_mk_injective _ _
  · rw [blockDiagonal'_apply_ne _ _ _ h, F_apply, sigma_eqv, sigma_eqv]
    exact ite_eq_right_iff.2 fun h' => absurd (congrArg Sigma.fst h'.1) h

end Sigma

end StringDecomp

/-! ### String decompositions from unbroken root strings -/

/-- Root-string data for a family of weights `ω : C → X` with injective weight map: `bot d` and
`top d` are the numbers of steps by which `ω d` can be moved down and up along `α` within the
family; the strings are unbroken, of length at most `3`, and `⟨ω d, α^∨⟩ = bot d - top d`. -/
structure StringData (C : Type u) (ω : C → X) where
  /-- The number of steps down from `ω d` along `α` within the family. -/
  bot : C → ℕ
  /-- The number of steps up from `ω d` along `α` within the family. -/
  top : C → ℕ
  injective : Function.Injective ω
  exists_iff : ∀ d (z : ℤ), (∃ d', ω d' = ω d + z • α) ↔ -(bot d : ℤ) ≤ z ∧ z ≤ top d
  bot_add_top_le : ∀ d, bot d + top d ≤ 3
  pair_eq : ∀ d, pair (ω d) = (bot d : ℤ) - top d

namespace StringData

variable {α pair} {C : Type u} {ω : C → X} (T : StringData α pair C ω)

theorem bot_top_of_eq {d d' : C} {z : ℤ} (h : ω d' = ω d + z • α) :
    (T.bot d' : ℤ) = T.bot d + z ∧ (T.top d' : ℤ) = T.top d - z := by
  have key : ∀ z' : ℤ, (-(T.bot d' : ℤ) ≤ z' ∧ z' ≤ T.top d') ↔
      (-(T.bot d : ℤ) ≤ z + z' ∧ z + z' ≤ T.top d) := by
    intro z'
    rw [← T.exists_iff, ← T.exists_iff, h, add_assoc, ← add_smul]
  have h1 := (key (-(T.bot d' : ℤ))).1 ⟨le_rfl, by omega⟩
  have h2 := (key (T.top d')).1 ⟨by omega, le_rfl⟩
  have h3 := (key (-(T.bot d : ℤ) - z)).2 ⟨by omega, by omega⟩
  have h4 := (key (T.top d - z)).2 ⟨by omega, by omega⟩
  omega

/-- The member of the family of weight `ω d + z • α`. -/
def mate (d : C) (z : ℤ) (hz : -(T.bot d : ℤ) ≤ z ∧ z ≤ T.top d) : C :=
  ((T.exists_iff d z).2 hz).choose

theorem weight_mate (d : C) (z : ℤ) (hz : -(T.bot d : ℤ) ≤ z ∧ z ≤ T.top d) :
    ω (T.mate d z hz) = ω d + z • α :=
  ((T.exists_iff d z).2 hz).choose_spec

/-- The bottom of the `α`-string through `d`. -/
def bottom (d : C) : C :=
  T.mate d (-(T.bot d : ℤ)) ⟨le_rfl, by omega⟩

theorem weight_bottom (d : C) : ω (T.bottom d) = ω d + (-(T.bot d : ℤ)) • α :=
  T.weight_mate d _ _

theorem bot_bottom (d : C) : T.bot (T.bottom d) = 0 := by
  have := (T.bot_top_of_eq (T.weight_bottom d)).1
  omega

theorem top_bottom (d : C) : T.top (T.bottom d) = T.bot d + T.top d := by
  have := (T.bot_top_of_eq (T.weight_bottom d)).2
  omega

theorem eq_add_smul_iff (r c : C) (z : ℤ) :
    ω r = ω c + z • α ↔ T.bottom r = T.bottom c ∧ (T.bot r : ℤ) = T.bot c + z := by
  constructor
  · intro h
    have hb := (T.bot_top_of_eq h).1
    refine ⟨T.injective ?_, hb⟩
    rw [T.weight_bottom, T.weight_bottom, h, hb]
    module
  · rintro ⟨h, hb⟩
    have h' := congrArg ω h
    rw [T.weight_bottom, T.weight_bottom, hb] at h'
    calc ω r = ω r + (-((T.bot c : ℤ) + z)) • α + ((T.bot c : ℤ) + z) • α := by module
      _ = ω c + z • α := by rw [h']; module

/-- The string decomposition defined by unbroken root strings. -/
def decomp [Finite C] : StringDecomp α pair C ω where
  K := {d // T.bot d = 0}
  fintypeK := Fintype.ofFinite _
  decEqK := Classical.decEq _
  len k := T.top k.1
  len_le k := by have := T.bot_add_top_le k.1; have := k.2; omega
  eqv :=
    { toFun := fun d => ⟨⟨T.bottom d, T.bot_bottom d⟩, ⟨T.bot d, by rw [T.top_bottom]; omega⟩⟩
      invFun := fun k => T.mate k.1.1 k.2 ⟨by have := k.1.2; omega, by have := k.2.2; omega⟩
      left_inv := fun d => by
        apply T.injective
        simp only
        rw [T.weight_mate, T.weight_bottom]
        module
      right_inv := fun k => by
        rcases k with ⟨⟨k, hk⟩, j⟩
        have hj : (j : ℕ) ≤ T.top k := Nat.le_of_lt_succ j.isLt
        have hm := T.weight_mate k j ⟨by omega, by omega⟩
        have hb := (T.bot_top_of_eq hm).1
        have h1 : T.bottom (T.mate k j ⟨by omega, by omega⟩) = k := by
          apply T.injective
          rw [T.weight_bottom, hm, hb, hk]
          module
        refine Sigma.ext (Subtype.ext h1) ((Fin.heq_ext_iff (by dsimp only; rw [h1])).2 ?_)
        simp only
        omega }
  weight_eq k j := by
    simp only [Equiv.coe_fn_symm_mk]
    rw [T.weight_mate, T.weight_mate]
    simp
  pair_bot k := by
    simp only [Equiv.coe_fn_symm_mk]
    rw [T.weight_mate]
    simp only [Fin.val_zero, Nat.cast_zero, zero_smul, add_zero]
    rw [T.pair_eq, k.2]
    simp

theorem decomp_eqv_fst [Finite C] (d : C) :
    (T.decomp.eqv d).1 = ⟨T.bottom d, T.bot_bottom d⟩ := rfl

theorem decomp_eqv_snd [Finite C] (d : C) : ((T.decomp.eqv d).2 : ℕ) = T.bot d := rfl

theorem decomp_len [Finite C] (d : C) (h : T.bot d = 0) : T.decomp.len ⟨d, h⟩ = T.top d := rfl

open Classical in
/-- The raising operator of the decomposition moves `ω c` to `ω c + α` with coefficient
`bot (ω c + α)`. -/
theorem decomp_E_one [Finite C] (r c : C) :
    T.decomp.E 1 r c = if ω r = ω c + α then (T.bot r : ℤ) else 0 := by
  rw [StringDecomp.E_apply, decomp_eqv_snd, decomp_eqv_snd, decomp_eqv_fst, decomp_eqv_fst,
    Nat.choose_one_right]
  refine if_congr ?_ rfl rfl
  have key := T.eq_add_smul_iff r c 1
  rw [one_smul] at key
  rw [key]
  exact ⟨fun ⟨h1, h2⟩ => ⟨congrArg Subtype.val h1, by omega⟩,
    fun ⟨h1, h2⟩ => ⟨Subtype.ext h1, by omega⟩⟩

open Classical in
/-- The lowering operator of the decomposition moves `ω c` to `ω c - α` with coefficient
`top (ω c - α)`. -/
theorem decomp_F_one [Finite C] (r c : C) :
    T.decomp.F 1 r c = if ω r + α = ω c then (T.top r : ℤ) else 0 := by
  rw [StringDecomp.F_apply, decomp_eqv_snd, decomp_eqv_snd, decomp_eqv_fst, decomp_eqv_fst,
    Nat.choose_one_right, decomp_len, T.top_bottom, Nat.add_sub_cancel_left]
  refine if_congr ?_ rfl rfl
  have key := T.eq_add_smul_iff c r 1
  rw [one_smul] at key
  rw [eq_comm (a := ω r + α), key]
  exact ⟨fun ⟨h1, h2⟩ => ⟨(congrArg Subtype.val h1).symm, by omega⟩,
    fun ⟨h1, h2⟩ => ⟨Subtype.ext h1.symm, by omega⟩⟩

end StringData

end Langlands.GroupScheme.SplitExistence

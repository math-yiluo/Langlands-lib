import Langlands.GroupScheme.SplitExistence.Subgroups
import Mathlib.LinearAlgebra.Matrix.Block

/-! # Positivity, triangularity and weight permutation

* The roots positive for the base `b` are exactly those on which the dominant functional `ℓ`
  is positive.
* `UT`: the subgroup of `GL_n(K)` of matrices whose nonzero entries `(c, d)` have
  `ℓ(wt d) < ℓ(wt c)` or are diagonal entries equal to `1`. It contains `U⁺`.
* `IsWeightPerm`: matrices whose nonzero entries `(c, d)` have `wt c = w (wt d)` for a fixed
  map `w`. The subgroup `N` consists of such matrices.
* Consequently `B ⊓ N = T`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [Field K]

/-! ### Positivity -/

theorem ℓ_root_eq_sum {j : J} {f : J → ℤ} (h : P.root j = ∑ k ∈ b.support, f k • P.root k) :
    D.ℓ (P.root j) = ∑ k ∈ b.support, f k * D.ℓ (P.root k) := by
  rw [h, map_sum]
  simp [map_zsmul]

theorem ℓ_root_pos_or_neg (j : J) :
    (b.IsPos j ∧ 0 < D.ℓ (P.root j)) ∨ (¬ b.IsPos j ∧ D.ℓ (P.root j) < 0) := by
  obtain ⟨f, hfs, hf, heq⟩ := b.exists_root_eq_sum_int j
  have hht := RootPairing.Base.height_eq_sum heq
  rw [D.ℓ_root_eq_sum heq]
  rcases hf with hf | hf
  · left
    obtain ⟨hf0, i, hi⟩ := Pi.lt_def.1 hf
    have hib : i ∈ b.support := hfs (Function.mem_support.2 (ne_of_gt hi))
    constructor
    · rw [RootPairing.Base.isPos_iff, hht]
      exact Finset.sum_pos' (fun k _ => hf0 k) ⟨i, hib, hi⟩
    · refine Finset.sum_pos' (fun k hk => mul_nonneg (hf0 k) (D.ℓ_pos k hk).le) ⟨i, hib, ?_⟩
      exact mul_pos hi (D.ℓ_pos i hib)
  · right
    obtain ⟨hf0, i, hi⟩ := Pi.lt_def.1 hf
    have hib : i ∈ b.support := hfs (Function.mem_support.2 (ne_of_lt hi))
    constructor
    · rw [RootPairing.Base.isPos_iff, hht, not_lt]
      exact (Finset.sum_neg' (fun k _ => hf0 k) ⟨i, hib, hi⟩).le
    · refine Finset.sum_neg' (fun k hk => mul_nonpos_of_nonpos_of_nonneg (hf0 k)
        (D.ℓ_pos k hk).le) ⟨i, hib, ?_⟩
      exact mul_neg_of_neg_of_pos hi (D.ℓ_pos i hib)

theorem isPos_iff_ℓ_pos (j : J) : b.IsPos j ↔ 0 < D.ℓ (P.root j) := by
  rcases D.ℓ_root_pos_or_neg j with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h h1, fun h => absurd h (not_lt.2 h2.le)⟩

theorem ℓ_root_ne_zero (j : J) : D.ℓ (P.root j) ≠ 0 := by
  rcases D.ℓ_root_pos_or_neg j with ⟨-, h⟩ | ⟨-, h⟩
  · exact h.ne'
  · exact h.ne

/-! ### Unitriangular matrices with respect to `ℓ` -/

/-- Nonzero entries `(c, d)` are diagonal entries equal to `1` or have `ℓ(wt d) < ℓ(wt c)`. -/
def IsUT (M : Matrix (Fin D.n) (Fin D.n) K) : Prop :=
  ∀ c d, M c d ≠ 0 → (c = d ∧ M c d = 1) ∨ D.ℓ (D.wt d) < D.ℓ (D.wt c)

/-- The block-triangularity of matrices whose nonzero entries `(c, d)` have
`ℓ(wt d) ≤ ℓ(wt c)`. -/
theorem blockTriangular_of_isUT {M : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsUT M) :
    M.BlockTriangular fun c => OrderDual.toDual (D.ℓ (D.wt c)) := by
  intro c d hcd
  by_contra hne
  rcases hM c d hne with ⟨rfl, -⟩ | h
  · exact lt_irrefl _ hcd
  · exact (lt_asymm hcd) h

theorem isUT_one : D.IsUT (1 : Matrix (Fin D.n) (Fin D.n) K) := by
  intro c d h
  by_cases hcd : c = d
  · subst hcd
    exact Or.inl ⟨rfl, by simp⟩
  · exact absurd (by simp [one_apply, hcd]) h

theorem IsUT.mul {M M' : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsUT M) (hM' : D.IsUT M') :
    D.IsUT (M * M') := by
  intro c d h
  by_cases hcd : c = d
  · subst hcd
    left
    refine ⟨rfl, ?_⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single c]
    · have h1 : M c c * M' c c ≠ 0 := by
        intro h0
        apply h
        rw [Matrix.mul_apply, Finset.sum_eq_single c]
        · exact h0
        · intro e _ hec
          by_contra hne
          rcases hM c e (left_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₁
          · exact hec rfl
          · rcases hM' e c (right_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₂
            · exact hec rfl
            · exact lt_asymm h₁ h₂
        · simp
      rcases hM c c (left_ne_zero_of_mul h1) with ⟨-, h₁⟩ | h₁
      · rcases hM' c c (right_ne_zero_of_mul h1) with ⟨-, h₂⟩ | h₂
        · rw [h₁, h₂, one_mul]
        · exact absurd h₂ (lt_irrefl _)
      · exact absurd h₁ (lt_irrefl _)
    · intro e _ hec
      by_contra hne
      rcases hM c e (left_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₁
      · exact hec rfl
      · rcases hM' e c (right_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₂
        · exact hec rfl
        · exact lt_asymm h₁ h₂
    · simp
  · right
    rw [Matrix.mul_apply] at h
    obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    rcases hM c e (left_ne_zero_of_mul he) with ⟨rfl, -⟩ | h₁
    · rcases hM' c d (right_ne_zero_of_mul he) with ⟨rfl, -⟩ | h₂
      · exact absurd rfl hcd
      · exact h₂
    · rcases hM' e d (right_ne_zero_of_mul he) with ⟨rfl, -⟩ | h₂
      · exact h₁
      · exact h₂.trans h₁

theorem IsUT.inv {g : GL (Fin D.n) K} (hg : D.IsUT (g : Matrix (Fin D.n) (Fin D.n) K)) :
    D.IsUT ((g⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
  set M := (g : Matrix (Fin D.n) (Fin D.n) K) with hMdef
  set M' := ((g⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) with hM'def
  have hbt' : M'.BlockTriangular fun c => OrderDual.toDual (D.ℓ (D.wt c)) := by
    let _ : Invertible M := Units.invertible g
    have h := Matrix.blockTriangular_inv_of_blockTriangular (D.blockTriangular_of_isUT hg)
    rwa [show M⁻¹ = M' by rw [hMdef, hM'def, Matrix.coe_units_inv]] at h
  have hprod : M' * M = 1 := by rw [hMdef, hM'def, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have key : ∀ c d, D.ℓ (D.wt c) = D.ℓ (D.wt d) → M' c d * M d d = (1 : Matrix _ _ K) c d := by
    intro c d hcd
    rw [← hprod, Matrix.mul_apply, Finset.sum_eq_single d]
    · intro e _ hed
      by_contra hne
      have h1 : ¬ D.ℓ (D.wt c) < D.ℓ (D.wt e) := fun hlt => left_ne_zero_of_mul hne (hbt' hlt)
      rcases hg e d (right_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h2
      · exact hed rfl
      · exact h1 (hcd ▸ h2)
    · simp
  have hdd : ∀ d, M d d = 1 := by
    intro d
    have h := key d d rfl
    rw [one_apply_eq] at h
    rcases hg d d (right_ne_zero_of_mul (h ▸ one_ne_zero)) with ⟨-, h'⟩ | h'
    · exact h'
    · exact absurd h' (lt_irrefl _)
  intro c d h
  by_cases hlt : D.ℓ (D.wt d) < D.ℓ (D.wt c)
  · exact Or.inr hlt
  · left
    have hle : D.ℓ (D.wt c) ≤ D.ℓ (D.wt d) := not_lt.1 hlt
    have hge : D.ℓ (D.wt d) ≤ D.ℓ (D.wt c) := by
      by_contra h'
      exact h (hbt' (lt_of_not_ge h' : D.ℓ (D.wt c) < D.ℓ (D.wt d)))
    have heq : D.ℓ (D.wt c) = D.ℓ (D.wt d) := le_antisymm hle hge
    have h2 := key c d heq
    rw [hdd d, mul_one] at h2
    by_cases hcd : c = d
    · subst hcd
      exact ⟨rfl, by rw [h2, one_apply_eq]⟩
    · rw [one_apply_ne hcd] at h2
      exact absurd h2 h

/-- The subgroup of `ℓ`-unitriangular matrices. -/
def utSub : Subgroup (GL (Fin D.n) K) where
  carrier := {g | D.IsUT (g : Matrix (Fin D.n) (Fin D.n) K)}
  mul_mem' {g g'} hg hg' := by
    change D.IsUT ((g * g' : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K)
    rw [Units.val_mul]
    exact IsUT.mul D hg hg'
  one_mem' := by
    change D.IsUT ((1 : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K)
    rw [Units.val_one]
    exact D.isUT_one
  inv_mem' {g} hg := IsUT.inv D hg

/-- Root elements of positive roots are `ℓ`-unitriangular. -/
theorem isUT_x {j : J} (hj : b.IsPos j) (s : K) :
    D.IsUT ((D.x j s : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
  have hℓ := (D.isPos_iff_ℓ_pos j).1 hj
  intro c d h
  rw [coe_x] at h ⊢
  simp only [divExp, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
    eq_intCast] at h ⊢
  -- every nonzero term with `k ≥ 1` strictly raises `ℓ`
  have hterm : ∀ k ∈ Finset.range (D.n + 1), 1 ≤ k →
      s ^ k * ((D.e j k c d : ℤ) : K) ≠ 0 → D.ℓ (D.wt d) < D.ℓ (D.wt c) := by
    intro k _ hk hne
    have he : D.e j k c d ≠ 0 := by
      intro h0
      simp [h0] at hne
    rw [D.e_weight j k c d he, map_add, map_nsmul, nsmul_eq_mul]
    have : (0 : ℤ) < (k : ℤ) * D.ℓ (P.root j) := mul_pos (by exact_mod_cast hk) hℓ
    linarith
  by_cases hlt : D.ℓ (D.wt d) < D.ℓ (D.wt c)
  · exact Or.inr hlt
  · left
    have hsum : ∑ k ∈ Finset.range (D.n + 1), s ^ k * ((D.e j k c d : ℤ) : K) =
        s ^ 0 * ((D.e j 0 c d : ℤ) : K) := by
      rw [Finset.sum_eq_single 0]
      · intro k hk hk0
        by_contra hne
        exact hlt (hterm k hk (Nat.one_le_iff_ne_zero.2 hk0) hne)
      · simp
    rw [hsum, D.e_zero] at h ⊢
    by_cases hcd : c = d
    · subst hcd
      exact ⟨rfl, by simp⟩
    · simp [one_apply_ne hcd] at h

theorem posSub_le_utSub : D.posSub K ≤ D.utSub := by
  rw [posSub, rootsSub, Subgroup.closure_le]
  intro g hg
  obtain ⟨j, hj, hg⟩ := Set.mem_iUnion₂.1 hg
  obtain ⟨s, rfl⟩ := mem_rootSub.1 hg
  exact D.isUT_x hj s

/-! ### Weight-permuting matrices -/

/-- Nonzero entries `(c, d)` satisfy `wt c = w (wt d)` for some fixed map `w`. -/
def IsWeightPerm (M : Matrix (Fin D.n) (Fin D.n) K) : Prop :=
  ∃ w : X → X, ∀ c d, M c d ≠ 0 → D.wt c = w (D.wt d)

theorem IsWeightPerm.mul {M M' : Matrix (Fin D.n) (Fin D.n) K} (hM : D.IsWeightPerm M)
    (hM' : D.IsWeightPerm M') : D.IsWeightPerm (M * M') := by
  obtain ⟨w, hw⟩ := hM
  obtain ⟨w', hw'⟩ := hM'
  refine ⟨w ∘ w', fun c d h => ?_⟩
  rw [Matrix.mul_apply] at h
  obtain ⟨e, -, he⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [hw c e (left_ne_zero_of_mul he), hw' e d (right_ne_zero_of_mul he)]
  rfl

theorem isWeightPerm_torusHom (χ : Multiplicative X →* Kˣ) :
    D.IsWeightPerm ((D.torusHom χ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) := by
  refine ⟨id, fun c d h => ?_⟩
  rw [coe_torusHom] at h
  by_cases hcd : c = d
  · rw [hcd]; rfl
  · exact absurd (by simp [diagonal_apply_ne _ hcd]) h

theorem isWeightPerm_wn (i : b.support) :
    D.IsWeightPerm ((D.wn i : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) :=
  ⟨P.reflection i, fun _ _ h => D.wn_weight i h⟩

theorem wn_inv_eq (i : b.support) :
    ((D.wn i)⁻¹ : GL (Fin D.n) K) = D.wn i * (D.torusHom (corootChar (P := P) (i : J) (-1)))⁻¹ := by
  rw [← D.wn_mul_self i, _root_.mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]

theorem isWeightPerm_of_mem_weylSub {g : GL (Fin D.n) K} (hg : g ∈ D.weylSub K) :
    D.IsWeightPerm (g : Matrix (Fin D.n) (Fin D.n) K) := by
  induction hg using Subgroup.closure_induction'' with
  | mem x hx =>
    rcases hx with ⟨χ, rfl⟩ | ⟨i, rfl⟩
    · exact D.isWeightPerm_torusHom χ
    · exact D.isWeightPerm_wn i
  | inv_mem x hx =>
    rcases hx with ⟨χ, rfl⟩ | ⟨i, rfl⟩
    · rw [← map_inv]
      exact D.isWeightPerm_torusHom _
    · rw [D.wn_inv_eq i, Units.val_mul, ← map_inv]
      exact (D.isWeightPerm_wn i).mul D (D.isWeightPerm_torusHom _)
  | one => exact ⟨id, fun c d h => by
      by_cases hcd : c = d
      · rw [hcd]; rfl
      · exact absurd (by simp [one_apply_ne hcd]) h⟩
  | mul x y _ _ hx hy =>
    rw [Units.val_mul]
    exact hx.mul D hy

/-- A weight-permuting `ℓ`-unitriangular invertible matrix is the identity. -/
theorem eq_one_of_isUT_of_isWeightPerm {g : GL (Fin D.n) K}
    (hut : D.IsUT (g : Matrix (Fin D.n) (Fin D.n) K))
    (hwp : D.IsWeightPerm (g : Matrix (Fin D.n) (Fin D.n) K)) : g = 1 := by
  obtain ⟨w, hw⟩ := hwp
  set M := (g : Matrix (Fin D.n) (Fin D.n) K)
  have hinv := IsUT.inv D hut
  have hprod : ((g⁻¹ : GL (Fin D.n) K) : Matrix (Fin D.n) (Fin D.n) K) * M = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- the diagonal entries of `g` are nonzero
  have hdd : ∀ d, M d d ≠ 0 := by
    intro d h0
    have h := congrArg (fun A => A d d) hprod
    simp only [Matrix.mul_apply, one_apply_eq] at h
    rw [Finset.sum_eq_single d] at h
    · rw [h0, mul_zero] at h
      exact zero_ne_one h
    · intro e _ hed
      by_contra hne
      rcases hinv d e (left_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₁
      · exact hed rfl
      · rcases hut e d (right_ne_zero_of_mul hne) with ⟨rfl, -⟩ | h₂
        · exact hed rfl
        · exact lt_asymm h₁ h₂
    · simp
  have hfix : ∀ d, w (D.wt d) = D.wt d := fun d => (hw d d (hdd d)).symm
  apply Units.ext
  rw [Units.val_one]
  ext c d
  change M c d = (1 : Matrix (Fin D.n) (Fin D.n) K) c d
  by_cases h : M c d = 0
  · have hcd : c ≠ d := fun hcd => hdd d (hcd ▸ h)
    rw [h, one_apply_ne hcd]
  · have hwt : D.wt c = D.wt d := (hw c d h).trans (hfix d)
    rcases hut c d h with ⟨rfl, h1⟩ | hlt
    · rw [h1, one_apply_eq]
    · rw [hwt] at hlt
      exact absurd hlt (lt_irrefl _)

/-- `B ⊓ N = T`. -/
theorem borelSub_inf_weylSub : D.borelSub K ⊓ D.weylSub K = D.torusSub K := by
  apply le_antisymm
  · rintro g ⟨hB, hN⟩
    obtain ⟨t, ht, u, hu, rfl⟩ := mem_borelSub.1 hB
    obtain ⟨χ, rfl⟩ := ht
    have huN : u ∈ D.weylSub K := by
      have : u = (D.torusHom χ)⁻¹ * (D.torusHom χ * u) := by group
      rw [this]
      exact (D.weylSub K).mul_mem ((D.weylSub K).inv_mem
        (torusSub_le_weylSub (torusHom_mem_torusSub χ))) hN
    have hu1 : u = 1 := D.eq_one_of_isUT_of_isWeightPerm (D.posSub_le_utSub hu)
      (D.isWeightPerm_of_mem_weylSub huN)
    rw [hu1, mul_one]
    exact torusHom_mem_torusSub χ
  · exact le_inf le_sup_left torusSub_le_weylSub

end ChevalleyData

end Langlands.GroupScheme.SplitExistence

import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerWords

/-! # Heights of rational matrices and archimedean entry bounds

A rational matrix `ρ` has height at most `(T, e)` when the entries of `ρ` and `ρ⁻¹` have mixed
norm at most `T` and become integral after multiplication by the positive integer `e`. Heights
multiply under products. For `x` in a compact set, the archimedean coordinates of `ρ x` and the
conjugated column directions `(ρ x)_∞⁻¹ colMatrix(w) (ρ x)_∞` have entries bounded by
`O(T)` and `O(T²)`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints

local instance heightsSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance heightsSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

section RationalPoint

/-- The adelic point of a rational matrix. -/
def ratPoint {n : ℕ} (ρ : RationalGL F n) : Points F n :=
  (GeneralLinearGroupPoints.adelicEquiv F n).symm (AdelicGL.rational F n ρ)

theorem ratPoint_mul {n : ℕ} (ρ σ : RationalGL F n) :
    ratPoint F (ρ * σ) = ratPoint F ρ * ratPoint F σ := by
  simp only [ratPoint, map_mul]

theorem ratPoint_one {n : ℕ} : ratPoint F (1 : RationalGL F n) = 1 := by
  simp only [ratPoint, map_one]

theorem ratPoint_inv {n : ℕ} (ρ : RationalGL F n) : ratPoint F ρ⁻¹ = (ratPoint F ρ)⁻¹ := by
  simp only [ratPoint, map_inv]

theorem padRational_eq_ratPoint {r k : ℕ} (hk : k ≤ r + 1) (g : RationalGL F k) :
    padRational F hk g = ratPoint F (padGL hk g) := by
  simp only [padRational, ratPoint, padGL_rational]

theorem ratPoint_eq_rational {n : ℕ} (ρ : RationalGL F n) :
    ratPoint F ρ = AdelicGroupPoints.rational F (Scheme F n)
      ((GeneralLinearGroupPoints.rationalEquiv F n).symm ρ) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  rw [GeneralLinearGroupPoints.adelicEquiv_rational, MulEquiv.apply_symm_apply, ratPoint,
    MulEquiv.apply_symm_apply]

theorem ratPoint_mem_rationalSubgroup {n : ℕ} (ρ : RationalGL F n) :
    ratPoint F ρ ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n) := by
  rw [ratPoint_eq_rational]
  exact ⟨_, rfl⟩

theorem detNorm_ratPoint {n : ℕ} (ρ : RationalGL F n) : detNorm F n (ratPoint F ρ) = 1 := by
  rw [ratPoint_eq_rational, detNorm_rational]

theorem archCoord_mul {n : ℕ} (x y : Points F n) :
    archCoord F (x * y) = archCoord F x * archCoord F y := by
  simp only [archCoord, map_mul]

theorem archCoord_inv {n : ℕ} (x : Points F n) : archCoord F x⁻¹ = (archCoord F x)⁻¹ := by
  simp only [archCoord, map_inv]

theorem archCoord_ratPoint_apply {n : ℕ} (ρ : RationalGL F n) (a b : Fin n) :
    ((archCoord F (ratPoint F ρ) : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b =
      mixedEmbedding F ((ρ : Matrix (Fin n) (Fin n) F) a b) := by
  simp only [archCoord, ratPoint, MulEquiv.apply_symm_apply]
  rw [archimedeanGLCoordinates_apply, AdelicGL.infinite_apply, AdelicGL.rational_apply,
    InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  rfl

theorem continuous_archCoord {n : ℕ} : Continuous (archCoord F (n := n)) := by
  unfold archCoord
  exact (archimedeanGLCoordinates F n).continuous.comp ((AdelicGL.infinite F n).continuous.comp
    (GeneralLinearGroupPoints.adelicHomeomorph F n).continuous)

end RationalPoint

section Norms

open scoped Classical

theorem norm_mixedEmbedding_le_iff (x : F) (t : ℝ) :
    ‖mixedEmbedding F x‖ ≤ t ↔ ∀ w : InfinitePlace F, w x ≤ t := by
  rw [mixedEmbedding.norm_eq_sup'_normAtPlace, Finset.sup'_le_iff]
  simp only [Finset.mem_univ, true_implies, mixedEmbedding.normAtPlace_apply]

theorem le_norm_mixedEmbedding (x : F) (w : InfinitePlace F) : w x ≤ ‖mixedEmbedding F x‖ :=
  (norm_mixedEmbedding_le_iff F x _).mp le_rfl w

theorem norm_mixedEmbedding_one_le : ‖mixedEmbedding F (1 : F)‖ ≤ 1 :=
  (norm_mixedEmbedding_le_iff F 1 1).mpr fun w => by rw [map_one]

/-- Entries of a product of matrices over a normed ring. -/
theorem norm_matrix_mul_apply_le {R : Type*} [NormedRing R] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) R) {α β : ℝ} (hA : ∀ a b, ‖A a b‖ ≤ α)
    (hB : ∀ a b, ‖B a b‖ ≤ β) (a b : Fin n) : ‖(A * B) a b‖ ≤ n * (α * β) := by
  rw [Matrix.mul_apply]
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ c ∈ (Finset.univ : Finset (Fin n)), ‖A a c * B c b‖ ≤ α * β := fun c _ =>
    (norm_mul_le _ _).trans
      (mul_le_mul (hA a c) (hB c b) (norm_nonneg _) ((norm_nonneg _).trans (hA a c)))
  refine (Finset.sum_le_sum h).trans ?_
  simp

end Norms

section Heights

open scoped Classical

/-- The entries of `M` have mixed norm at most `T` and become integral after multiplication
by `e`. -/
def EntryHeightLE {n : ℕ} (T : ℝ) (e : ℕ) (M : Matrix (Fin n) (Fin n) F) : Prop :=
  ∀ a b, ‖mixedEmbedding F (M a b)‖ ≤ T ∧ IsIntegral ℤ ((e : F) * M a b)

/-- The rational matrix `ρ` has height at most `(T, e)`: both `ρ` and `ρ⁻¹` satisfy
`EntryHeightLE T e`. -/
def HeightLE {n : ℕ} (T : ℝ) (e : ℕ) (ρ : RationalGL F n) : Prop :=
  EntryHeightLE F T e (ρ : Matrix (Fin n) (Fin n) F) ∧
    EntryHeightLE F T e ((ρ⁻¹ : RationalGL F n) : Matrix (Fin n) (Fin n) F)

variable {F}

theorem EntryHeightLE.mul {n : ℕ} {T₁ T₂ : ℝ} {e₁ e₂ : ℕ} {M N : Matrix (Fin n) (Fin n) F}
    (hM : EntryHeightLE F T₁ e₁ M) (hN : EntryHeightLE F T₂ e₂ N) :
    EntryHeightLE F (n * (T₁ * T₂)) (e₁ * e₂) (M * N) := by
  intro a b
  constructor
  · have h := norm_matrix_mul_apply_le (M.map (mixedEmbedding F)) (N.map (mixedEmbedding F))
      (fun a b => (hM a b).1) (fun a b => (hN a b).1) a b
    rwa [← Matrix.map_mul, Matrix.map_apply] at h
  · rw [Matrix.mul_apply, Finset.mul_sum]
    refine IsIntegral.sum _ fun c _ => ?_
    have h : ((e₁ * e₂ : ℕ) : F) * (M a c * N c b) =
        ((e₁ : F) * M a c) * ((e₂ : F) * N c b) := by
      push_cast
      ring
    rw [h]
    exact (hM a c).2.mul (hN c b).2

theorem HeightLE.mul {n : ℕ} {T₁ T₂ : ℝ} {e₁ e₂ : ℕ} {g0 ρ : RationalGL F n}
    (hg0 : HeightLE F T₁ e₁ g0) (hρ : HeightLE F T₂ e₂ ρ) :
    HeightLE F (n * (T₁ * T₂)) (e₁ * e₂) (g0 * ρ) := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul]
    exact hg0.1.mul hρ.1
  · rw [mul_inv_rev, Units.val_mul, mul_comm T₁, mul_comm e₁]
    exact hρ.2.mul hg0.2

omit [NumberField F] in
theorem isIntegral_natCast_mul_one_apply {n : ℕ} (e : ℕ) (a b : Fin n) :
    IsIntegral ℤ ((e : F) * (1 : Matrix (Fin n) (Fin n) F) a b) := by
  rw [Matrix.one_apply]
  split_ifs
  · rw [mul_one]
    exact isIntegral_natCast e
  · rw [mul_zero]
    exact isIntegral_zero

theorem norm_mixedEmbedding_one_apply_le {n : ℕ} (a b : Fin n) :
    ‖mixedEmbedding F ((1 : Matrix (Fin n) (Fin n) F) a b)‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs
  · exact norm_mixedEmbedding_one_le F
  · rw [map_zero, norm_zero]
    exact zero_le_one

theorem EntryHeightLE.one {n : ℕ} (e : ℕ) :
    EntryHeightLE F 1 e (1 : Matrix (Fin n) (Fin n) F) := fun a b =>
  ⟨norm_mixedEmbedding_one_apply_le a b, isIntegral_natCast_mul_one_apply e a b⟩

theorem HeightLE.one {n : ℕ} (e : ℕ) : HeightLE F 1 e (1 : RationalGL F n) := by
  refine ⟨?_, ?_⟩
  · rw [Units.val_one]
    exact EntryHeightLE.one e
  · rw [inv_one, Units.val_one]
    exact EntryHeightLE.one e

theorem EntryHeightLE.pad {m n : ℕ} (h : m ≤ n) {T : ℝ} (hT : 1 ≤ T) {e : ℕ}
    {g0 : RationalGL F m} (hg0 : EntryHeightLE F T e (g0 : Matrix (Fin m) (Fin m) F)) :
    EntryHeightLE F T e
      ((RankinSelbergGlobal.padGL h g0 : RationalGL F n) : Matrix (Fin n) (Fin n) F) := by
  intro a b
  rw [UnequalAnalytic.padGL_apply]
  split_ifs with hab
  · exact hg0 _ _
  · exact ⟨(norm_mixedEmbedding_one_apply_le a b).trans hT, isIntegral_natCast_mul_one_apply e a b⟩

theorem HeightLE.pad {m n : ℕ} (h : m ≤ n) {T : ℝ} (hT : 1 ≤ T) {e : ℕ}
    {g0 : RationalGL F m} (hg0 : HeightLE F T e g0) :
    HeightLE F T e (RankinSelbergGlobal.padGL h g0 : RationalGL F n) := by
  refine ⟨hg0.1.pad h hT, ?_⟩
  have h' : ((RankinSelbergGlobal.padGL h g0)⁻¹ : RationalGL F n) =
      RankinSelbergGlobal.padGL h g0⁻¹ := (map_inv (RankinSelbergGlobal.padGL h) g0).symm
  rw [h']
  exact hg0.2.pad h hT

end Heights

section Entries

open scoped Classical

variable {F}

/-- Entry bounds for the archimedean coordinates of `ρ x` and of their inverse. -/
theorem norm_archCoord_ratPoint_mul_apply_le {n : ℕ} {T : ℝ} {e : ℕ} {ρ : RationalGL F n}
    (hρ : HeightLE F T e ρ) {x : Points F n} {B : ℝ}
    (hx : ∀ a b, ‖((archCoord F x : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤ B ∧
      ‖(((archCoord F x)⁻¹ : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤ B)
    (a b : Fin n) :
    ‖((archCoord F (ratPoint F ρ * x) : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤
        n * (T * B) ∧
      ‖(((archCoord F (ratPoint F ρ * x))⁻¹ : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤
        n * (T * B) := by
  constructor
  · rw [archCoord_mul, Units.val_mul]
    refine norm_matrix_mul_apply_le _ _ (fun a b => ?_) (fun a b => (hx a b).1) a b
    rw [archCoord_ratPoint_apply]
    exact (hρ.1 a b).1
  · rw [archCoord_mul, mul_inv_rev, Units.val_mul, mul_comm T]
    refine norm_matrix_mul_apply_le _ _ (fun a b => (hx a b).2) (fun a b => ?_) a b
    rw [← archCoord_inv, ← ratPoint_inv, archCoord_ratPoint_apply]
    exact (hρ.2 a b).1

/-- Entry bounds on a compact set. -/
theorem exists_archCoord_bound {n : ℕ} {C : Set (Points F n)} (hC : IsCompact C) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ C, ∀ a b : Fin n,
      ‖((archCoord F x : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤ B ∧
      ‖(((archCoord F x)⁻¹ : ArchimedeanGL F n) : ArchimedeanMatrix F n) a b‖ ≤ B := by
  have h1 : Continuous fun x : Points F n =>
      ((archCoord F x : ArchimedeanGL F n) : ArchimedeanMatrix F n) :=
    Units.continuous_val.comp (continuous_archCoord F)
  have h2 : Continuous fun x : Points F n =>
      (((archCoord F x)⁻¹ : ArchimedeanGL F n) : ArchimedeanMatrix F n) :=
    Units.continuous_coe_inv.comp (continuous_archCoord F)
  set Φ : Points F n → (Fin n × Fin n →
      mixedEmbedding.mixedSpace F × mixedEmbedding.mixedSpace F) :=
    fun x p => (((archCoord F x : ArchimedeanGL F n) : ArchimedeanMatrix F n) p.1 p.2,
      (((archCoord F x)⁻¹ : ArchimedeanGL F n) : ArchimedeanMatrix F n) p.1 p.2) with hΦ
  have hΦc : Continuous Φ :=
    continuous_pi fun p => (h1.matrix_elem p.1 p.2).prodMk (h2.matrix_elem p.1 p.2)
  obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hΦc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun x hx a b => ⟨?_, ?_⟩⟩
  · exact (norm_fst_le (Φ x (a, b))).trans ((norm_le_pi_norm (Φ x) (a, b)).trans
      ((hB x hx).trans (le_max_left _ _)))
  · exact (norm_snd_le (Φ x (a, b))).trans ((norm_le_pi_norm (Φ x) (a, b)).trans
      ((hB x hx).trans (le_max_left _ _)))

/-- Entry bound for the conjugated column direction `y_∞⁻¹ colMatrix(w) y_∞`. -/
theorem norm_colConj_apply_le {r : ℕ} (j : ℕ) (y : Points F (r + 1))
    (w : Fin (r + 1) → mixedEmbedding.mixedSpace F) {τ ω : ℝ}
    (hy : ∀ a b, ‖((archCoord F y : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) a b‖
        ≤ τ ∧
      ‖(((archCoord F y)⁻¹ : ArchimedeanGL F (r + 1)) : ArchimedeanMatrix F (r + 1)) a b‖ ≤ τ)
    (hw : ∀ a, ‖w a‖ ≤ ω) (a b : Fin (r + 1)) :
    ‖colConj F j y w a b‖ ≤ (r + 1 : ℕ) * ((r + 1 : ℕ) * (τ * ω) * τ) := by
  have hω : 0 ≤ ω := (norm_nonneg _).trans (hw 0)
  have hc : ∀ a b, ‖colMatrix j w a b‖ ≤ ω := by
    intro a b
    rw [colMatrix_apply]
    split_ifs
    · exact hw a
    · rw [norm_zero]
      exact hω
  have h1 := norm_matrix_mul_apply_le _ _ (fun a b => (hy a b).2) hc
  exact norm_matrix_mul_apply_le _ _ h1 (fun a b => (hy a b).1) a b

end Entries

end Langlands.Global.RankinSelbergGlobal.Unfolding

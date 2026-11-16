import Langlands.Global.RankinSelberg.DualExpansionPoints
import Langlands.Global.RankinSelberg.DualExpansionSums

/-! # Dual Whittaker-type functions and their corner sums -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global

variable (F : Type u) [Field F] [NumberField F]

local instance dualDataSchemeAffine (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance dualDataSchemeSmooth (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Rational

variable {r : ℕ}

/-- A rational unipotent padded point lies in `N(𝔸)` with trivial generic character. -/
theorem padRational_mem_unipotentAdelic {k : ℕ} (hk : k ≤ r + 1) {n : RationalGL F k}
    (hn : n ∈ rationalUpperUnipotent F k) :
    padRational F hk n ∈ unipotentAdelic F (r + 1) := by
  rw [mem_unipotentAdelic_iff]
  change PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F (padRational F hk n))
  rw [pointMatrix_padRational, padGL_rational]
  exact (isUnitriangular_padGL hk _ ((mem_rationalUpperUnipotent_iff F n).mp hn)).map _

theorem genericCharacter_padRational {k : ℕ} (hk : k ≤ r + 1) {n : RationalGL F k}
    (hn : n ∈ rationalUpperUnipotent F k) (ψ : AddChar (Adeles F) ℂ)
    (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) :
    genericCharacter F r ψ (fun _ => 1) ⟨_, padRational_mem_unipotentAdelic F hk hn⟩ = 1 := by
  simp only [genericCharacter, map_one, one_mul]
  change ψ (∑ i : Fin r, pointMatrix F (padRational F hk n) i.castSucc i.succ) = 1
  rw [pointMatrix_padRational, padGL_rational]
  simp only [AdelicGL.rational_apply]
  rw [← map_sum]
  exact hψF _

end Rational

variable (m : ℕ)

/-- The corner family `q ↦ W(diag(q, 1) g)` over `N_(m+K)(F) \ GL_(m+K)(F)`. -/
def cornerFamily (K : ℕ) (W : Points F (m + K + 1) → ℂ) (q : UnipotentRationalCosets F (m + K))
    (g : Points F (m + K + 1)) : ℂ :=
  W (padRational F (Nat.le_succ (m + K)) q.out * g)

/-- The corner sum `S W(g) = Σ_q W(diag(q, 1) g)`. -/
def cornerSum (K : ℕ) (W : Points F (m + K + 1) → ℂ) (g : Points F (m + K + 1)) : ℂ :=
  ∑' q, cornerFamily F m K W q g

/-- The corner sum of absolute values. -/
def cornerNormSum (K : ℕ) (W : Points F (m + K + 1) → ℂ) (g : Points F (m + K + 1)) : ℝ :=
  ∑' q, ‖cornerFamily F m K W q g‖

/-- A dual Whittaker-type function at rank `m + K + 1`: continuous, transforming by the
inverse generic character under `N(𝔸)`, with a locally uniformly absolutely convergent corner
expansion. -/
structure DualData (ψ : AddChar (Adeles F) ℂ) (K : ℕ) (W : Points F (m + K + 1) → ℂ) : Prop where
  continuous : Continuous W
  equivariant : ∀ (n : unipotentAdelic F (m + K + 1)) (g : Points F (m + K + 1)),
    W ((n : Points F (m + K + 1)) * g) = (genericCharacter F (m + K) ψ (fun _ => 1) n)⁻¹ * W g
  summable : LocUnifSummable (cornerFamily F m K W)

variable {F m}

section Basic

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {K : ℕ} {W : Points F (m + K + 1) → ℂ}
include hψF

/-- `W(diag(g, I) z)` only depends on the coset `N(F) g`. -/
theorem DualData.padRational_of_rightRel (hW : DualData F m ψ K W) {k : ℕ}
    (hk : k ≤ m + K + 1) {a b : RationalGL F k}
    (hab : QuotientGroup.rightRel (rationalUpperUnipotent F k) a b) (z : Points F (m + K + 1)) :
    W (padRational F hk b * z) = W (padRational F hk a * z) := by
  have h := QuotientGroup.rightRel_apply.mp hab
  have hb : b = (b * a⁻¹) * a := by group
  rw [hb, padRational_mul, mul_assoc]
  have := hW.equivariant ⟨_, padRational_mem_unipotentAdelic F hk h⟩ (padRational F hk a * z)
  rw [this, genericCharacter_padRational F hk h ψ hψF, inv_one, one_mul]

omit hψF in
theorem DualData.continuous_cornerFamily (hW : DualData F m ψ K W)
    (q : UnipotentRationalCosets F (m + K)) : Continuous (cornerFamily F m K W q) :=
  hW.continuous.comp (continuous_const.mul continuous_id)

end Basic

section Cosets

variable {j : ℕ}

/-- Right multiplication by a rational `p₀` on `N_j(F) \ GL_j(F)`. -/
def cosetMul (p₀ : RationalGL F j) : UnipotentRationalCosets F j → UnipotentRationalCosets F j :=
  Quotient.map' (· * p₀) fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    have : b * p₀ * (a * p₀)⁻¹ = b * a⁻¹ := by group
    rw [this]
    exact hab

omit [NumberField F] in
theorem cosetMul_mk (p₀ : RationalGL F j) (a : RationalGL F j) :
    cosetMul p₀ (Quotient.mk _ a) = Quotient.mk _ (a * p₀) := rfl

omit [NumberField F] in
theorem cosetMul_mul (p₀ δ : RationalGL F j) (q : UnipotentRationalCosets F j) :
    cosetMul δ (cosetMul p₀ q) = cosetMul (p₀ * δ) q := by
  induction q using Quotient.inductionOn with | h a => ?_
  rw [cosetMul_mk, cosetMul_mk, cosetMul_mk, mul_assoc]

omit [NumberField F] in
theorem cosetMul_one (q : UnipotentRationalCosets F j) : cosetMul (1 : RationalGL F j) q = q := by
  induction q using Quotient.inductionOn with | h a => ?_
  rw [cosetMul_mk, mul_one]

/-- The bijection of `N_j(F) \ GL_j(F)` given by right multiplication by `p₀`. -/
def cosetMulEquiv (p₀ : RationalGL F j) :
    UnipotentRationalCosets F j ≃ UnipotentRationalCosets F j where
  toFun := cosetMul p₀
  invFun := cosetMul p₀⁻¹
  left_inv q := by rw [cosetMul_mul, mul_inv_cancel, cosetMul_one]
  right_inv q := by rw [cosetMul_mul, inv_mul_cancel, cosetMul_one]

omit [NumberField F] in
theorem rightRel_out_cosetMul (p₀ : RationalGL F j) (q : UnipotentRationalCosets F j) :
    QuotientGroup.rightRel (rationalUpperUnipotent F j) (q.out * p₀) (cosetMul p₀ q).out := by
  have : cosetMul p₀ q = Quotient.mk _ (q.out * p₀) := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  rw [this]
  exact Quotient.exact (Quotient.out_eq _).symm

end Cosets

section Invariance

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {K : ℕ} {W : Points F (m + K + 1) → ℂ}
include hψF

/-- Each corner term at `diag(p₀, 1) g` is a reindexed corner term at `g`. -/
theorem DualData.cornerFamily_padRational_mul (hW : DualData F m ψ K W)
    (p₀ : RationalGL F (m + K)) (q : UnipotentRationalCosets F (m + K)) (g : Points F (m + K + 1)) :
    cornerFamily F m K W q (padRational F (Nat.le_succ (m + K)) p₀ * g) =
      cornerFamily F m K W (cosetMul p₀ q) g := by
  unfold cornerFamily
  rw [← mul_assoc, ← padRational_mul]
  exact (hW.padRational_of_rightRel hψF _ (rightRel_out_cosetMul p₀ q) g).symm

/-- The corner sum is left invariant under `diag(GL_(m+K)(F), 1)`. -/
theorem DualData.cornerSum_padRational_mul (hW : DualData F m ψ K W)
    (p₀ : RationalGL F (m + K)) (g : Points F (m + K + 1)) :
    cornerSum F m K W (padRational F (Nat.le_succ (m + K)) p₀ * g) = cornerSum F m K W g := by
  unfold cornerSum
  simp_rw [hW.cornerFamily_padRational_mul hψF p₀]
  exact (cosetMulEquiv p₀).tsum_eq (fun q => cornerFamily F m K W q g)

/-- The corner sum of norms is left invariant under `diag(GL_(m+K)(F), 1)`. -/
theorem DualData.cornerNormSum_padRational_mul (hW : DualData F m ψ K W)
    (p₀ : RationalGL F (m + K)) (g : Points F (m + K + 1)) :
    cornerNormSum F m K W (padRational F (Nat.le_succ (m + K)) p₀ * g) =
      cornerNormSum F m K W g := by
  unfold cornerNormSum
  simp_rw [hW.cornerFamily_padRational_mul hψF p₀]
  exact (cosetMulEquiv p₀).tsum_eq (fun q => ‖cornerFamily F m K W q g‖)

end Invariance

section LastColumn

variable {r : ℕ}

theorem isUnitriangular_one_add_lastColMat {R : Type*} [CommRing R] (d : Fin r → R) :
    PrimitiveAdelicHeight.IsUnitriangular (1 + lastColMat d) := by
  refine ⟨fun a b hab => ?_, fun a => ?_⟩
  · have hab' : (b : ℕ) < a := hab
    simp only [Matrix.add_apply, lastColMat]
    rw [Matrix.one_apply_ne (fun h => by subst h; omega), dite_eq_right (by omega), add_zero]
  · simp only [Matrix.add_apply, lastColMat, Matrix.one_apply_eq]
    rw [dite_eq_right (by omega), add_zero]

theorem lastColPoint_mem_unipotentAdelic (d : Fin r → Adeles F) :
    lastColPoint F d ∈ unipotentAdelic F (r + 1) := by
  rw [mem_unipotentAdelic_iff]
  change PrimitiveAdelicHeight.IsUnitriangular (pointMatrix F (lastColPoint F d))
  rw [pointMatrix_lastColPoint]
  exact isUnitriangular_one_add_lastColMat d

theorem genericCharacter_lastColPoint (ψ : AddChar (Adeles F) ℂ) (d : Fin r → Adeles F) :
    genericCharacter F r ψ (fun _ => 1) ⟨_, lastColPoint_mem_unipotentAdelic d⟩ =
      ψ (lastEntry d) := by
  simp only [genericCharacter, map_one, one_mul]
  change ψ (∑ i : Fin r, pointMatrix F (lastColPoint F d) i.castSucc i.succ) = _
  rw [pointMatrix_lastColPoint]
  congr 1
  unfold lastEntry
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.add_apply, lastColMat, Fin.val_castSucc, Fin.val_succ]
  rw [Matrix.one_apply_ne (Fin.castSucc_lt_succ).ne, zero_add]
  by_cases hi : (i : ℕ) + 1 = r
  · rw [dite_eq_left ⟨i.isLt, hi⟩, ite_eq_left hi]
  · rw [dite_eq_right (fun h => hi h.2), ite_eq_right hi]

/-- Conjugating a last-column point by `diag(p₀, 1)`. -/
theorem padRational_mul_lastColPoint (p₀ : RationalGL F r) (d : Fin r → Adeles F) :
    padRational F (Nat.le_succ r) p₀ * lastColPoint F d =
      lastColPoint F (Matrix.mulVec ((AdelicGL.rational F r p₀ : AdelicGL F r) :
        Matrix (Fin r) (Fin r) (Adeles F)) d) * padRational F (Nat.le_succ r) p₀ := by
  apply point_ext
  rw [pointMatrix_mul, pointMatrix_mul, pointMatrix_lastColPoint, pointMatrix_lastColPoint,
    pointMatrix_padRational, mul_add, mul_one, add_mul, one_mul]
  set P := ((padGL (Nat.le_succ r) (AdelicGL.rational F r p₀) : AdelicGL F (r + 1)) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) with hP
  set e := Matrix.mulVec ((AdelicGL.rational F r p₀ : AdelicGL F r) :
    Matrix (Fin r) (Fin r) (Adeles F)) d with he
  have h1 : P * lastColMat d = lastColMat e := by
    ext a b
    rw [Matrix.mul_apply]
    by_cases hb : (b : ℕ) = r
    · rw [Fin.sum_univ_castSucc]
      have hlast : lastColMat d (Fin.last r) b = 0 := by
        simp only [lastColMat, Fin.val_last]
        rw [dite_eq_right (by omega)]
      rw [hlast, mul_zero, add_zero]
      have hcol : ∀ l : Fin r, lastColMat d l.castSucc b = d l := by
        intro l
        simp only [lastColMat, Fin.val_castSucc]
        rw [dite_eq_left ⟨l.isLt, hb⟩]
      simp_rw [hcol]
      simp only [lastColMat, hP, padGL_apply, Fin.val_castSucc, Fin.is_lt, dite_true, he,
        Matrix.mulVec, dotProduct]
      by_cases ha : (a : ℕ) < r
      · simp only [ha, hb, and_self, dite_true, Fin.eta]
      · simp only [ha, false_and, dite_false]
        refine Finset.sum_eq_zero fun x _ => ?_
        rw [ite_eq_right (fun h => by have := congrArg Fin.val h; simp at this; omega), zero_mul]
    · rw [Finset.sum_eq_zero]
      · simp only [lastColMat]
        rw [dite_eq_right (fun h => hb h.2)]
      · intro l _
        simp only [lastColMat]
        rw [dite_eq_right (fun h => hb h.2), mul_zero]
  have h2 : lastColMat e * P = lastColMat e := by
    ext a b
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last r)]
    · simp only [hP, padGL_apply, Fin.val_last, lt_irrefl, dite_false]
      by_cases hb : Fin.last r = b
      · rw [ite_eq_left hb, mul_one, ← hb]
      · rw [ite_eq_right hb, mul_zero]
        simp only [lastColMat]
        rw [dite_eq_right (fun h => hb (Fin.ext (by simp; omega)))]
    · intro l _ hl
      simp only [lastColMat]
      rw [dite_eq_right (fun h => hl (Fin.ext (by simp; omega))), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1, h2]

end LastColumn

section ColumnInvariance

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1)
  {K : ℕ} {W : Points F (m + K + 1) → ℂ}

omit hψF in
theorem DualData.lastColPoint_mul (hW : DualData F m ψ K W) (d : Fin (m + K) → Adeles F)
    (g : Points F (m + K + 1)) :
    W (lastColPoint F d * g) = (ψ (lastEntry d))⁻¹ * W g := by
  rw [show lastColPoint F d = ((⟨_, lastColPoint_mem_unipotentAdelic d⟩ :
    unipotentAdelic F (m + K + 1)) : Points F (m + K + 1)) from rfl, hW.equivariant,
    genericCharacter_lastColPoint]

include hψF

theorem lastEntry_ratVec_mulVec (p₀ : RationalGL F (m + K)) (d : Fin (m + K) → F) :
    ψ (lastEntry (Matrix.mulVec ((AdelicGL.rational F (m + K) p₀ : AdelicGL F (m + K)) :
      Matrix (Fin (m + K)) (Fin (m + K)) (Adeles F))
        (fun i => algebraMap F (Adeles F) (d i)))) = 1 := by
  have : Matrix.mulVec ((AdelicGL.rational F (m + K) p₀ : AdelicGL F (m + K)) :
      Matrix (Fin (m + K)) (Fin (m + K)) (Adeles F)) (fun i => algebraMap F (Adeles F) (d i)) =
      fun i => algebraMap F (Adeles F)
        (Matrix.mulVec (p₀ : Matrix (Fin (m + K)) (Fin (m + K)) F) d i) := by
    funext i
    simp only [Matrix.mulVec, dotProduct, AdelicGL.rational_apply, map_sum, map_mul]
  rw [this]
  unfold lastEntry
  have : ∑ i : Fin (m + K), (if (i : ℕ) + 1 = m + K then
      algebraMap F (Adeles F) (Matrix.mulVec (p₀ : Matrix (Fin (m + K)) (Fin (m + K)) F) d i)
        else 0) = algebraMap F (Adeles F) (∑ i : Fin (m + K), if (i : ℕ) + 1 = m + K then
          Matrix.mulVec (p₀ : Matrix (Fin (m + K)) (Fin (m + K)) F) d i else 0) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [this, hψF]

theorem DualData.cornerFamily_lastColPoint_mul (hW : DualData F m ψ K W) (d : Fin (m + K) → F)
    (q : UnipotentRationalCosets F (m + K)) (g : Points F (m + K + 1)) :
    cornerFamily F m K W q (lastColPoint F (fun i => algebraMap F (Adeles F) (d i)) * g) =
      cornerFamily F m K W q g := by
  unfold cornerFamily
  rw [← mul_assoc, padRational_mul_lastColPoint, mul_assoc, hW.lastColPoint_mul,
    lastEntry_ratVec_mulVec hψF, inv_one, one_mul]

theorem DualData.cornerSum_lastColPoint_mul (hW : DualData F m ψ K W) (d : Fin (m + K) → F)
    (g : Points F (m + K + 1)) :
    cornerSum F m K W (lastColPoint F (fun i => algebraMap F (Adeles F) (d i)) * g) =
      cornerSum F m K W g := by
  unfold cornerSum
  simp_rw [hW.cornerFamily_lastColPoint_mul hψF d]

theorem DualData.cornerNormSum_lastColPoint_mul (hW : DualData F m ψ K W)
    (d : Fin (m + K) → F) (g : Points F (m + K + 1)) :
    cornerNormSum F m K W (lastColPoint F (fun i => algebraMap F (Adeles F) (d i)) * g) =
      cornerNormSum F m K W g := by
  unfold cornerNormSum
  simp_rw [hW.cornerFamily_lastColPoint_mul hψF d]

end ColumnInvariance

section Regularity

variable {ψ : AddChar (Adeles F) ℂ} {K : ℕ} {W : Points F (m + K + 1) → ℂ}

theorem DualData.continuous_cornerSum (hW : DualData F m ψ K W) :
    Continuous (cornerSum F m K W) :=
  hW.summable.continuous_tsum hW.continuous_cornerFamily

theorem DualData.continuous_cornerNormSum (hW : DualData F m ψ K W) :
    Continuous (cornerNormSum F m K W) :=
  hW.summable.continuous_tsum_norm hW.continuous_cornerFamily

theorem norm_cornerSum_le (hW : DualData F m ψ K W) (g : Points F (m + K + 1)) :
    ‖cornerSum F m K W g‖ ≤ cornerNormSum F m K W g :=
  norm_tsum_le_tsum_norm (hW.summable.1 g)

end Regularity

section Pullback

variable {ψ : AddChar (Adeles F) ℂ} (hψF : ∀ a : F, ψ (algebraMap F (Adeles F) a) = 1) {K : ℕ}

theorem padGL_comp {R : Type*} [CommRing R] {k n n' : ℕ} (h₁ : k ≤ n) (h₂ : n ≤ n')
    (g : Matrix.GeneralLinearGroup (Fin k) R) :
    padGL h₂ (padGL h₁ g) = padGL (h₁.trans h₂) g := by
  ext a b
  simp only [padGL_apply]
  split_ifs <;> first | rfl | (exfalso; omega) | simp_all [Fin.ext_iff]

theorem pad_padRational {k r n : ℕ} (h₁ : k ≤ r + 1) (h₂ : r + 1 ≤ n + 1) (g : RationalGL F k) :
    pad F h₂ (padRational F h₁ g) = padRational F (h₁.trans h₂) g := by
  simp only [pad, padRational, MulEquiv.apply_symm_apply, padGL_comp]

/-- The pullback `W_y(h) = W(diag(h, 1) y)` to rank `m + K + 1`. -/
def dualPullback (W : Points F (m + (K + 1) + 1) → ℂ) (y : Points F (m + (K + 1) + 1)) :
    Points F (m + K + 1) → ℂ :=
  fun h => W (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y)

include hψF in
theorem DualData.cornerFamily_dualPullback {W : Points F (m + (K + 1) + 1) → ℂ}
    (hW : DualData F m ψ (K + 1) W) (y : Points F (m + (K + 1) + 1))
    (q : UnipotentRationalCosets F (m + K)) (h : Points F (m + K + 1)) :
    cornerFamily F m K (dualPullback W y) q h =
      cornerFamily F m (K + 1) W (cosetPad F (m + K) q)
        (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) h * y) := by
  unfold cornerFamily dualPullback
  rw [pad_mul, pad_padRational, mul_assoc]
  have h1 : QuotientGroup.rightRel (rationalUpperUnipotent F (m + K + 1))
      (padGL (Nat.le_succ (m + K)) q.out) (cosetPad F (m + K) q).out := by
    have : cosetPad F (m + K) q = Quotient.mk _ (padGL (Nat.le_succ (m + K)) q.out) := by
      conv_lhs => rw [← Quotient.out_eq q]
      rfl
    rw [this]
    exact Quotient.exact (Quotient.out_eq _).symm
  rw [hW.padRational_of_rightRel hψF _ h1, padRational_padGL]

include hψF in
theorem DualData.pullbackData {W : Points F (m + (K + 1) + 1) → ℂ} (hW : DualData F m ψ (K + 1) W)
    (y : Points F (m + (K + 1) + 1)) : DualData F m ψ K (dualPullback W y) where
  continuous := hW.continuous.comp ((continuous_pad F _).mul continuous_const)
  equivariant n g := by
    unfold dualPullback
    rw [pad_mul, mul_assoc]
    have := hW.equivariant (padUnipotent F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) n)
      (pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) g * y)
    rw [show ((padUnipotent F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) n :
      unipotentAdelic F (m + (K + 1) + 1)) : Points F (m + (K + 1) + 1)) =
        pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega) (n : Points F (m + K + 1)) from rfl]
      at this
    rw [this, genericCharacter_padUnipotent]
  summable := by
    have h := (hW.summable.comp_injective (cosetPad_injective F)).comp
      ((continuous_pad F (show m + K + 1 ≤ m + (K + 1) + 1 by omega)).mul
        (continuous_const (y := y)))
    convert h using 1
    funext q h'
    exact hW.cornerFamily_dualPullback hψF y q h'

end Pullback

end Langlands.Global.RankinSelbergGlobal.Unfolding

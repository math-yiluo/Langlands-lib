import Langlands.Representation.Archimedean.ComplexNoncompactPicture
import Langlands.Representation.Archimedean.ComplexTorusDerivative
import Langlands.Representation.Archimedean.ComplexBlockPolynomial
import Langlands.Representation.Archimedean.WeightedPolynomialDerivative

/-!
# A degree filtration of block-polynomial principal-series functions

Fix positive real polynomial weights `T_m` (`m : κ`) of degree `≤ e` on the coordinates of the
lower unipotent group, exponents `σ_m` and a slope `c`. `filtrationLevel N` consists of the
block-polynomial functions `F` of the principal series of `χ` such that, on the lower unipotent
group, `F(nbUnit v) · (∏ T_m(v))^N = (∏ T_m(v)^{σ_m}) · P(v)` with `P` of degree `≤ c (N + 1)`.

`rightDerivative_mem_filtrationLevel`: if `c ≥ (n + 1) + (n + 2) + |κ| e`, right derivatives map
level `N` to level `N + 1`. `filtrationLevel_mono`: the levels increase.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ComplexConjugate ContDiff Manifold

set_option autoImplicit false

namespace Langlands.Archimedean.NoncompactPicture

open Langlands.GeneralLinear Langlands.Archimedean.RealPolynomialFunctions
open Langlands.Archimedean.BlockPolynomial Langlands.Archimedean.LevelFunctions

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem principalSeriesCharacter_one {χ : ℕ → ℂˣ → ℂ} (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) :
    principalSeriesCharacter ℂ n χ 1 = 1 := by
  unfold principalSeriesCharacter
  refine Finset.prod_eq_one fun k _ => ?_
  have hp : phase (1 : ℂˣ) = 1 := by simp [phase]
  simp [hχ, hp]

/-- The matrix `nbMat v · X · (nbMat v)⁻¹`. -/
def conjMat (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  nbMat v * X * (nbMat v)⁻¹

theorem isPolyMat_conjMat (X : Matrix (Fin n) (Fin n) ℂ) :
    IsPolyMat (ι := Lw n) (n + 1) (conjMat X) := by
  have h := ((isPolyMat_nbMat (n := n)).mul (isPolyMat_const (ι := Lw n) X 0)).mul
    (isPolyMat_nbMat_inv (n := n))
  have hdeg : 1 + 0 + n = n + 1 := by omega
  rw [hdeg] at h
  exact h

/-- The vector field of the noncompact formula. -/
def fieldW (X : Matrix (Fin n) (Fin n) ℂ) (v : Lw n → ℂ) : Lw n → ℂ :=
  lowCoords (lowMat (lowCoords (conjMat X v)) * nbMat v)

theorem coord_fieldW_mem (X : Matrix (Fin n) (Fin n) ℂ) (c : Lw n × Bool) :
    coord (Lw n) c ∘ fieldW X ∈ degLE (Lw n) (n + 2) := by
  have hlow : IsPolyMat (ι := Lw n) (n + 1) fun v => lowMat (lowCoords (conjMat X v)) := by
    intro a b
    by_cases h : b < a
    · have : (fun v : Lw n → ℂ => lowMat (lowCoords (conjMat X v)) a b) =
          fun v => conjMat X v a b := by
        funext v; simp [lowMat, lowCoords, h]
      rw [this]; exact isPolyMat_conjMat X a b
    · have : (fun v : Lw n → ℂ => lowMat (lowCoords (conjMat X v)) a b) = fun _ => 0 := by
        funext v; simp [lowMat, h]
      rw [this]; exact Submodule.zero_mem _
  have hM := hlow.mul (isPolyMat_nbMat (n := n))
  refine coord_comp_mem_degLE (fun p => ?_) c
  simpa [fieldW, lowCoords] using hM p.1.1 p.1.2

theorem re_mem_degLE {ι : Type*} [Fintype ι] {d : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι d) :
    (fun v => ((f v).re : ℂ)) ∈ degLE ι d := by
  have : (fun v => ((f v).re : ℂ)) = (2⁻¹ : ℂ) • (f + fun v => conj (f v)) := by
    funext v; simp [Complex.re_eq_add_conj]; ring
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hf (conj_mem_degLE hf))

theorem im_mem_degLE {ι : Type*} [Fintype ι] {d : ℕ} {f : (ι → ℂ) → ℂ} (hf : f ∈ degLE ι d) :
    (fun v => ((f v).im : ℂ)) ∈ degLE ι d := by
  have : (fun v => ((f v).im : ℂ)) = (2 * Complex.I)⁻¹ • (f - fun v => conj (f v)) := by
    funext v
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    rw [Complex.im_eq_sub_conj, div_eq_inv_mul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hf (conj_mem_degLE hf))

theorem torusDeriv_conjMat_mem (l : ℕ → ℤ) (t : ℕ → ℂ) (X : Matrix (Fin n) (Fin n) ℂ) :
    (fun v => torusDeriv l t (fun a => conjMat X v a a)) ∈ degLE (Lw n) (n + 1) := by
  have : (fun v => torusDeriv l t (fun a => conjMat X v a a)) = ∑ k : Fin n,
      (((l k : ℂ) * Complex.I) • (fun v => ((conjMat X v k k).im : ℂ)) +
        (2 * (t k + ((n : ℂ) - 1) / 2 - ((k : ℕ) : ℂ))) • fun v => ((conjMat X v k k).re : ℂ)) := by
    funext v; simp [torusDeriv, Finset.sum_apply, mul_assoc]
  rw [this]
  refine Submodule.sum_mem _ fun k _ => Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)
  · exact im_mem_degLE (isPolyMat_conjMat X k k)
  · exact re_mem_degLE (isPolyMat_conjMat X k k)

variable (χ : ℕ → ℂˣ → ℂ) {i r : Fin n} (hir : i ≠ r) (p q : ℕ)
  {κ : Type*} [Fintype κ] [DecidableEq κ] (T : κ → (Lw n → ℂ) → ℂ) (σ : κ → ℂ) (c : ℕ)

/-- Level `N` of the filtration. -/
def filtrationLevel (N : ℕ) : Submodule ℂ (Langlands.GeneralLinear n ℂ → ℂ) where
  carrier := {F | F ∈ principalSeries ℂ n χ ∧ IsBlockPoly hir p q F ∧
    ∃ P ∈ degLE (Lw n) (c * (N + 1)), ∀ v,
      F (nbUnit v) * (∏ m, T m v) ^ N = (∏ m, T m v ^ σ m) * P v}
  add_mem' {F G} hF hG := by
    obtain ⟨hF1, hF2, P, hP, hPe⟩ := hF
    obtain ⟨hG1, hG2, Q, hQ, hQe⟩ := hG
    refine ⟨Submodule.add_mem _ hF1 hG1, (blockPolySubmodule hir p q).add_mem hF2 hG2,
      P + Q, Submodule.add_mem _ hP hQ, fun v => ?_⟩
    simp only [Pi.add_apply, add_mul, mul_add, hPe, hQe]
  zero_mem' := ⟨Submodule.zero_mem _, (blockPolySubmodule hir p q).zero_mem, 0,
    Submodule.zero_mem _, fun v => by simp⟩
  smul_mem' a F hF := by
    obtain ⟨hF1, hF2, P, hP, hPe⟩ := hF
    refine ⟨Submodule.smul_mem _ a hF1, (blockPolySubmodule hir p q).smul_mem a hF2,
      a • P, Submodule.smul_mem _ a hP, fun v => ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, hPe]
    ring

variable {χ T}

omit [DecidableEq κ] in
theorem filtrationLevel_mono {e : ℕ} (hTdeg : ∀ m, T m ∈ degLE (Lw n) e)
    (hc : Fintype.card κ * e ≤ c) (N : ℕ) :
    filtrationLevel χ hir p q T σ c N ≤ filtrationLevel χ hir p q T σ c (N + 1) := by
  rintro F ⟨hF1, hF2, P, hP, hPe⟩
  refine ⟨hF1, hF2, P * fun v => ∏ m, T m v, ?_, fun v => ?_⟩
  · have hD : (fun v => ∏ m, T m v) ∈ degLE (Lw n) (Fintype.card κ * e) := by
      have := prod_mem_degLE (ι := Lw n) Finset.univ T (fun _ => e) fun m _ => hTdeg m
      have h' : (∏ m, T m) = fun v => ∏ m, T m v := by funext v; simp [Finset.prod_apply]
      rw [h'] at this
      simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using this
    exact degLE_mono (by nlinarith) (mul_mem_degLE hP hD)
  · simp only [Pi.mul_apply]
    rw [pow_succ, ← mul_assoc, hPe]
    ring

/-- **Right derivatives raise the level by one.** -/
theorem rightDerivative_mem_filtrationLevel (l : ℕ → ℤ) (t : ℕ → ℂ)
    (hχ : ∀ k z, χ k z = phase z ^ l k * ((‖(z : ℂ)‖ : ℂ)) ^ (2 * t k)) {e : ℕ}
    (hTdeg : ∀ m, T m ∈ degLE (Lw n) e) (hTpos : ∀ m, IsPosReal (T m))
    (hc : (n + 1) + (n + 2) + Fintype.card κ * e ≤ c) {N : ℕ}
    {F : Langlands.GeneralLinear n ℂ → ℂ} (hF : F ∈ filtrationLevel χ hir p q T σ c N)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    rightDerivative (matrixModel ℂ n) X F ∈ filtrationLevel χ hir p q T σ c (N + 1) := by
  obtain ⟨hF1, hF2, P, hP, hPe⟩ := hF
  have hFs := ((mem_principalSeries_iff ℂ n χ F).1 hF1).1
  refine ⟨rightDerivative_mem_principalSeries χ hF1 X,
    isBlockPoly_rightDerivative hir hFs hF2 X, ?_⟩
  -- the restriction to the lower unipotent group is differentiable
  set φ : (Lw n → ℂ) → ℂ := fun v => F (nbUnit v)
  have hφ : Differentiable ℝ φ := by
    intro v
    have hcomp : φ = unitsExtension F ∘ fun w => 1 + lowMatCLM w := by
      funext w
      simp only [φ, Function.comp_apply]
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + lowMatCLM w = (nbUnit w : Matrix _ _ ℂ) from rfl,
        unitsExtension_val]
    rw [hcomp]
    exact (differentiableAt_unitsExtension hFs (isUnit_nbMat v)).comp v
      ((lowMatCLM.differentiableAt).const_add 1)
  obtain ⟨P', hP', hP'e⟩ := exists_fderiv_weighted T hTdeg hTpos σ hφ hP hPe
    (coord_fieldW_mem X)
  set Λ : (Lw n → ℂ) → ℂ := fun v => torusDeriv l t (fun a => conjMat X v a a)
  have hΛ := torusDeriv_conjMat_mem l t X
  have hD : (fun v => ∏ m, T m v) ∈ degLE (Lw n) (Fintype.card κ * e) := by
    have := prod_mem_degLE (ι := Lw n) Finset.univ T (fun _ => e) fun m _ => hTdeg m
    have h' : (∏ m, T m) = fun v => ∏ m, T m v := by funext v; simp [Finset.prod_apply]
    rw [h'] at this
    simpa [Finset.sum_const, Finset.card_univ, smul_eq_mul] using this
  refine ⟨Λ * P * (fun v => ∏ m, T m v) + P', ?_, fun v => ?_⟩
  · refine Submodule.add_mem _ ?_ ?_
    · exact degLE_mono (by nlinarith) (mul_mem_degLE (mul_mem_degLE hΛ hP) hD)
    · exact degLE_mono (by nlinarith) hP'
  · have hform := rightDerivative_nbMat hF1 (principalSeriesCharacter_one l t hχ)
      (torusDeriv l t) (fun d y => fderiv_unitsExtension_diagonal_mul l t hχ hF1 d y) X v
    rw [hform]
    have h1 : fderiv ℝ (fun w => F (nbUnit w)) v
        (lowCoords (lowMat (lowCoords (nbMat v * X * (nbMat v)⁻¹)) * nbMat v)) *
          (∏ m, T m v) ^ (N + 1) = (∏ m, T m v ^ σ m) * P' v := hP'e v
    have h2 := hPe v
    simp only [Pi.add_apply, Pi.mul_apply, Λ, conjMat]
    linear_combination (torusDeriv l t (fun a => (nbMat v * X * (nbMat v)⁻¹) a a) *
      ∏ m, T m v) * h2 + h1

end Langlands.Archimedean.NoncompactPicture

import Langlands.Algebra.UnitaryDiscriminant.ChartChange
import Langlands.ClassFieldTheory.Local.CyclicClassAlgebra

/-! # The discriminant of a Hermitian matrix adjoint -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.UnitaryDiscriminant

open ClassFieldTheory.Local LinearAlgebra.UnitaryTwistedDescent BrauerComparison
open ClassFieldTheory.Local.CyclicClassAlgebra (cyclicUnitCocycle_apply)
open CentralSimple
open Matrix.GeneralLinearGroup (det)

variable {F L M : Type u} [Field F] [Field L] [Field M] [Algebra F L] [Algebra F M]
  [Algebra L M] [IsScalarTower F L M] [Algebra.IsQuadraticExtension F L]
  {ι : L ≃ₐ[F] L} (hι : ι ≠ 1)

open Classical in
/-- The quadratic character determined by the action on the center. -/
def centerCharacter : Gal(M/F) →* Multiplicative (ZMod 2) where
  toFun g := if g ∈ centerFixing F L M then 1 else Multiplicative.ofAdd 1
  map_one' := by simp
  map_mul' g h := by
    by_cases hg : g ∈ centerFixing F L M <;> by_cases hh : h ∈ centerFixing F L M
    · simp [mul_mem_centerFixing_iff hι, hg, hh]
    · simp [mul_mem_centerFixing_iff hι, hg, hh]
    · simp [mul_mem_centerFixing_iff hι, hg, hh]
    · simp only [mul_mem_centerFixing_iff hι, hg, hh, iff_self, ite_true, ite_false]
      decide

theorem centerCharacter_toAdd (g : Gal(M/F)) :
    (centerCharacter (M := M) hι g).toAdd = (by
      classical exact if g ∈ centerFixing F L M then 0 else 1) := by
  classical
  by_cases hg : g ∈ centerFixing F L M <;> simp [centerCharacter, hg]

theorem centerCharacter_injective :
    Function.Injective (centerCharacter (M := L) hι) := by
  apply (injective_iff_map_eq_one _).2
  intro g hg
  have hzero : (centerCharacter (M := L) hι g).toAdd = 0 := congrArg Multiplicative.toAdd hg
  rw [centerCharacter_toAdd] at hzero
  have hfix : g ∈ centerFixing F L L := by
    classical
    by_contra h
    exact one_ne_zero (by simpa only [h, ite_false] using hzero)
  exact AlgEquiv.ext ((mem_centerFixing.mp hfix))

private theorem cyclicCarry_centerCharacter (g h : Gal(M/F)) :
    cyclicCarry (centerCharacter hι g).toAdd (centerCharacter hι h).toAdd =
      (by classical exact if g ∉ centerFixing F L M ∧ h ∉ centerFixing F L M then 1 else 0) := by
  classical
  rw [centerCharacter_toAdd, centerCharacter_toAdd]
  by_cases hg : g ∈ centerFixing F L M <;> by_cases hh : h ∈ centerFixing F L M <;>
    simp [cyclicCarry, hg, hh] <;> decide

variable {B : Type u} [Ring B] [Algebra L B] {m : ℕ} {τ : B → B}
  (hτ : IsUnitaryInvolution ι τ)
  (e : M ⊗[L] B ≃ₐ[M] Matrix (Fin (2 * m)) (Fin (2 * m)) M)
  (f : B ≃ₐ[L] Matrix (Fin (2 * m)) (Fin (2 * m)) L)
  (H : GL (Fin (2 * m)) L)
  (hHerm : ((H : Matrix (Fin (2 * m)) (Fin (2 * m)) L).map ι)ᵀ = H)
  (hf : ∀ b, f (τ b) = ((H⁻¹ : GL (Fin (2 * m)) L) : Matrix _ _ L) *
    ((f b).map ι)ᵀ * (H : Matrix _ _ L))
  (d : Fˣ) (hd : algebraMap F L (d : F) = (-1 : L)^m * (det H : L))

include hHerm hf hd in
/-- For a Hermitian adjoint the relative discriminant is the quadratic carry class with
parameter the inverse signed determinant, inflated to the given splitting field. -/
theorem relativeDiscriminantClass_of_hermitian :
    relativeDiscriminantClass hι hτ e = cyclicClass F M (centerCharacter hι) d⁻¹ := by
  classical
  let N := Fin (2 * m)
  let J := centerFixing F L M
  let Q : GL N M := GeneralLinearGroup.map (algebraMap L M) H
  let P (g : Gal(M/F)) : GL N M := if g ∈ J then 1 else Q⁻¹
  let c (_ _ : Gal(M/F)) : Mˣ := 1
  let e' := splitPresentationChart (L := M) f
  have hmap_in (g : Gal(M/F)) (hg : g ∈ J) (X : Matrix N N L) :
      (X.map (algebraMap L M)).map g = X.map (algebraMap L M) := by
    ext i j
    exact (mem_centerFixing.mp hg) (X i j)
  have hmap_out (g : Gal(M/F)) (hg : g ∉ J) (X : Matrix N N L) :
      (X.map (algebraMap L M)).map g = (X.map ι).map (algebraMap L M) := by
    ext i j
    exact apply_algebraMap_of_not_mem hι hg (X i j)
  have hQ_in (g : Gal(M/F)) (hg : g ∈ J) :
      twistGL J g Q = Q := by
    rw [twistGL_of_mem hg]
    exact Units.ext (hmap_in g hg H)
  have hQ_out (g : Gal(M/F)) (hg : g ∉ J) :
      twistGL J g Q = Q⁻¹ := by
    rw [twistGL_of_not_mem hg]
    apply inv_injective
    apply Units.ext
    rw [coe_invTranspose_inv, inv_inv]
    change ((H.val.map (algebraMap L M)).map g)ᵀ = H.val.map (algebraMap L M)
    rw [hmap_out g hg, ← Matrix.transpose_map, hHerm]
  have hc (g h : Gal(M/F)) : P g * twistGL J g (P h) =
      GeneralLinearGroup.scalar N (c g h) * P (g * h) := by
    by_cases hg : g ∈ J <;> by_cases hh : h ∈ J
    · have hgh : g * h ∈ J := J.mul_mem hg hh
      simp [P, c, hg, hh, hgh, twistGL_of_mem hg]
    · have hgh : g * h ∉ J := by simpa only [J, mul_mem_centerFixing_iff hι, hg, hh] using
        (show ¬ (True ↔ False) by decide)
      simp [P, c, hg, hh, hgh, twistGL_inv, hQ_in g hg]
    · have hgh : g * h ∉ J := by simpa only [J, mul_mem_centerFixing_iff hι, hg, hh] using
        (show ¬ (False ↔ True) by decide)
      simp [P, c, hg, hh, hgh, twistGL_of_not_mem hg]
    · have hgh : g * h ∈ J := (mul_mem_centerFixing_iff hι g h).2 (iff_of_false hg hh)
      simp [P, c, hg, hh, hgh, twistGL_inv, hQ_out g hg]
  have hchart (b : B) : chartMap e' b = (f b).map (algebraMap L M) := by
    simp [chartMap_apply, e']
  have hin (g : Gal(M/F)) (hg : g ∈ J) (b : B) :
      twistedAct J P g (chartMap e' b) = chartMap e' b := by
    simp only [twistedAct_of_mem hg, hchart, hmap_in g hg, P, ite_eq_left hg, inv_one,
      Units.val_one, Matrix.one_mul, Matrix.mul_one]
  have hout (g : Gal(M/F)) (hg : g ∉ J) (b : B) :
      twistedAct J P g (chartMap e' b) = chartMap e' (τ b) := by
    simp only [twistedAct_of_not_mem hg, hchart, hmap_out g hg, P, ite_eq_right hg,
      inv_inv, hf, Matrix.map_mul]
    rfl
  have hdet (g : Gal(M/F)) (hg : g ∉ J) : g • det Q = det Q := by
    have h := det_twistGL (H := J) g Q
    rw [hQ_out g hg, twistUnit_of_not_mem hg, map_inv] at h
    exact (inv_injective h).symm
  have hdM : Units.map (algebraMap F M).toMonoidHom d = (-1 : Mˣ)^m * det Q := by
    apply Units.ext
    change algebraMap F M (d : F) = (-1 : M)^m * (det Q : M)
    rw [IsScalarTower.algebraMap_apply F L M, hd, map_mul, map_pow, map_neg, map_one]
    dsimp only [Q]
    rw [GeneralLinearGroup.map_det]
    rfl
  have heq (g h : Gal(M/F)) : Additive.ofMul (detCocycle J P c m g h) =
      cyclicUnitCocycle F M (centerCharacter hι) d⁻¹ (g, h) := by
    rw [cyclicUnitCocycle_apply, cyclicCarry_centerCharacter]
    by_cases hg : g ∈ J
    · rw [detCocycle_of_mem P c m hg]
      simp [c, J, hg]
      rfl
    · by_cases hh : h ∈ J
      · rw [detCocycle_of_not_mem_of_mem P c m hg hh]
        simp [c, P, J, hh]
        rfl
      · rw [detCocycle_of_not_mem_of_not_mem P c m hg hh]
        simp only [c, one_pow, one_mul, P, ite_eq_right hh, map_inv, smul_inv', hdet g hg]
        change Additive.ofMul ((det Q)⁻¹ * (-1 : Mˣ)^m) =
          (if g ∉ J ∧ h ∉ J then 1 else 0) • baseUnit F M d⁻¹
        simp only [hg, hh, not_false_eq_true, and_self, ite_true, baseUnit]
        apply congrArg Additive.ofMul
        rw [pow_one]
        change (det Q)⁻¹ * (-1 : Mˣ)^m = Units.map (algebraMap F M).toMonoidHom d⁻¹
        have hsign : ((-1 : Mˣ)⁻¹) = -1 := by
          apply Units.ext
          simp
        rw [map_inv, hdM, _root_.mul_inv_rev, ← inv_pow, hsign]
  rw [relativeDiscriminantClass_eq_of_chart hι hτ e e',
    ← relativeDiscriminantClass_eq_of_lifts hι hτ e' P c hin hout hc]
  unfold unitClass cyclicClass
  exact congrArg (groupCohomology.H2π _) (groupCohomology.cocycles₂_ext heq)

end Langlands.UnitaryDiscriminant

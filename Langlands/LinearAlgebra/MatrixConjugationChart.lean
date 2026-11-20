import Langlands.LinearAlgebra.MatrixConjugationConormal
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Local coordinates for matrix conjugation with transverse directions -/

noncomputable section

open Matrix
open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Split the infinitesimal conjugation map with a transverse complement containing `Z`. -/
theorem exists_matrixConjugationSplitting (C : Mat) (Z : Submodule ℝ Mat)
    (hZ : Disjoint Z (LinearMap.range (matrixConjugationTangent C))) :
    ∃ X Y : Mat →L[ℝ] Mat,
      (∀ w, matrixConjugationTangent C (X w) + Y w = w) ∧
      (∀ z ∈ Z, X z = 0 ∧ Y z = z) := by
  let L := matrixConjugationTangent C
  obtain ⟨W, hZW, hWT⟩ := hZ.exists_isCompl
  let P := (LinearMap.range L).prodEquivOfIsCompl W hWT.symm
  obtain ⟨J, hJ⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  have hJ' (t : LinearMap.range L) : L (J t) = t :=
    congrArg Subtype.val (LinearMap.congr_fun hJ t)
  let X : Mat →L[ℝ] Mat :=
    (J.comp ((LinearMap.fst ℝ (LinearMap.range L) W).comp P.symm.toLinearMap)).toContinuousLinearMap
  let Y : Mat →L[ℝ] Mat :=
    LinearMap.toContinuousLinearMap
      (W.subtype.comp ((LinearMap.snd ℝ (LinearMap.range L) W).comp P.symm.toLinearMap))
  refine ⟨X, Y, fun w => ?_, fun z hz => ?_⟩
  · change L (J (P.symm w).1) + ((P.symm w).2 : Mat) = w
    rw [hJ']
    exact P.apply_symm_apply w
  · have hP : P.symm z = (0, ⟨z, hZW hz⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right _ _ hWT.symm ⟨z, hZW hz⟩
    change J (P.symm z).1 = 0 ∧ ((P.symm z).2 : Mat) = z
    rw [hP]
    exact ⟨map_zero J, rfl⟩

/-- Affine conjugation of the transverse displacement of `C`. On the open set
where `1 + X w` is a unit, this is actual matrix conjugation by that unit. -/
def affineMatrixConjugation (C : Mat) (X Y : Mat →L[ℝ] Mat) (w : Mat) : Mat :=
  (1 + X w) * (C + Y w) * Ring.inverse (1 + X w)

@[simp]
theorem affineMatrixConjugation_zero (C : Mat) (X Y : Mat →L[ℝ] Mat) :
    affineMatrixConjugation C X Y 0 = C := by simp [affineMatrixConjugation]

theorem contDiffOn_affineMatrixConjugation (C : Mat) (X Y : Mat →L[ℝ] Mat) :
    ContDiffOn ℝ ∞ (affineMatrixConjugation C X Y) {w | IsUnit (1 + X w)} := by
  intro w hw
  obtain ⟨a, ha⟩ := hw
  have hX : ContDiff ℝ ∞ fun v => 1 + X v := contDiff_const.add X.contDiff
  have hY : ContDiff ℝ ∞ fun v => C + Y v := contDiff_const.add Y.contDiff
  have hi : ContDiffAt ℝ ∞ Ring.inverse (1 + X w) := ha ▸ contDiffAt_ringInverse ℝ a
  exact ((hX.contDiffAt.mul hY.contDiffAt).mul (hi.comp w hX.contDiffAt)).contDiffWithinAt

theorem hasFDerivAt_affineMatrixConjugation_zero (C : Mat) (X Y : Mat →L[ℝ] Mat)
    (h : ∀ w, matrixConjugationTangent C (X w) + Y w = w) :
    HasFDerivAt (affineMatrixConjugation C X Y) (1 : Mat →L[ℝ] Mat) 0 := by
  have hX : HasFDerivAt (fun w => 1 + X w) X 0 := X.hasFDerivAt.const_add 1
  have hY : HasFDerivAt (fun w => C + Y w) Y 0 := Y.hasFDerivAt.const_add C
  have hI : HasFDerivAt Ring.inverse (-(1 : Mat →L[ℝ] Mat)) (1 : Mat) := by
    have he : ContinuousLinearMap.mulLeftRight ℝ Mat (1 : Mat) (1 : Mat) =
        (1 : Mat →L[ℝ] Mat) := by
      ext1 w
      simp [ContinuousLinearMap.mulLeftRight_apply]
    simpa only [inv_one, Units.val_one, he] using
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : Matˣ))
  have hR : HasFDerivAt (fun w => Ring.inverse (1 + X w)) (-X) 0 := by
    have hI' : HasFDerivAt Ring.inverse (-(1 : Mat →L[ℝ] Mat)) ((fun w => 1 + X w) 0) := by
      simpa only [map_zero, add_zero] using hI
    have he : (-(1 : Mat →L[ℝ] Mat)).comp X = -X := by ext1; rfl
    simpa only [he, Function.comp_def] using hI'.comp 0 hX
  refine ((hX.fun_mul' hY).fun_mul' hR).congr_fderiv ?_
  ext1 w
  simp only [map_zero, add_zero, one_mul, Ring.inverse_one, _root_.add_apply, _root_.neg_apply,
    _root_.smul_apply, smul_eq_mul, op_smul_eq_mul, one_smul, mul_one, mul_neg, one_apply_eq_self]
  simpa only [matrixConjugationTangent_apply, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    using h w

/-- A linear splitting of the infinitesimal conjugation map gives a smooth local
coordinate chart with the affine conjugation formula. -/
theorem exists_affineMatrixConjugationChart (C : Mat) (X Y : Mat →L[ℝ] Mat)
    (h : ∀ w, matrixConjugationTangent C (X w) + Y w = w) :
    ∃ e : OpenPartialHomeomorph Mat Mat,
      (e : Mat → Mat) = affineMatrixConjugation C X Y ∧ 0 ∈ e.source ∧ e 0 = C ∧
      (∀ w ∈ e.source, IsUnit (1 + X w)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target := by
  let f := affineMatrixConjugation C X Y
  let V : Set Mat := {w | IsUnit (1 + X w)}
  have hV : IsOpen V := Units.isOpen.preimage (continuous_const.add X.continuous)
  have hV₀ : (0 : Mat) ∈ V := by simp [V]
  have hf : ContDiffOn ℝ ∞ f V := contDiffOn_affineMatrixConjugation C X Y
  have hfa : ContDiffAt ℝ ∞ f 0 := hf.contDiffAt (hV.mem_nhds hV₀)
  have hd : HasFDerivAt f ((ContinuousLinearEquiv.refl ℝ Mat : Mat ≃L[ℝ] Mat) :
      Mat →L[ℝ] Mat) 0 := hasFDerivAt_affineMatrixConjugation_zero C X Y h
  let p := hfa.toOpenPartialHomeomorph f hd (by simp)
  let W := V ∩ (fderiv ℝ f) ⁻¹' {L : Mat →L[ℝ] Mat | IsUnit L}
  have hW : IsOpen W :=
    (hf.continuousOn_fderiv_of_isOpen hV (by norm_num)).isOpen_inter_preimage hV Units.isOpen
  have hW₀ : (0 : Mat) ∈ W := by
    refine ⟨hV₀, ?_⟩
    change IsUnit (fderiv ℝ f 0)
    rw [hd.fderiv]
    exact isUnit_one
  let e := p.restrOpen W hW
  have he₀ : (0 : Mat) ∈ e.source :=
    ⟨hfa.mem_toOpenPartialHomeomorph_source hd (by simp), hW₀⟩
  have hew : ∀ w ∈ e.source, w ∈ W := fun _ hw => hw.2
  refine ⟨e, rfl, he₀, affineMatrixConjugation_zero C X Y, fun w hw => (hew w hw).1,
    hf.mono (fun w hw => (hew w hw).1), ?_⟩
  intro z hz
  have hw := hew _ (e.map_target hz)
  have hfw : ContDiffAt ℝ ∞ f (e.symm z) := hf.contDiffAt (hV.mem_nhds hw.1)
  have hu : IsUnit (fderiv ℝ f (e.symm z)) := hw.2
  obtain ⟨u, hu⟩ := hu
  have hdu : HasFDerivAt e ((ContinuousLinearEquiv.ofUnit u : Mat ≃L[ℝ] Mat) : Mat →L[ℝ] Mat)
      (e.symm z) := by
    change HasFDerivAt f (u : Mat →L[ℝ] Mat) (e.symm z)
    rw [hu]
    exact (hfw.differentiableAt (by simp)).hasFDerivAt
  exact (e.contDiffAt_symm hz hdu hfw).contDiffWithinAt

end Langlands

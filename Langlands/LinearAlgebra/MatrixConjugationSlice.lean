import Langlands.LinearAlgebra.MatrixConjugationChart
import Langlands.LinearAlgebra.NearbyMatrixIntertwiner
import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-! # Transverse slices for real matrix conjugation -/

noncomputable section

open scoped ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Conjugate a point of the affine slice by a unit close to the identity. -/
def matrixSliceConjugation (C : Mat) {T W : Submodule ℝ Mat} (J : T →L[ℝ] Mat)
    (p : T × W) : Mat :=
  (1 + J p.1) * (C + p.2) * Ring.inverse (1 + J p.1)

/-- Product coordinates for a prescribed transverse complement. A nearby pair consisting of a
slice point and a matrix of sufficiently small intertwining rank has the prescribed slice
coordinate in this chart. -/
theorem exists_matrixConjugationSlice (C : Mat) (W : Submodule ℝ Mat)
    (hW : IsCompl (LinearMap.range (matrixConjugationTangent C)) W) :
    ∃ (J : (LinearMap.range (matrixConjugationTangent C)) →L[ℝ] Mat)
      (e : OpenPartialHomeomorph ((LinearMap.range (matrixConjugationTangent C)) × W) Mat)
      (U : Set (Mat × Mat)),
      (∀ t : LinearMap.range (matrixConjugationTangent C), matrixConjugationTangent C (J t) = t) ∧
      (e : _ → Mat) = matrixSliceConjugation C J ∧
      0 ∈ e.source ∧ e 0 = C ∧ (∀ p ∈ e.source, IsUnit (1 + J p.1)) ∧
      ContDiffOn ℝ ∞ e e.source ∧ ContDiffOn ℝ ∞ e.symm e.target ∧
      IsOpen U ∧ (C, C) ∈ U ∧
      ∀ (w : W) (B : Mat), (C + (w : Mat), B) ∈ U →
        Module.finrank ℝ (LinearMap.range (matrixIntertwinerMap (C + (w : Mat)) B).toLinearMap) ≤
          Module.finrank ℝ (LinearMap.range (matrixConjugationTangent C)) →
        B ∈ e.target ∧ (e.symm B).2 = w := by
  let L := matrixConjugationTangent C
  let T := LinearMap.range L
  obtain ⟨j, hj⟩ := L.rangeRestrict.exists_rightInverse_of_surjective L.range_rangeRestrict
  let J : T →L[ℝ] Mat := j.toContinuousLinearMap
  have hJ (t : T) : L (J t) = t := congrArg Subtype.val (LinearMap.congr_fun hj t)
  let E : (T × W) ≃L[ℝ] Mat := (T.prodEquivOfIsCompl W hW).toContinuousLinearEquiv
  let X : Mat →L[ℝ] Mat := J.comp ((ContinuousLinearMap.fst ℝ T W).comp E.symm.toContinuousLinearMap)
  let Y : Mat →L[ℝ] Mat := W.subtypeL.comp ((ContinuousLinearMap.snd ℝ T W).comp E.symm.toContinuousLinearMap)
  have hsplit (w : Mat) : L (X w) + Y w = w := by
    change L (J (E.symm w).1) + ((E.symm w).2 : Mat) = w
    rw [hJ]
    exact E.apply_symm_apply w
  obtain ⟨a, ha, ha₀, haC, haunit, haf, hai⟩ := exists_affineMatrixConjugationChart C X Y hsplit
  let e := E.toHomeomorph.transOpenPartialHomeomorph a
  have hX (p : T × W) : X (E p) = J p.1 := by
    change J (E.symm (E p)).1 = J p.1
    rw [E.symm_apply_apply]
  have hY (p : T × W) : Y (E p) = p.2 := by
    change ((E.symm (E p)).2 : Mat) = p.2
    rw [E.symm_apply_apply]
  have hf : (e : T × W → Mat) = matrixSliceConjugation C J := by
    funext p
    change a (E p) = _
    rw [ha]
    simp only [affineMatrixConjugation, hX, hY, matrixSliceConjugation]
  have he₀ : 0 ∈ e.source := by
    change E 0 ∈ a.source
    rwa [map_zero]
  have heC : e 0 = C := by
    change a (E 0) = C
    rwa [map_zero]
  have hunit (p : T × W) (hp : p ∈ e.source) : IsUnit (1 + J p.1) := by
    rw [← hX p]
    exact haunit (E p) hp
  have hforward : ContDiffOn ℝ ∞ e e.source :=
    haf.comp_continuousLinearMap E.toContinuousLinearMap
  have hbackward : ContDiffOn ℝ ∞ e.symm e.target :=
    hai.continuousLinearMap_comp E.symm.toContinuousLinearMap
  obtain ⟨V, g, hV, hV₀, hg₀, hg, hcorr, hsolve⟩ := exists_smooth_nearbyMatrixIntertwiner C J hJ
  let r : Mat →L[ℝ] T := L.rangeRestrict.toContinuousLinearMap
  let c (p : Mat × Mat) : T × W := (r (g p - 1), (E.symm (p.1 - C)).2)
  have hc : ContinuousOn c V :=
    (r.continuous.comp_continuousOn (hg.continuousOn.sub continuousOn_const)).prodMk
      ((continuous_snd.comp (E.symm.continuous.comp (continuous_fst.sub continuous_const))).continuousOn)
  have hc₀ : c (C, C) = 0 := by simp [c, hg₀]
  let U := V ∩ c ⁻¹' e.source
  refine ⟨J, e, U, hJ, hf, he₀, heC, hunit, hforward, hbackward,
    hc.isOpen_inter_preimage hV e.open_source, ⟨hV₀, ?_⟩, ?_⟩
  · change c (C, C) ∈ e.source
    rwa [hc₀]
  intro w B hp hrank
  let p := (C + (w : Mat), B)
  have hpV : p ∈ V := hp.1
  have hpc : c p ∈ e.source := hp.2
  obtain ⟨hu, hEq⟩ := hsolve p hpV
  obtain ⟨u, hu⟩ := hu
  have hc₁ : 1 + J (c p).1 = g p := by
    obtain ⟨t, ht⟩ := hcorr p
    change J t = g p - 1 at ht
    have hrt : r (J t) = t := Subtype.ext (hJ t)
    change 1 + J (r (g p - 1)) = g p
    rw [← ht, hrt, ht]
    abel
  have hc₂ : (c p).2 = w := by
    change (E.symm (C + (w : Mat) - C)).2 = w
    rw [add_sub_cancel_left]
    exact congrArg Prod.snd (Submodule.prodEquivOfIsCompl_symm_apply_right T W hW w)
  have hEp : e (c p) = B := by
    rw [hf, matrixSliceConjugation, hc₁, hc₂, ← hu, Ring.inverse_unit]
    change (u : Mat) * p.1 * (↑u⁻¹ : Mat) = B
    rw [hu, hEq hrank, ← hu]
    simp [p, mul_assoc]
  have hB : B ∈ e.target := hEp ▸ e.map_source hpc
  exact ⟨hB, by rw [← hEp, e.left_inv hpc, hc₂]⟩

end Langlands

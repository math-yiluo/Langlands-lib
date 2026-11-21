import Langlands.Representation.Archimedean.RealCartanAngularFrame
import Langlands.Representation.Archimedean.RealCartanArgumentJacobian
import Langlands.Representation.Archimedean.RealLeviSlices

/-! # Differential of the angular Levi frame -/

noncomputable section

open Matrix
open scoped Matrix.Norms.Operator ContDiff

namespace Langlands.Archimedean.RealCartanAngularDifferential

open RealCartanAngularFrame RealSmallOrthogonalHaar RealCartanPeakTest RealCartanLowerCoordinates
  RealCartanArgumentJacobian RealBlockRotation RealLeviChart RealLeviSlices RealLeviCompactChart
  RealLeviParabolicIntegration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "M" n:max => Matrix (Fin n) (Fin n) ℝ
local notation "L" n:max => (LowerIndex n → ℝ)

private def lowerTwo : LowerIndex 2 := pairLower rfl

private theorem lowerTwo_eq : lowerTwo.1 = (1, 0) := rfl

private theorem eq_lowerTwo (p : LowerIndex 2) : p = lowerTwo := by
  have hp := p.2
  apply Subtype.ext
  rw [lowerTwo_eq]
  apply Prod.ext <;> apply Fin.ext
  · change p.1.1.val = 1
    omega
  · change p.1.2.val = 0
    omega

private theorem angularBlock_matrix_two : (fun z : L 2 => (angularBlock 2 z : M 2)) =
    fun z => rotMatrix (by decide : 0 + 1 < 2) (z lowerTwo) := by
  funext z
  rw [angularBlock_two]
  exact blockRotation_val_eq (by decide) (z lowerTwo)

private theorem contDiff_angularBlock_matrix (n : ℕ) (hn : n = 1 ∨ n = 2) :
    ContDiff ℝ ∞ (fun z : L n => (angularBlock n z : M n)) := by
  rcases hn with h | h
  · subst n
    have he (z : L 1) : (angularBlock 1 z : M 1) = 1 := by rw [angularBlock_one]; rfl
    simp_rw [he]
    exact contDiff_const
  · subst n
    rw [angularBlock_matrix_two]
    let e : L 2 →L[ℝ] ℝ := ContinuousLinearMap.proj lowerTwo
    exact (contDiff_const.add (((Real.contDiff_cos.comp e.contDiff).sub contDiff_const).smul
      contDiff_const)).add ((Real.contDiff_sin.comp e.contDiff).smul contDiff_const)

private theorem hasFDerivAt_angularBlock_matrix (n : ℕ) (hn : n = 1 ∨ n = 2) :
    HasFDerivAt (fun z : L n => (angularBlock n z : M n)) (skewLower n) 0 := by
  rcases hn with h | h
  · subst n
    have hz (z : L 1) : z = 0 := by
      ext p
      have := p.2
      omega
    have he (z : L 1) : (angularBlock 1 z : M 1) = 1 := by rw [angularBlock_one]; rfl
    simp_rw [he]
    refine (hasFDerivAt_const (c := (1 : M 1)) (0 : L 1)).congr_fderiv ?_
    exact ContinuousLinearMap.ext fun z => by rw [hz z, map_zero, map_zero]
  · subst n
    rw [angularBlock_matrix_two]
    let e : L 2 →L[ℝ] ℝ := ContinuousLinearMap.proj lowerTwo
    have h : HasDerivAt (rotMatrix (by decide : 0 + 1 < 2)) (rotationGenerator 2 0) (e 0) := by
      rw [map_zero]
      simpa [rotMatrix] using hasDerivAt_rotMatrix (by decide : 0 + 1 < 2) 0
    refine (h.hasFDerivAt.comp 0 e.hasFDerivAt).congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro z
    change z lowerTwo • rotationGenerator 2 0 = skewLower 2 z
    ext p q
    rw [skewLower_apply, rotationGenerator_eq (by decide : 0 + 1 < 2)]
    fin_cases p <;> fin_cases q <;> simp [ia, ib, eq_lowerTwo]

section Frame

variable {c : ℕ} (sz : Fin c → ℕ)
local notation "N" => ∑ i, sz i
local notation "ZSpace" => (WithinIndex sz → ℝ)

/-- The angular variation in the full compact group. -/
def angularMatrix (Z : ZSpace) : K N := blockFrame sz (angularFrame sz Z)

@[simp]
theorem angularMatrix_zero : angularMatrix sz 0 = 1 := by
  rw [angularMatrix, angularFrame_zero, map_one]

theorem continuous_angularMatrix : Continuous (angularMatrix sz) :=
  (continuous_blockFrame sz).comp (continuous_angularFrame sz)

private def blockCoords (i : Fin c) : ZSpace →L[ℝ] L (sz i) :=
  ContinuousLinearMap.pi fun p => ContinuousLinearMap.proj (withinAt sz i p)

private def glueBlocks : (∀ i, M (sz i)) →L[ℝ] M N :=
  (blockDiagLin sz).toContinuousLinearMap

private theorem angularMatrix_val (Z : ZSpace) : (angularMatrix sz Z : M N) =
    glueBlocks sz (fun i => (angularBlock (sz i) (blockCoords sz i Z) : M (sz i))) := rfl

private theorem glueBlocks_skew (Z : ZSpace) :
    glueBlocks sz (fun i => skewLower (sz i) (blockCoords sz i Z)) = interiorSkew sz Z := by
  let f := fun i => skewLower (sz i) (blockCoords sz i Z)
  change blockDiagHom sz f = _
  have hskew : (blockDiagHom sz f)ᵀ = -(blockDiagHom sz f) := by
    rw [blockDiagHom_transpose, ← map_neg]
    congr 1
    funext i
    exact transpose_skewLower _
  rw [← skewLower_lowerProjection hskew, interiorSkew_apply]
  congr 1
  funext p
  obtain ⟨q, rfl⟩ := (lowerIndexEquiv sz).surjective p
  cases q with
  | inl q =>
    rw [joinLower_apply_off, lowerProjection_apply, lowerIndexEquiv_inl]
    change blockDiagHom sz f q.1.1 q.1.2 = 0
    obtain ⟨a, ha⟩ := pos_cls sz q.1.1
    obtain ⟨b, hb⟩ := pos_cls sz q.1.2
    rw [← ha, ← hb, blockDiagHom_pos_pos_of_ne sz f (ne_of_gt q.2)]
  | inr q =>
    obtain ⟨⟨i, p⟩, rfl⟩ := (withinEquivSigma sz).surjective q
    rw [withinEquivSigma_apply, joinLower_apply_within, lowerProjection_apply, lowerIndexEquiv_inr]
    change blockDiagHom sz f (pos sz i p.1.1) (pos sz i p.1.2) = Z (withinAt sz i p)
    rw [blockDiagHom_pos_pos_self]
    exact congrFun (lowerProjection_skewLower (blockCoords sz i Z)) p

/-- The within-block angles are smooth and have exactly the within-block skew derivative. -/
def RealCartanAngularDifferentialStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ), (∀ i, sz i = 1 ∨ sz i = 2) →
    ContDiff ℝ ∞ (fun Z => (angularMatrix sz Z : M (∑ i, sz i))) ∧
      HasFDerivAt (fun Z => (angularMatrix sz Z : M (∑ i, sz i))) (interiorSkew sz) 0

theorem realCartanAngularDifferential : RealCartanAngularDifferentialStatement := by
  intro c sz hsize
  simp only [angularMatrix_val]
  let B (i : Fin c) (Z : WithinIndex sz → ℝ) := (angularBlock (sz i) (blockCoords sz i Z) : M (sz i))
  have hc : ContDiff ℝ ∞ (fun Z i => B i Z) := contDiff_pi.mpr fun i =>
    (contDiff_angularBlock_matrix _ (hsize i)).comp (blockCoords sz i).contDiff
  let D (i : Fin c) := (skewLower (sz i)).comp (blockCoords sz i)
  have hD : HasFDerivAt (fun Z i => B i Z) (ContinuousLinearMap.pi D) 0 :=
    hasFDerivAt_pi.mpr fun i => by
      have h : HasFDerivAt (fun z : L (sz i) => (angularBlock (sz i) z : M (sz i)))
          (skewLower (sz i)) (blockCoords sz i 0) := by
        rw [map_zero]
        exact hasFDerivAt_angularBlock_matrix _ (hsize i)
      exact h.comp 0 (blockCoords sz i).hasFDerivAt
  refine ⟨(glueBlocks sz).contDiff.comp hc, ?_⟩
  refine ((glueBlocks sz).hasFDerivAt.comp 0 hD).congr_fderiv ?_
  exact ContinuousLinearMap.ext (glueBlocks_skew sz)

end Frame

end Langlands.Archimedean.RealCartanAngularDifferential

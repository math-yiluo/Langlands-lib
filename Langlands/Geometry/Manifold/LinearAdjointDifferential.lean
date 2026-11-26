import Langlands.Geometry.Manifold.SmoothGroupConjugationLie
import Langlands.Geometry.Manifold.MatrixCoefficientLie
import Mathlib.Analysis.Calculus.MeanValue

/-! # Differentiating the adjoint action through a linear representation -/

noncomputable section

open scoped Manifold ContDiff

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Geometry.Manifold.LinearAdjoint

open MatrixCoefficientLie

variable {E G A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace G] [ChartedSpace E G] [Group G] [LieGroup 𝓘(ℝ, E) ∞ G]
  [NormedRing A] [NormedAlgebra ℝ A]

local notation "MI" => 𝓘(ℝ, E)
local notation "L" => GroupLieAlgebra MI G

/-- The differential at the identity of a linear realization. -/
def tangent (r : G →* A) : L →L[ℝ] A := mvfderiv MI (fun g => r g) 1

variable (r : G →* A)
variable (hr : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, A) ∞ (fun g : G => r g))

include hr

local instance : ContMDiffMul 𝓘(ℝ, A) ∞ A := by
  constructor
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (contDiff_fst.mul contDiff_snd).contMDiff

omit [CompleteSpace E] [LieGroup MI ∞ G] in
private theorem contMDiff_test (a b : A) (l : A →L[ℝ] ℂ) :
    ContMDiff MI 𝓘(ℝ, ℂ) ∞ (fun g => l (a * r g * b)) :=
  (l.comp (ContinuousLinearMap.mulLeftRight ℝ A a b)).contDiff.contMDiff.comp hr

omit [CompleteSpace E] [LieGroup MI ∞ G] in
private theorem tangent_test (a b : A) (l : A →L[ℝ] ℂ) (x : G) (X : L) :
    groupDirectionalValue MI X (fun g => l (a * r g * b)) x =
      l ((a * r x) * tangent r X * b) := by
  unfold groupDirectionalValue
  simp only [map_mul, ← mul_assoc a]
  exact mvfderiv_clm_comp MI (hr.mdifferentiableAt (by simp))
    (l.comp (ContinuousLinearMap.mulLeftRight ℝ A (a * r x) b)) X

/-- The differential preserves the Lie bracket, computed as a commutator in the ambient algebra. -/
theorem tangent_lie (X Y : L) :
    tangent r ⁅X, Y⁆ = tangent r X * tangent r Y - tangent r Y * tangent r X := by
  apply (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).mpr
  intro l
  let c := Complex.ofRealCLM.comp l
  have h := groupDirectionalValue_commutator_of_vectorFieldCommutator MI
    (smoothVectorFieldCommutator_proof (I := MI) (M := G)) X Y
    (contMDiff_test r hr 1 1 c) 1
  have htest (Z : L) (a b : A) :
      groupDirectionalValue MI Z (fun g => c (a * r g * b)) =
        fun x => c (a * r x * (tangent r Z * b)) := by
    funext x
    rw [tangent_test r hr, mul_assoc (a * r x)]
  rw [htest, htest, htest, htest, htest] at h
  simp only [map_one, one_mul, mul_one] at h
  apply Complex.ofReal_injective
  simpa only [c, map_sub, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_sub] using h

omit [CompleteSpace E] in
/-- Tangent conjugation is computed by conjugating the realized tangent vector. -/
theorem tangent_conjugation (g : G) (X : L) :
    tangent r (groupTangentConjugation MI g X) = r g * tangent r X * r g⁻¹ := by
  let f : G → G := fun h => g * h * g⁻¹
  have hf : MDifferentiableAt MI MI f (1 : G) := mdifferentiableAt_conjugation MI g 1
  have he : f 1 = 1 := by simp [f]
  have hc := mvfderiv_comp_apply_of_eq (I := MI) (I' := MI)
    (g := fun h => r h) (f := f) (1 : G)
    (hr.mdifferentiableAt (by simp) (x := (1 : G))) hf he X
  have htest : (fun h => r (f h)) =
      fun h => (ContinuousLinearMap.mulLeftRight ℝ A (r g) (r g⁻¹)) (r h) := by
    funext h
    simp [f]
  change mvfderiv MI (fun h => r (f h)) 1 X = tangent r (groupTangentConjugation MI g X) at hc
  rw [htest] at hc
  exact hc.symm.trans (mvfderiv_clm_comp MI (hr.mdifferentiableAt (by simp))
    (ContinuousLinearMap.mulLeftRight ℝ A (r g) (r g⁻¹)) X)

omit hr [CompleteSpace E] [Group G] [LieGroup MI ∞ G] in
/-- A scalar test of a product can be differentiated using the bilinear product rule. -/
private theorem mvfderiv_mul_apply {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    {f g : G → A} {x : G} (hf : MDifferentiableAt MI 𝓘(ℝ, A) f x)
    (hg : MDifferentiableAt MI 𝓘(ℝ, A) g x) (l : A →L[ℝ] B) (X : TangentSpace MI x) :
    mvfderiv MI (fun t => l (f t * g t)) x X =
      l ((mvfderiv MI f x X) * g x + f x * (mvfderiv MI g x X)) := by
  have hp := (hasFDerivAt_fst (𝕜 := ℝ) (p := (f x, g x))).mul'
    (hasFDerivAt_snd (𝕜 := ℝ) (p := (f x, g x)))
  have hl := l.hasFDerivAt.comp (f x, g x) hp
  have hF : MDifferentiableAt MI 𝓘(ℝ, A × A) (fun t => (f t, g t)) x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hf.prodMk hg
  have hd := mvfderiv_comp_apply (I := 𝓘(ℝ, A × A)) (I' := MI)
    (g := fun p : A × A => l (p.1 * p.2)) (f := fun t : G => (f t, g t)) x
    hl.differentiableAt.mdifferentiableAt hF X
  change mvfderiv MI (fun t => l (f t * g t)) x X = _ at hd
  rw [hd, mvfderiv_eq_fderiv, show (fun p : A × A => l (p.1 * p.2)) =
    (l : A → B) ∘ (Prod.fst * Prod.snd) from rfl, hl.fderiv]
  have hproj (Q : A × A →L[ℝ] A) := mvfderiv_clm_comp MI hF Q X
  have ha := hproj (ContinuousLinearMap.fst ℝ A A)
  have hb := hproj (ContinuousLinearMap.snd ℝ A A)
  change mvfderiv MI f x X = (mvfderiv MI (fun t => (f t, g t)) x X).1 at ha
  change mvfderiv MI g x X = (mvfderiv MI (fun t => (f t, g t)) x X).2 at hb
  change l (f x * (mvfderiv MI (fun t => (f t, g t)) x X).2 +
    (mvfderiv MI (fun t => (f t, g t)) x X).1 * g x) = _
  rw [← ha, ← hb]
  exact congrArg l (add_comm _ _)

omit [CompleteSpace E] in
private theorem tangent_inverse (Y : L) : mvfderiv MI (fun g => r (g⁻¹)) 1 Y = -tangent r Y := by
  have hi : MDifferentiableAt MI 𝓘(ℝ, A) (fun g => r (g⁻¹)) (1 : G) :=
    (hr.comp (contMDiff_inv MI ∞)).mdifferentiableAt (by simp)
  have h := mvfderiv_mul_apply (hr.mdifferentiableAt (by simp)) hi
    (ContinuousLinearMap.id ℝ A) Y
  simp only [← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.id_apply,
    mvfderiv_const, zero_apply, inv_one, mul_one, one_mul] at h
  exact eq_neg_of_add_eq_zero_right h.symm

variable (P : A →L[ℝ] E)
variable (hP : ∀ X : GroupLieAlgebra 𝓘(ℝ, E) G, P (tangent r X) = X)

include r P hP


omit [CompleteSpace E] in
/-- A linear left inverse gives a formula for the tangent action on the model. -/
theorem conjugation_eq (X : L) (g : G) :
    groupTangentConjugation MI g X = P (r g * tangent r X * r g⁻¹) := by
  rw [← tangent_conjugation r hr, hP]

omit [CompleteSpace E] in
/-- A tangent adjoint orbit is smooth in the linear realization. -/
theorem contMDiff_conjugation_apply (X : L) :
    ContMDiff (M' := E) MI MI ∞ (fun g => groupTangentConjugation MI g X) := by
  have heq : (fun g : G => (show E from groupTangentConjugation MI g X)) =
      (fun g : G => P (r g * tangent r X * r g⁻¹)) :=
    funext (conjugation_eq r hr P hP X)
  rw [heq]
  exact P.contDiff.contMDiff.comp ((hr.mul contMDiff_const).mul (hr.comp (contMDiff_inv MI ∞)))

/-- Differentiation at the identity of the adjoint action gives the Lie bracket. -/
theorem mfderiv_conjugation_apply (X Y : L) :
    mvfderiv (F := E) MI (fun g => groupTangentConjugation MI g X) 1 Y = ⁅Y, X⁆ := by
  have heq : (fun g : G => (show E from groupTangentConjugation MI g X)) =
      (fun g : G => P (r g * tangent r X * r g⁻¹)) :=
    funext (conjugation_eq r hr P hP X)
  rw [heq]
  have hsm : ContMDiff MI 𝓘(ℝ, A) ∞ (fun g => r g * tangent r X) := hr.mul contMDiff_const
  have h1 : mvfderiv MI (fun g => r g * tangent r X) 1 Y = tangent r Y * tangent r X := by
    simpa only [ContinuousLinearMap.mulLeftRight_apply, one_mul, tangent] using
      mvfderiv_clm_comp MI (hr.mdifferentiableAt (by simp))
        (ContinuousLinearMap.mulLeftRight ℝ A 1 (tangent r X)) Y
  have hi : MDifferentiableAt MI 𝓘(ℝ, A) (fun g => r (g⁻¹)) (1 : G) :=
    (hr.comp (contMDiff_inv MI ∞)).mdifferentiableAt (by simp)
  have hd := mvfderiv_mul_apply (hsm.mdifferentiableAt (by simp)) hi P Y
  rw [h1, tangent_inverse r hr, inv_one, map_one, mul_one, one_mul, mul_neg,
    ← sub_eq_add_neg, ← tangent_lie r hr, hP] at hd
  exact hd

end Langlands.Geometry.Manifold.LinearAdjoint

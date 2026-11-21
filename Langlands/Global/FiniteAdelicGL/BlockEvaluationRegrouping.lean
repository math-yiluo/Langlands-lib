import Langlands.Global.FiniteAdelicGL.BlockParabolicCoefficientAction

/-! # Finite adelic evaluation with coefficients grouped by Levi blocks -/

noncomputable section

open scoped Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 80000

universe u v

namespace Langlands.Global.FiniteAdelicGL.BlockInducedReferences

open GeneralLinear AdelicBlockParabolic AdelicBlockDeterminantCharacter RestrictedTensor

variable {F : Type u} [Field F] [NumberField F] {n : ℕ} {B : BlockShape n}
variable {V : FinitePlace F → Fin B.length → Type v}
variable [∀ w i, AddCommGroup (V w i)] [∀ w i, Module ℂ (V w i)]
variable {σ : ∀ w i, Representation ℂ (FiniteLocalGL F (B.size i) w) (V w i)}
variable (D : BlockInducedReferences F B σ)
variable (hD : ∀ w ∉ D.exceptional, ∀ i, D.blockReference w i ≠ 0)

local notation "Gf" => FiniteAdelicGL F n
local notation "Q" => D.parabolicCoefficientEquiv hD

include hD in
private theorem coefficientReference_nonzero (w : FinitePlace F)
    (hw : w ∉ D.exceptional) : D.coefficientReference w ≠ 0 := by
  choose φ hφ using fun i : Fin B.length =>
    Module.Projective.exists_dual_eq_one ℂ (hD w hw i)
  let f := PiTensorProduct.lift ((MultilinearMap.mkPiAlgebra ℂ (Fin B.length) ℂ).compLinearMap φ)
  have hf : f (PiTensorProduct.tprod ℂ (D.blockReference w)) = 1 := by simp [f, hφ]
  intro hz
  change PiTensorProduct.tprod ℂ (D.blockReference w) = 0 at hz
  exact zero_ne_one ((map_zero f).symm.trans ((congrArg f hz).symm.trans hf))

/-- Pointwise evaluation expressed in the indexed tensor of the actual
restricted Levi block coefficients. -/
def blockEvaluation (g : Gf) : D.Source →ₗ[ℂ] (⨂[ℂ] i, D.BlockCoefficients i) :=
  (Q).toLinearEquiv.toLinearMap.comp (D.evaluationAt g)

theorem blockEvaluation_right (d g : Gf) (a : D.Source) :
    D.blockEvaluation hD g (D.sourceRepresentation d a) = D.blockEvaluation hD (g * d) a :=
  congrArg Q (LinearMap.congr_fun (D.evaluationAt_comp_sourceRepresentation g d) a)

/-- The parabolic acts on the regrouped evaluation by the actual adelic half
character and by its finite Levi projection on the individual block factors. -/
theorem blockEvaluation_parabolic (p : Finite F B) (g : Gf) (a : D.Source) :
    D.blockEvaluation hD (p.val * g) a =
      (parabolicHalfCharacter F B (ofFinite F B p) : ℂ) •
        PiTensorProduct.map (fun i => D.blockRepresentation i (B.leviProjection
          (FiniteAdeles F) p i)) (D.blockEvaluation hD g a) := by
  have h₁ := congrArg Q (LinearMap.congr_fun (D.evaluationAt_parabolic_mul p g) a)
  have h₂ := Representation.IntertwiningMap.isIntertwining _ _ (Q).toIntertwiningMap p
    (D.evaluationAt g a)
  exact h₁.trans h₂

/-- The restriction of the regrouped evaluations to the finite integral
compact subgroup still separates the actual restricted inducing tensor. -/
theorem blockEvaluation_compact_injective :
    Function.Injective (fun a : D.Source => fun l : standardIntegral F n =>
      D.blockEvaluation hD l.val a) := by
  intro a b hK
  let e (w : FinitePlace F) := localBlockCompactEvaluation F B w (σ w)
  let L := pointwiseEvaluation e D.exceptional D.sectionReference D.coefficientReference
    D.sectionReference_evaluation
  have hi : Function.Injective L := pointwiseEvaluation_injective
    e D.exceptional D.sectionReference D.coefficientReference D.sectionReference_evaluation
    (fun w => eq_zero_of_localBlockCompactEvaluation_zero F B w (σ w)) (D.coefficientReference_nonzero hD)
  refine @hi a b ?_
  funext k
  let j := standardIntegralProductEquiv F n
  let l := j.symm k
  have he : D.evaluationAt l.val a = D.evaluationAt l.val b := (Q).injective (congrFun hK l)
  have h₁ : D.evaluationAt l.val a = L a k :=
    (D.evaluationAt_compact l a).trans (congrArg (L a) (j.apply_symm_apply k))
  have h₂ : D.evaluationAt l.val b = L b k :=
    (D.evaluationAt_compact l b).trans (congrArg (L b) (j.apply_symm_apply k))
  exact h₁.symm.trans (he.trans h₂)

end Langlands.Global.FiniteAdelicGL.BlockInducedReferences

import Langlands.Global.ArchimedeanEnvelopingLaws

/-! # Proof of left-translation compatibility for the enveloping action -/

noncomputable section
universe u
open scoped TensorProduct
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

theorem complexSmoothLieAction_leftTranslation (X : ComplexLieAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    complexSmoothLieAction K n X * smoothLeftTranslation K n a =
      smoothLeftTranslation K n a * complexSmoothLieAction K n X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexSmoothLieAction_tmul, smul_mul_assoc, mul_smul_comm]
    exact congrArg (fun T : Module.End ℂ (SmoothFunctions K n) => z • T)
      (smoothDifferential_leftTranslation K n X a)
  | add X Y hX hY =>
    simp only [map_add, add_mul, mul_add, hX, hY]

theorem envelopingLeftTranslation : EnvelopingLeftTranslation K n := by
  intro u a
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ComplexLieAlgebra K n)) u
  change envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) *
      smoothLeftTranslation K n a =
    smoothLeftTranslation K n a *
      envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    simp only [AlgHom.commutes]
    exact Algebra.commutes z (smoothLeftTranslation K n a)
  | ι X =>
    change envelopingAction K n (envelopingGenerator K n X) * _ =
      _ * envelopingAction K n (envelopingGenerator K n X)
    rw [envelopingAction_generator]
    exact complexSmoothLieAction_leftTranslation K n X a
  | mul x y hx hy =>
    simp only [map_mul]
    calc
      _ = envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ x) *
          (envelopingAction K n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) *
            smoothLeftTranslation K n a) := mul_assoc _ _ _
      _ = _ := by rw [hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add, hx, hy]

theorem envelopingAction_leftTranslation_apply (u : EnvelopingAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    envelopingAction K n u (smoothLeftTranslation K n a f) =
      smoothLeftTranslation K n a (envelopingAction K n u f) :=
  LinearMap.congr_fun (envelopingLeftTranslation K n u a) f

theorem envelopingAction_leftTranslation_eval (u : EnvelopingAlgebra K n)
    (a x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    (envelopingAction K n u (smoothLeftTranslation K n a f)).val x =
      (envelopingAction K n u f).val (a * x) := by
  rw [envelopingAction_leftTranslation_apply, smoothLeftTranslation_apply]

theorem envelopingAction_preserves_left_invariance (u : EnvelopingAlgebra K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) (hf : smoothLeftTranslation K n a f = f) :
    smoothLeftTranslation K n a (envelopingAction K n u f) =
      envelopingAction K n u f := by
  rw [← envelopingAction_leftTranslation_apply, hf]

theorem centerAction_leftTranslation (z : EnvelopingCenter K n)
    (a : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    centerAction K n z (smoothLeftTranslation K n a f) =
      smoothLeftTranslation K n a (centerAction K n z f) :=
  envelopingAction_leftTranslation_apply K n (centerInclusion K n z) a f

example : ∀ (K : Type u) [Field K] [NumberField K] (n : ℕ),
    EnvelopingLeftTranslation K n :=
  @envelopingLeftTranslation

end Langlands.Global.ArchimedeanGL

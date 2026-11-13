import Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent
import Langlands.GroupScheme.Quaternionic.Involution

/-! # Involutions on Galois-fixed algebras -/

noncomputable section

universe u v

open scoped TensorProduct

namespace Langlands.CentralSimple.SemilinearGaloisAction

open Langlands.GroupScheme.Quaternionic

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {B : Type v} [Ring B] [Algebra L B] [Algebra K B] [IsScalarTower K L B]
  (ρ : SemilinearGaloisAction K L B) (τ : FirstKindInvolution L B)
  (hτ : ∀ σ x, ρ.act σ (τ x) = τ (ρ.act σ x))

/-- A commuting involution restricts to the Galois-fixed algebra. -/
def fixedInvolution : FirstKindInvolution K ρ.fixed where
  toLinearMap :=
    { toFun := fun a => ⟨τ a, fun σ => by rw [hτ, ρ.act_fixed]⟩
      map_add' := fun a b => Subtype.ext (τ.map_add a b)
      map_smul' := fun k a =>
        Subtype.ext ((τ.toLinearMap.restrictScalars K).map_smul k (a : B)) }
  map_one' := Subtype.ext τ.map_one
  map_mul' := fun a b => Subtype.ext (τ.map_mul a b)
  involutive' := fun a => Subtype.ext (τ.apply_apply a)

@[simp]
theorem coe_fixedInvolution (a : ρ.fixed) :
    (ρ.fixedInvolution τ hτ a : B) = τ a := rfl

variable [FiniteDimensional K L] [IsGalois K L]

/-- The algebra descent chart intertwines the extended fixed involution and the
original involution. -/
theorem descentEquiv_fixedInvolution (x : L ⊗[K] ρ.fixed) :
    ρ.descentEquiv ((ρ.fixedInvolution τ hτ).baseChange L x) =
      τ (ρ.descentEquiv x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul l a =>
    rw [FirstKindInvolution.baseChange_tmul, descentEquiv_tmul, descentEquiv_tmul]
    change algebraMap L B l * τ a = τ (algebraMap L B l * a)
    simpa only [Algebra.smul_def] using (τ.map_smul l (a : B)).symm

end Langlands.CentralSimple.SemilinearGaloisAction

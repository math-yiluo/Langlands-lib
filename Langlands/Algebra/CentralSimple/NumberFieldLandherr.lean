import Langlands.Algebra.CentralSimple.NumberFieldLandherrStatement
import Langlands.Algebra.CentralSimple.LandherrEichlerGlobal
import Langlands.Algebra.CentralSimple.LandherrMain

/-! # Landherr's theorem over number fields -/

noncomputable section

namespace Langlands.CentralSimple

open Langlands.GroupScheme.Quaternionic Langlands.GroupScheme.SU3Root Landherr
open scoped TensorProduct

universe u

/-- **Landherr's theorem.** A symmetric unit of a central simple algebra with an involution of
the second kind over a quadratic extension of number fields which is locally of the form
`x τ(x)` at every place is globally of this form. -/
theorem numberFieldLandherr : NumberFieldLandherrStatement.{u} := by
  intro F E B _ _ _ _ _ _ _ _ _ _ _ _ _ τ hτ y hy hloc
  obtain ⟨b, hb⟩ := exists_relNorm_eq_one F E B τ hτ y hy hloc
  let y₂ : Bˣ := b⁻¹ * y * involutionUnit τ b⁻¹
  have hy₂ : (y₂ : B) = ((b⁻¹ : Bˣ) : B) * y * τ ((b⁻¹ : Bˣ) : B) := rfl
  have hy₂τ : τ (y₂ : B) = y₂ := by
    rw [hy₂]
    simp only [FirstKindInvolution.map_mul, FirstKindInvolution.apply_apply, hy, mul_assoc]
  have hloc₂ : ∀ v : Global.Place F, ∃ x : (Global.placeCompletion F v ⊗[F] B)ˣ,
      (1 : Global.placeCompletion F v) ⊗ₜ[F] (y₂ : B) =
        (x : Global.placeCompletion F v ⊗[F] B) * τ.baseChange (Global.placeCompletion F v) x := by
    intro v
    obtain ⟨x, hx⟩ := hloc v
    let c : (Global.placeCompletion F v ⊗[F] B)ˣ :=
      Units.map (Algebra.TensorProduct.includeRight :
        B →ₐ[F] Global.placeCompletion F v ⊗[F] B).toMonoidHom b⁻¹
    have hc : (c : Global.placeCompletion F v ⊗[F] B) =
        (1 : Global.placeCompletion F v) ⊗ₜ[F] ((b⁻¹ : Bˣ) : B) := rfl
    refine ⟨c * x, ?_⟩
    rw [hy₂, Units.val_mul, FirstKindInvolution.map_mul, hc, FirstKindInvolution.baseChange_tmul]
    calc (1 : Global.placeCompletion F v) ⊗ₜ[F] (((b⁻¹ : Bˣ) : B) * y * τ ((b⁻¹ : Bˣ) : B))
        = ((1 : Global.placeCompletion F v) ⊗ₜ[F] ((b⁻¹ : Bˣ) : B)) *
            ((1 : Global.placeCompletion F v) ⊗ₜ[F] (y : B)) *
            ((1 : Global.placeCompletion F v) ⊗ₜ[F] τ ((b⁻¹ : Bˣ) : B)) := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
            one_mul]
      _ = ((1 : Global.placeCompletion F v) ⊗ₜ[F] ((b⁻¹ : Bˣ) : B)) *
            ((x : Global.placeCompletion F v ⊗[F] B) *
              τ.baseChange (Global.placeCompletion F v) x) *
            ((1 : Global.placeCompletion F v) ⊗ₜ[F] τ ((b⁻¹ : Bˣ) : B)) := by
          rw [hx]
      _ = _ := by simp only [mul_assoc]
  obtain ⟨x₂, hx₂⟩ := exists_eq_mul_of_relNorm_eq_one F E B τ hτ y₂ hy₂τ
    (fun v => hloc₂ (.inr v)) (fun w => hloc₂ (.inl w)) hb
  refine ⟨b * x₂, ?_⟩
  have h1 : τ ((b⁻¹ : Bˣ) : B) * τ (b : B) = 1 := by
    rw [← FirstKindInvolution.map_mul, Units.mul_inv, FirstKindInvolution.map_one]
  have hyb : (y : B) = (b : B) * y₂ * τ (b : B) := by
    rw [hy₂]
    calc (y : B) = ((b : B) * ((b⁻¹ : Bˣ) : B)) * y * (τ ((b⁻¹ : Bˣ) : B) * τ (b : B)) := by
          rw [Units.mul_inv, h1, one_mul, mul_one]
      _ = _ := by simp only [mul_assoc]
  rw [hyb, hx₂, Units.val_mul, FirstKindInvolution.map_mul]
  simp only [mul_assoc]

end Langlands.CentralSimple

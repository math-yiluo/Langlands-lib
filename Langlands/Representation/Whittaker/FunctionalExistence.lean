import Langlands.Representation.Whittaker.MirabolicModels
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Rank-one nonvanishing and mirabolic evaluation of Whittaker functionals

The mirabolic evaluation construction preserves nonzero intertwiners. It does
not construct an intertwiner into the mirabolic model.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis

universe uF uV

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A nonzero rank-one carrier has a nonzero standard Whittaker functional. -/
theorem hasFunctional_rankOne [Nontrivial V] (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) V) :
    HasFunctional (N := upperUnipotent 1 F) (θ := standardCharacter ψ 0) ρ := by
  obtain ⟨ℓ, hℓ⟩ := exists_ne (0 : Module.Dual ℂ V)
  refine ⟨⟨ℓ, ?_⟩, hℓ⟩
  change ℓ ∈ glFunctionals ψ 0 ρ
  rw [glFunctionals_rankOne]
  trivial

/-- Irreducibility supplies the nonzero carrier needed for rank-one genericity. -/
theorem isGeneric_rankOne (ψ : UnitaryAdditiveCharacter F)
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) V)
    [Representation.IsIrreducible ρ] (hρ : IsAdmissible ρ) :
    IsGeneric ψ 0 ρ := by
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Langlands.GeneralLinear 1 F)) ρ.asModule
  exact ⟨inferInstance, hρ, hasFunctional_rankOne ψ ρ⟩

section Mirabolic

variable [IsTopologicalRing F]
variable (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
variable (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Evaluation at the identity turns an actual mirabolic-model intertwiner
into an ambient standard Whittaker functional. -/
def mirabolicEvaluation :
    Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n)
      →ₗ[ℂ] glFunctionals ψ n ρ where
  toFun f :=
    ⟨{ toFun := fun v => mirabolicEval ψ n (f v) 1
       map_add' v w := by
         change mirabolicEval ψ n (f (v + w)) 1 =
           mirabolicEval ψ n (f v) 1 + mirabolicEval ψ n (f w) 1
         rw [map_add]
         rfl
       map_smul' a v := by
         change mirabolicEval ψ n (f (a • v)) 1 =
           a • mirabolicEval ψ n (f v) 1
         rw [map_smul]
         rfl },
      by
        intro u v
        let uP : Mirabolic.upperUnipotent n F := Mirabolic.upperUnipotentEquiv.symm u
        change mirabolicEval ψ n (f ((ρ.comp (mirabolic n F).subtype) uP.val v)) 1 =
          (standardCharacter ψ n u : ℂ) * mirabolicEval ψ n (f v) 1
        rw [f.isIntertwining, mirabolicEval_translate, one_mul]
        simpa only [mul_one, mirabolicCharacter_apply, uP, MulEquiv.apply_symm_apply] using
          mirabolicEval_covariance ψ n (f v) uP 1⟩
  map_add' f h := by
    apply Subtype.ext
    ext v
    rfl
  map_smul' a f := by
    apply Subtype.ext
    ext v
    rfl

@[simp]
theorem mirabolicEvaluation_apply
    (f : Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n))
    (v : V) :
    (mirabolicEvaluation ψ n ρ f).val v = mirabolicEval ψ n (f v) 1 := rfl

/-- Every value of the intertwiner is recovered by translating its input. -/
theorem mirabolicEvaluation_coefficient
    (f : Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n))
    (v : V) (g : mirabolic n F) :
    (mirabolicEvaluation ψ n ρ f).val (ρ g.val v) = mirabolicEval ψ n (f v) g := by
  change mirabolicEval ψ n (f ((ρ.comp (mirabolic n F).subtype) g v)) 1 = _
  rw [f.isIntertwining, mirabolicEval_translate, one_mul]

/-- Evaluation at one is injective on mirabolic intertwiners because right
translation recovers evaluation at every group element. -/
theorem mirabolicEvaluation_injective : Function.Injective (mirabolicEvaluation ψ n ρ) := by
  intro f h hfh
  ext v g
  have heq := congrArg (fun ℓ : glFunctionals ψ n ρ => ℓ.val (ρ g.val v)) hfh
  simpa only [mirabolicEvaluation_coefficient, mirabolicEval_def,
    Representation.IntertwiningMap.toLinearMap_apply] using heq

/-- A specified nonzero mirabolic intertwiner yields a nonzero ambient functional. -/
theorem mirabolicEvaluation_ne_zero
    (f : Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n))
    (hf : f ≠ 0) :
    (mirabolicEvaluation ψ n ρ f).val ≠ 0 := by
  intro h
  apply hf
  apply mirabolicEvaluation_injective ψ n ρ
  have hz : mirabolicEvaluation ψ n ρ f = 0 := Subtype.ext h
  rw [hz, map_zero]

/-- The algebraic functional passage from an actual nonzero mirabolic map. -/
theorem hasFunctional_of_mirabolicIntertwiner
    (f : Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n))
    (hf : f ≠ 0) :
    HasFunctional (N := upperUnipotent (n + 1) F) (θ := standardCharacter ψ n) ρ :=
  ⟨mirabolicEvaluation ψ n ρ f, mirabolicEvaluation_ne_zero ψ n ρ f hf⟩

/-- An irreducible admissible representation with such a map is generic. -/
theorem isGeneric_of_mirabolicIntertwiner [Representation.IsIrreducible ρ]
    (hρ : IsAdmissible ρ)
    (f : Representation.IntertwiningMap (ρ.comp (mirabolic n F).subtype) (mirabolicSmoothInduced ψ n))
    (hf : f ≠ 0) :
    IsGeneric ψ n ρ :=
  ⟨inferInstance, hρ, hasFunctional_of_mirabolicIntertwiner ψ n ρ f hf⟩

end Mirabolic
end Langlands.Whittaker

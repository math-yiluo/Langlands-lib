import Langlands.Representation.Whittaker.MirabolicRestrictionInjectivityStatement
import Langlands.Representation.Whittaker.LocalFieldMultiplicityOneStatement
import Langlands.Representation.Whittaker.LocalFieldMirabolicNondegeneracyStatement
import Langlands.Representation.Whittaker.FunctionalExactness
import Langlands.Group.GL.LocalFieldUpperUnipotentCompactSubgroup
import Langlands.Group.GL.Nonarchimedean
import Langlands.Topology.Nonarchimedean.Subgroup
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-! # The mirabolic coefficient map and its kernel -/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear Langlands.HarmonicAnalysis

universe uF uV

section Algebraic

variable {F : Type uF} [CommRing F] [TopologicalSpace F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The coefficient map restricted to the actual mirabolic group, with its
right-translation action. -/
def mirabolicCoefficientFunctionMap (ℓ : glFunctionals ψ n π) :
    Representation.IntertwiningMap (π.comp (mirabolic n F).subtype)
      (rightTranslation ℂ (mirabolic n F)) where
  toLinearMap := matrixCoefficient (π.comp (mirabolic n F).subtype) ℓ.val
  isIntertwining' p := by
    ext v q
    change ℓ.val (π q.val (π p.val v)) = ℓ.val (π (q.val * p.val) v)
    rw [map_mul, Module.End.mul_apply]

/-- The actual mirabolic invariant subspace of vectors whose restricted
coefficient function vanishes identically. -/
def mirabolicCoefficientKernel (ℓ : glFunctionals ψ n π) :
    Subrepresentation (π.comp (mirabolic n F).subtype) :=
  (mirabolicCoefficientFunctionMap ψ n π ℓ).ker

@[simp] theorem mem_mirabolicCoefficientKernel (ℓ : glFunctionals ψ n π) (v : V) :
    v ∈ mirabolicCoefficientKernel ψ n π ℓ ↔
      ∀ p : mirabolic n F, ℓ.val (π p.val v) = 0 := by
  change (fun p : mirabolic n F => ℓ.val (π p.val v)) = 0 ↔ _
  exact funext_iff

theorem functional_eq_zero_on_mirabolicCoefficientKernel (ℓ : glFunctionals ψ n π)
    (v : (mirabolicCoefficientKernel ψ n π ℓ).toSubmodule) : ℓ.val v.val = 0 := by
  have h := (mem_mirabolicCoefficientKernel ψ n π ℓ v.val).mp v.property 1
  simpa only [OneMemClass.coe_one, map_one, Module.End.one_apply] using h

end Algebraic

section LocalField

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (ψ : UnitaryAdditiveCharacter F) (n : ℕ)
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Under multiplicity one, the kernel's full upper character quotient is zero.
The compact-containment and smooth localization inputs hold over every local
field and are discharged here. -/
theorem mirabolicCoefficientKernel_coinvariants_subsingleton
    (hπ : IsGeneric ψ n π) (ℓ : glFunctionals ψ n π)
    (hmult : ∀ m : glFunctionals ψ n π, ∃ c : ℂ, m = c • ℓ) :
    Subsingleton
      (Jacquet.Localization.Coinvariants
        (mirabolicCoefficientKernel ψ n π ℓ).toRepresentation
        (Mirabolic.upperUnipotent n F)
        ((standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom)) := by
  let K := mirabolicCoefficientKernel ψ n π ℓ
  let ρ := π.comp (mirabolic n F).subtype
  let U := Mirabolic.upperUnipotent n F
  let θ := (standardCharacter ψ n).comp Mirabolic.upperUnipotentEquiv.toMonoidHom
  let ι : K.toRepresentation.IntertwiningMap ρ :=
    ⟨K.toSubmodule.subtype, fun _ => rfl⟩
  have hρ : IsSmooth ρ :=
    isSmooth_comp (mirabolic n F).subtype continuous_subtype_val hπ.2.1.1
  letI : NonarchimedeanGroup (Langlands.GeneralLinear (n + 1) F) :=
    valuativeGeneralLinearNonarchimedean F (n + 1)
  have hθc : Continuous θ :=
    (standardCharacterContinuous ψ n).continuous.comp
      Mirabolic.upperUnipotentContinuousEquiv.continuous
  have hθloc : IsLocallyConstant (fun u : U => (θ u : ℂ)) :=
    RankinSelberg.isLocallyConstant_of_continuous_complex_character θ hθc
  have hzero : ∀ m : functionals U θ K.toRepresentation, m = 0 := by
    intro m
    obtain ⟨L, hL⟩ := functionalsComap_surjective_of_smooth U
      (localField_mirabolicUpperUnipotent_isLimitOfCompactSubgroups F n) θ hθloc
      ι Subtype.val_injective hρ m
    let L' : glFunctionals ψ n π :=
      ⟨L.val, fun u v => L.property (Mirabolic.upperUnipotentEquiv.symm u) v⟩
    obtain ⟨c, hc⟩ := hmult L'
    apply Subtype.ext
    ext v
    have hv : m.val v = L.val v.val :=
      (congrArg (fun t : functionals U θ K.toRepresentation => t.val v) hL).symm
    rw [hv]
    change L'.val v.val = 0
    rw [hc]
    change c * ℓ.val v.val = 0
    rw [functional_eq_zero_on_mirabolicCoefficientKernel ψ n π ℓ v, mul_zero]
  haveI : Subsingleton (functionals U θ K.toRepresentation) :=
    ⟨fun a b => (hzero a).trans (hzero b).symm⟩
  haveI : Subsingleton
      (Module.Dual ℂ (Jacquet.Localization.Coinvariants K.toRepresentation U θ)) :=
    (functionalsLocalizationDualEquiv U θ K.toRepresentation).toEquiv.subsingleton_congr.mp
      inferInstance
  exact (Module.subsingleton_dual_iff ℂ).mp inferInstance

/-- The exact injectivity target follows once the two all-field representation
theorems are proved. This implication alone does not prove the target. -/
theorem mirabolicRestrictionInjectivity_of_multiplicityOne_of_nondegeneracy
    (hmult : LocalFieldMultiplicityOneStatement.{uF,uV})
    (hnd : LocalFieldMirabolicNondegeneracyStatement.{uF,uV}) :
    MirabolicRestrictionInjectivityStatement.{uF,uV} := by
  intro F _ _ _ _ n ψ V _ _ π hπ ℓ hℓ
  let K := mirabolicCoefficientKernel ψ n π ℓ
  have hK : K = ⊥ := hnd F n ψ π hπ K
    (mirabolicCoefficientKernel_coinvariants_subsingleton ψ n π hπ ℓ
      (fun m => by
        obtain ⟨c, hc, _⟩ := hmult F n V ψ π hπ.2.1 hπ.1 ℓ m hℓ
        exact ⟨c, hc⟩))
  apply (mirabolicCoefficientFunctionMap ψ n π ℓ).toLinearMap.ker_eq_bot.mp
  exact congrArg Subrepresentation.toSubmodule hK

end LocalField
end Langlands.Whittaker

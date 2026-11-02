import Langlands.Automorphic.ConstantRealizationProperties
import Langlands.Automorphic.AutomorphicCentralCharacterDeterminantMultiplier

/-! # Actual automorphic lines of finite-order Hecke characters -/

noncomputable section

universe uF

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.FiniteOrderHeckeRealization

open Langlands.Global ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)
variable (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)

local instance heckeLineGroup1 : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance heckeLineGroup2 : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeLineGroup3 : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance heckeLineGroup4 : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance heckeLineGroup5 : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

/-- The actual line of forms obtained by multiplying constants by `χ ∘ det`. -/
def realization : OperatorRealization F n :=
  (ConstantFunctions.realization F n).determinantTwist χ hχ

local instance heckeLineGroup6 : AddCommGroup (realization F n χ hχ).Space := Submodule.addCommGroup _
local instance heckeLineGroup7 : AddCommGroup (ConstantFunctions.realization F n).Space :=
  Submodule.addCommGroup _

/-- A scalar maps to the represented function `g ↦ χ(det g) * c`. -/
def scalarEquiv : ℂ ≃ₗ[ℂ] (realization F n χ hχ).Space :=
  (ConstantFunctions.scalarEquiv F n).trans
    ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ).toLinearEquiv

@[simp]
theorem evaluate_scalarEquiv (c : ℂ) (g : AdelicGL F n) :
    evaluate F n ((realization F n χ hχ).toContinuous (scalarEquiv F n χ hχ c)) g =
      (χ.adelicDeterminant n g : ℂ) * c := rfl

/-- Evaluation at the identity recovers the unique scalar of any represented vector. -/
theorem scalarEquiv_symm_apply (f : (realization F n χ hχ).Space) :
    (scalarEquiv F n χ hχ).symm f =
      evaluate F n ((realization F n χ hχ).toContinuous f) 1 := by
  obtain ⟨c, rfl⟩ := (scalarEquiv F n χ hχ).surjective f
  rw [LinearEquiv.symm_apply_apply, evaluate_scalarEquiv]
  simp only [map_one, Units.val_one, one_mul]

theorem realization_finrank : Module.finrank ℂ (realization F n χ hχ).Space = 1 := by
  rw [← (scalarEquiv F n χ hχ).finrank_eq, Module.finrank_self]

/-- The actual forms, retaining their original embedding in `AutomorphicForms`. -/
def form : ℂ →ₗ[ℂ] AutomorphicForms F n :=
  (realization F n χ hχ).formInclusion.toLinearMap.comp
    (scalarEquiv F n χ hχ).toLinearMap

@[simp]
theorem evaluate_form (c : ℂ) (g : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n (form F n χ hχ c)) g =
      (χ.adelicDeterminant n g : ℂ) * c := rfl

theorem form_injective : Function.Injective (form F n χ hχ) :=
  (realization F n χ hχ).formInclusion_injective.comp
    (scalarEquiv F n χ hχ).injective

/-- Every finite-order Hecke character supplies a nonzero actual form. -/
theorem form_one_ne_zero : form F n χ hχ 1 ≠ 0 := by
  intro h
  exact one_ne_zero ((form_injective F n χ hχ) (h.trans (map_zero _).symm))

theorem finiteRepresentation_scalarEquiv (d : FiniteAdelicGL F n) (c : ℂ) :
    (realization F n χ hχ).finiteRepresentation d (scalarEquiv F n χ hχ c) =
      scalarEquiv F n χ hχ
        ((χ.adelicDeterminant n (AdelicGL.ofFinite F n d) : ℂ) * c) := by
  change ((ConstantFunctions.realization F n).determinantTwist χ hχ).finiteRepresentation d
      ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ
        (ConstantFunctions.scalarEquiv F n c)) = _
  rw [OperatorRealization.determinantTwistEquiv_finite,
    ConstantFunctions.finiteRepresentation_scalarEquiv]
  exact ((scalarEquiv F n χ hχ).map_smul _ c).symm

theorem compactRepresentation_scalarEquiv (k : standardInfiniteCompact F n) (c : ℂ) :
    (realization F n χ hχ).compactRepresentation k (scalarEquiv F n χ hχ c) =
      scalarEquiv F n χ hχ
        ((χ.adelicDeterminant n (AdelicGL.ofInfinite F n k.val) : ℂ) * c) := by
  change ((ConstantFunctions.realization F n).determinantTwist χ hχ).compactRepresentation k
      ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ
        (ConstantFunctions.scalarEquiv F n c)) = _
  rw [OperatorRealization.determinantTwistEquiv_compact,
    ConstantFunctions.compactRepresentation_scalarEquiv]
  exact ((scalarEquiv F n χ hχ).map_smul _ c).symm

/-- Finite order leaves the genuine infinitesimal action equal to the augmentation. -/
theorem envelopingAction_scalarEquiv (a : ArchimedeanGL.EnvelopingAlgebra F n) (c : ℂ) :
    (realization F n χ hχ).envelopingAction a (scalarEquiv F n χ hχ c) =
      scalarEquiv F n χ hχ (ArchimedeanGL.augmentation F n a * c) := by
  change ((ConstantFunctions.realization F n).determinantTwist χ hχ).envelopingAction a
      ((ConstantFunctions.realization F n).determinantTwistEquiv χ hχ
        (ConstantFunctions.scalarEquiv F n c)) = _
  rw [OperatorRealization.determinantTwistEquiv_differential,
    ConstantFunctions.envelopingAction_scalarEquiv]
  rfl

theorem realization_isIrreducible : (realization F n χ hχ).IsIrreducible :=
  ((ConstantFunctions.realization F n).determinantTwist_isIrreducible_iff χ hχ).mpr
    (ConstantFunctions.realization_isIrreducible F n)

/-- Scalar ideles act through `χ^n`, with the actual matrix rank retained. -/
theorem realization_hasCentralCharacter :
    (realization F n χ hχ).HasCentralCharacter (χ ^ n) := by
  have h :
      ((ConstantFunctions.realization F n).determinantTwist χ hχ).HasCentralCharacter
        (χ ^ n * (1 : HeckeCharacter F)) :=
    (ConstantFunctions.realization F n).determinantTwist_hasCentralCharacter χ 1 hχ
      (ConstantFunctions.realization_hasCentralCharacter F n)
  have hχone : χ ^ n * (1 : HeckeCharacter F) = χ ^ n := by
    apply ContinuousMonoidHom.ext
    intro x
    change (χ ^ n) x * (1 : ℂˣ) = (χ ^ n) x
    exact mul_one ((χ ^ n) x)
  rw [hχone] at h
  exact h

theorem realization_hasInfinitesimalCharacter :
    (realization F n χ hχ).HasInfinitesimalCharacter
      ((ArchimedeanGL.augmentation F n).comp (ArchimedeanGL.centerInclusion F n)) := by
  intro z f
  obtain ⟨c, rfl⟩ := (scalarEquiv F n χ hχ).surjective f
  rw [envelopingAction_scalarEquiv]
  exact (scalarEquiv F n χ hχ).map_smul (ArchimedeanGL.augmentation F n z.val) c

theorem realization_isRegularAlgebraic : (realization F n χ hχ).IsRegularAlgebraic :=
  ⟨_, ArchimedeanGL.isRegularAlgebraicCharacter_augmentation F n,
    realization_hasInfinitesimalCharacter F n χ hχ⟩

section RankOne

variable [CompactSpace (AdeleQuotient F)]

/-- The actual finite-order Hecke-character line is a rank-one cuspidal object. -/
def cuspidal : CuspidalOperatorRealization F 0 :=
  (ConstantFunctions.rankOneCuspidal F).determinantTwist χ hχ

@[simp]
theorem cuspidal_realization :
    (cuspidal F χ hχ).realization = realization F 1 χ hχ := rfl

theorem cuspidal_hasCentralCharacter : (cuspidal F χ hχ).HasCentralCharacter χ := by
  change (realization F 1 χ hχ).HasCentralCharacter χ
  simpa only [pow_one] using realization_hasCentralCharacter F 1 χ hχ

/-- The class has the constructed actual representative above. -/
def cuspidalClass : CuspidalOperatorRealization.IsoClass F 0 :=
  (cuspidal F χ hχ).isoClass

@[simp]
theorem cuspidalClass_toOperatorClass :
    (cuspidalClass F χ hχ).toOperatorClass = (realization F 1 χ hχ).isoClass := rfl

theorem cuspidalClass_isRegularAlgebraic :
    (cuspidalClass F χ hχ).IsRegularAlgebraic :=
  ((cuspidal F χ hχ).isoClass_isRegularAlgebraic_iff).mpr
    (realization_isRegularAlgebraic F 1 χ hχ)

end RankOne
end Langlands.Automorphic.FiniteOrderHeckeRealization

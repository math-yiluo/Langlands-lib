import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Connected.TotallyDisconnected

/-! Common nonarchimedean test functions and the plus-sign Fourier integral. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe u

/-- A continuous, nontrivial additive character with values in the unit circle. -/
structure UnitaryAdditiveCharacter (F : Type u) [AddGroup F] [TopologicalSpace F]
    extends AddChar F Circle where
  continuous_toFun : Continuous toAddChar
  nontrivial : toAddChar ≠ 1

instance {F : Type u} [AddGroup F] [TopologicalSpace F] :
    CoeFun (UnitaryAdditiveCharacter F) (fun _ => F → Circle) :=
  ⟨fun ψ => ψ.toAddChar⟩

/-- A quasicharacter is a continuous unit-valued multiplicative character.
This is an abbreviation for the existing Mathlib object, not a new character type. -/
abbrev Quasicharacter (F : Type u) [Field F] [TopologicalSpace F] :=
  ContinuousMonoidHom Fˣ ℂˣ

namespace UnitaryAdditiveCharacter

variable {F : Type u} [AddGroup F] [TopologicalSpace F]

/-- The same character, viewed as a complex-valued additive character. -/
def complex (ψ : UnitaryAdditiveCharacter F) : AddChar F ℂ :=
  Circle.coeHom.compAddChar ψ.toAddChar

@[simp]
theorem complex_apply (ψ : UnitaryAdditiveCharacter F) (x : F) :
    ψ.complex x = (ψ x : ℂ) := rfl

theorem continuous_complex (ψ : UnitaryAdditiveCharacter F) :
    Continuous ψ.complex :=
  continuous_subtype_val.comp ψ.continuous_toFun

@[simp]
theorem norm_complex (ψ : UnitaryAdditiveCharacter F) (x : F) :
    ‖ψ.complex x‖ = 1 := Circle.norm_coe _

end UnitaryAdditiveCharacter

section TestFunctions

variable (X : Type u) [TopologicalSpace X]

/-- Compactly supported locally constant complex functions, as a submodule. -/
def schwartzBruhatSubmodule : Submodule ℂ (X → ℂ) where
  carrier := {f | IsLocallyConstant f ∧ HasCompactSupport f}
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  add_mem' hf hg := ⟨hf.1.comp₂ hg.1 (· + ·), hf.2.add hg.2⟩
  smul_mem' c _f hf := ⟨hf.1.comp (c • ·), hf.2.smul_left⟩

/-- The Schwartz–Bruhat space for a nonarchimedean topological space. -/
abbrev SchwartzBruhat := ↥(schwartzBruhatSubmodule X)

instance : CoeFun (SchwartzBruhat X) (fun _ => X → ℂ) := ⟨fun f => f.1⟩

namespace SchwartzBruhat

variable {X}

theorem locallyConstant (f : SchwartzBruhat X) : IsLocallyConstant (f : X → ℂ) :=
  f.2.1

theorem hasCompactSupport (f : SchwartzBruhat X) : HasCompactSupport (f : X → ℂ) :=
  f.2.2

theorem continuous (f : SchwartzBruhat X) : Continuous (f : X → ℂ) :=
  (locallyConstant f).continuous

end SchwartzBruhat

end TestFunctions

section Measures

variable (F : Type u) [AddGroup F] [TopologicalSpace F] [MeasurableSpace F]

/-- A regular additive Haar measure, without any imposed normalization. -/
structure AdditiveHaarMeasure where
  measure : Measure F
  isAddHaar : measure.IsAddHaarMeasure
  regular : measure.Regular

attribute [instance] AdditiveHaarMeasure.isAddHaar AdditiveHaarMeasure.regular

variable [IsTopologicalAddGroup F] [LocallyCompactSpace F] [T2Space F] [BorelSpace F]

/-- Haar measure normalized on a supplied compact set with nonempty interior. -/
def normalizedAdditiveHaar (K : TopologicalSpace.PositiveCompacts F) :
    AdditiveHaarMeasure F where
  measure := Measure.addHaarMeasure K
  isAddHaar := inferInstance
  regular := inferInstance

end Measures

section Fourier

variable {F : Type u} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [BorelSpace F]

/-- The raw Bochner integral, using `ψ(x*y)` with a plus sign.
For arbitrary functions Mathlib's usual nonintegrable convention applies;
`fourierTransform` below restricts its input to test functions and proves integrability. -/
def fourierIntegral (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F)
    (f : F → ℂ) (y : F) : ℂ :=
  ∫ x, ψ.complex (x * y) * f x ∂μ.measure

theorem fourierIntegrand_integrable (ψ : UnitaryAdditiveCharacter F)
    (μ : AdditiveHaarMeasure F) (f : SchwartzBruhat F) (y : F) :
    Integrable (fun x => ψ.complex (x * y) * f x) μ.measure := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (ψ.continuous_complex.comp (continuous_id.mul continuous_const)).mul
      (SchwartzBruhat.continuous f)
  · exact (SchwartzBruhat.hasCompactSupport f).mul_left

/-- The plus-sign Fourier transform as a linear map from test functions to functions.
Preservation of the Schwartz–Bruhat subspace is a separate theorem obligation. -/
def fourierTransform (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F) :
    SchwartzBruhat F →ₗ[ℂ] (F → ℂ) where
  toFun f := fourierIntegral ψ μ f
  map_add' f g := by
    funext y
    simp only [fourierIntegral, Submodule.coe_add, Pi.add_apply, mul_add]
    exact integral_add (fourierIntegrand_integrable ψ μ f y)
      (fourierIntegrand_integrable ψ μ g y)
  map_smul' c f := by
    funext y
    simp only [fourierIntegral, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    simp_rw [mul_left_comm (ψ.complex _) c]
    exact integral_const_mul c _

/-- Intrinsic Fourier self-duality on the nonarchimedean test space.
The second integral is required to converge, and Fourier squared is reflection. -/
def IsSelfDual [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) (μ : AdditiveHaarMeasure F) : Prop :=
  ∀ f : SchwartzBruhat F,
    (∀ y : F, Integrable (fun x =>
      ψ.complex (x * y) * fourierTransform ψ μ f x) μ.measure) ∧
    ∀ x : F, fourierIntegral ψ μ (fourierTransform ψ μ f) x = f (-x)

/-- An existence proposition, not an assumed or chosen self-dual measure. -/
def SelfDualMeasureExists [LocallyCompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ψ : UnitaryAdditiveCharacter F) : Prop :=
  ∃ μ : AdditiveHaarMeasure F, IsSelfDual ψ μ

end Fourier

end Langlands.HarmonicAnalysis

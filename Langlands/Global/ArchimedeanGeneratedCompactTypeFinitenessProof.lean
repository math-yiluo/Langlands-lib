import Langlands.Global.ArchimedeanCompactTypeCentralSpanProof
import Langlands.Global.ArchimedeanGeneratedCompactTypeFinitenessStatement
import Langlands.Global.ArchimedeanGeneratedCenterAnnihilator
import Langlands.Global.ArchimedeanCenterQuotientOrbit

/-! # Finite compact types in the actual generated differential module -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open DerivativeSmoothFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- One common finite-codimensional annihilator turns a finite covering by
actual center orbits into finite-dimensional compact-type intersections. -/
theorem generatedCompactTypeFiniteness :
    GeneratedCompactTypeFinitenessStatement K n := by
  intro f hf hz σ
  obtain ⟨I, hI, hann⟩ :=
    exists_common_center_ideal_generatedCompactDifferentialSpan K n f hf hz
  obtain ⟨m, v, hcover⟩ := compactTypeCentralSpan K n f hf σ
  have hv (i : Fin m) : IsCenterFinite K n (toSmooth K n (v i).val) := by
    apply isCenterFinite_of_finite_quotient_annihilates K n I hI
    intro z hzI
    have h := congrArg (toSmooth K n) (hann z hzI (v i).val (v i).property)
    simpa only [toSmooth_operator, map_zero, centerAction_apply] using h
  let S : Submodule ℂ (DerivativeSmoothFunctions K n) :=
    ⨆ i : Fin m, (centerOrbitSpan K n (toSmooth K n (v i).val)).map
      (toSmooth K n).symm.toLinearMap
  have : ∀ i : Fin m, Module.Finite ℂ
      ((centerOrbitSpan K n (toSmooth K n (v i).val)).map
        (toSmooth K n).symm.toLinearMap) := by
    intro i
    have : Module.Finite ℂ (centerOrbitSpan K n (toSmooth K n (v i).val)) := hv i
    infer_instance
  have : Module.Finite ℂ S := Submodule.finite_iSup _
  exact Submodule.finiteDimensional_of_le (S₂ := S) hcover

end Langlands.Global.ArchimedeanGL

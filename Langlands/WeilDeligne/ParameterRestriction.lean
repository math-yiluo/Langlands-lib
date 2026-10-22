import Langlands.WeilDeligne.Parameters
import Langlands.WeilDeligne.Restriction

/-! # Parameter restriction along continuous homomorphisms respecting inertia -/

noncomputable section

universe uG uH uV

namespace Langlands

variable {G : Type uG} {H : Type uH} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  (I : Subgroup G) (J : Subgroup H) (φ : H →* G) (hφ : Continuous φ)
  (hJI : ∀ j : J, φ (j : H) ∈ I)

namespace FiniteRepresentation

include hφ hJI in
/-- The restricted inertia kernel is the continuous preimage of the original one. -/
theorem hasOpenInertiaKernel_restrict
    {A : FiniteRepresentation.{0, uG, uV} ℂ G} (hA : A.HasOpenInertiaKernel I) :
    (restrict φ A).HasOpenInertiaKernel J := by
  let f : J → I := fun j => ⟨φ (j : H), hJI j⟩
  have hf : Continuous f := (hφ.comp continuous_subtype_val).subtype_mk _
  exact hA.preimage hf

/-- Restrict the actual open-inertia representation along a continuous map respecting inertia. -/
def openInertiaRestrict (A : OpenInertiaObjects.{uG, uV} I) : OpenInertiaObjects.{uH, uV} J :=
  ⟨restrict φ A.val, hasOpenInertiaKernel_restrict I J φ hφ hJI A.property⟩

/-- Restriction is well defined on genuine open-inertia representation classes. -/
def openInertiaRestrictClass :
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uG, uV} ℂ G => A.HasOpenInertiaKernel I) →
    IsomorphismClassesWith
      (fun A : FiniteRepresentation.{0, uH, uV} ℂ H => A.HasOpenInertiaKernel J) :=
  Quotient.map (openInertiaRestrict I J φ hφ hJI)
    (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

end FiniteRepresentation

namespace WeilDeligneRepresentation

variable {ν : G →* ℂˣ}

/-- Restrict an actual parameter, retaining monodromy and pulling back the norm character. -/
def parameterRestrict (A : ParameterObjects.{uG, uV} (ν := ν) I) :
    ParameterObjects.{uH, uV} (ν := ν.comp φ) J :=
  ⟨restrict φ A.val,
    FiniteRepresentation.hasOpenInertiaKernel_restrict I J φ hφ hJI A.property⟩

/-- Parameter restriction descends to the genuine isomorphism quotients. -/
def parameterRestrictClass : ParameterClasses.{uG, uV} (ν := ν) I →
    ParameterClasses.{uH, uV} (ν := ν.comp φ) J :=
  Quotient.map (parameterRestrict I J φ hφ hJI) (fun _ _ ⟨e⟩ => ⟨restrictEquiv φ e⟩)

end WeilDeligneRepresentation

end Langlands

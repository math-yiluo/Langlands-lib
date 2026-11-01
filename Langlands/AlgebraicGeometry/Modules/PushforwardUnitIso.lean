import Langlands.AlgebraicGeometry.Modules.PullbackUnit
import Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

/-! # The structure-module pushforward comparison -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite

namespace Langlands.Scheme.Modules

variable {X S : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- If the structure map is invertible on sections over every open, its
actual comparison of module sheaves is invertible. -/
theorem isIso_unitToPushforwardUnit_of_isIso_app (p : X ⟶ S)
    (h : ∀ U : S.Opens, IsIso (p.app U)) :
    IsIso (unitToPushforwardUnit p) := by
  let φ := (unitToPushforwardUnit p).val
  have hφ (U : S.Opensᵒᵖ) : IsIso (φ.app U) := by
    rw [ConcreteCategory.isIso_iff_bijective]
    change Function.Bijective (p.app U.unop)
    exact (ConcreteCategory.isIso_iff_bijective _).mp (h U.unop)
  have := hφ
  let e := PresheafOfModules.isoMk (fun U ↦ asIso (φ.app U))
    (fun {_ _} f ↦ φ.naturality f)
  have he : e.hom = φ := by
    ext U
    rfl
  have : IsIso ((SheafOfModules.forget S.ringCatSheaf).map
      (unitToPushforwardUnit p)) := by
    change IsIso φ
    rw [← he]
    infer_instance
  exact isIso_of_reflects_iso (unitToPushforwardUnit p)
    (SheafOfModules.forget S.ringCatSheaf)

/-- The structure-module comparison is invertible for a smooth proper
morphism with geometrically connected fibres. -/
theorem isIso_unitToPushforwardUnit (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyConnected p] :
    IsIso (unitToPushforwardUnit p) :=
  isIso_unitToPushforwardUnit_of_isIso_app p
    (Langlands.AlgebraicGeometry.smoothProperConnectedGlobalFunctions X S p
      inferInstance inferInstance inferInstance)

/-- The actual isomorphism from the structure module on the base to the
pushforward of the structure module on a smooth proper connected family. -/
def pushforwardUnitIso (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyConnected p] :
    SheafOfModules.unit S.ringCatSheaf ≅
      (Scheme.Modules.pushforward p).obj (SheafOfModules.unit X.ringCatSheaf) :=
  haveI := isIso_unitToPushforwardUnit p
  asIso (unitToPushforwardUnit p)

@[simp]
lemma pushforwardUnitIso_hom (p : X ⟶ S)
    [Smooth p] [IsProper p] [GeometricallyConnected p] :
    (pushforwardUnitIso p).hom = unitToPushforwardUnit p := rfl

end Langlands.Scheme.Modules

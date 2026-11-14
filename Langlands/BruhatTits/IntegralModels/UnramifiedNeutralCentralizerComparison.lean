import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralGeneration
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusIwahoriModelAssembly
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.Geometry.Building.GenericApartmentInjection

/-! # Comparison of neutral centralizers and neutral fixer models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)

private theorem centralizer_fixes_apartment_of_fixes_one
    (z : rationalPoints C.centralizer.Z) {x : C.Apartment}
    (hx : rationalPoints.map C.centralizer.j z • C.apartmentMap x = C.apartmentMap x)
    (y : C.Apartment) :
    rationalPoints.map C.centralizer.j z • C.apartmentMap y = C.apartmentMap y := by
  have hx' :
      (Submodule.Quotient.mk (C.translation z).toAdd : TranslationSpace C.i) +ᵥ x = x :=
    C.apartment.apartmentMap_injective C.isConnectedReductive C.isMaximalSplitTorus
      ((C.centralizer_smul_apartmentMap z x).symm.trans hx)
  have hzero :
      (Submodule.Quotient.mk (C.translation z).toAdd : TranslationSpace C.i) = 0 := by
    simpa only [vadd_vsub, vsub_self] using
      congrArg (fun p : C.Apartment => p -ᵥ x) hx'
  rw [C.centralizer_smul_apartmentMap, hzero, zero_vadd]

variable
    (D₁ D₂ : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω₁ Ω₂ : Set C.Apartment)
    (hN₁ : D₁.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω₁))
    (hN₂ : D₂.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω₂))

include hN₁ hN₂ in
/-- Centralizer points integral in the first neutral model lie in the second
full model whenever the first apartment subset is nonempty. -/
theorem map_unramifiedNeutralCentralizerModel_integralPoints_le_full
    (hne₁ : Ω₁.Nonempty) :
    (unramifiedNeutralCentralizerModel C D₁ Ω₁ hN₁).integralPoints.map
        (rationalPoints.map C.centralizer.j) ≤ D₂.full.integralPoints := by
  rintro _ ⟨z, hz, rfl⟩
  have hzneutral :=
    (unramifiedNeutralCentralizerModelMap C D₁ Ω₁ hN₁).map_mem_integralPoints hz
  have hzfull : rationalPoints.map C.centralizer.j z ∈ D₁.full.integralPoints := by
    apply D₁.neutralPoints_le_full
    rwa [D₁.neutralPoints_eq]
  rw [hN₁] at hzfull
  rw [hN₂]
  refine ⟨hzfull.1, C.apartment.mem_pointwiseFixer.mpr ?_⟩
  obtain ⟨x, hx⟩ := hne₁
  have hzfix : rationalPoints.map C.centralizer.j z • C.apartmentMap x =
      C.apartmentMap x :=
    C.apartment.mem_pointwiseFixer.mp hzfull.2 _ ⟨x, hx, rfl⟩
  rintro _ ⟨y, _, rfl⟩
  exact centralizer_fixes_apartment_of_fixes_one C z hzfix y

set_option maxHeartbeats 800000 in
include hN₁ hN₂ in
/-- Smooth extension followed by connected factorization compares the
actual neutral-centralizer integral points. -/
theorem unramifiedNeutralCentralizerModel_integralPoints_le
    (hne₁ : Ω₁.Nonempty) :
    (unramifiedNeutralCentralizerModel C D₁ Ω₁ hN₁).integralPoints ≤
      (unramifiedNeutralCentralizerModel C D₂ Ω₂ hN₂).integralPoints := by
  let W := unramifiedNeutralCentralizerModel C D₁ Ω₁ hN₁
  have hW : W.IsSmooth :=
    unramifiedNeutralCentralizerModel_isSmooth C D₁ Ω₁ hN₁
  have hle : W.integralPoints.map (rationalPoints.map C.centralizer.j) ≤
      D₂.full.integralPoints :=
    map_unramifiedNeutralCentralizerModel_integralPoints_le_full
      C D₁ D₂ Ω₁ Ω₂ hN₁ hN₂ hne₁
  obtain ⟨φ⟩ := exists_hom_of_map_integralPoints_le
    IntegralModel.smoothHomExtension F hW rfl hle
  let : GeometricallyConnected W.group.X.hom :=
    unramifiedNeutralCentralizerModel_hasGeometricallyConnectedFibres C D₁ Ω₁ hN₁
  rw [unramifiedNeutralCentralizerModel_integralPoints_eq_comap C D₂ Ω₂ hN₂]
  intro z hz
  exact (D₂.factorConnectedModelHom φ).map_mem_integralPoints hz

/-- The actual neutral-centralizer integral-point subgroup is independent
of the nonempty apartment subset and of the supplied full fixer model. -/
theorem unramifiedNeutralCentralizerModel_integralPoints_eq
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty) :
    (unramifiedNeutralCentralizerModel C D₁ Ω₁ hN₁).integralPoints =
      (unramifiedNeutralCentralizerModel C D₂ Ω₂ hN₂).integralPoints :=
  le_antisymm
    (unramifiedNeutralCentralizerModel_integralPoints_le
      C D₁ D₂ Ω₁ Ω₂ hN₁ hN₂ hne₁)
    (unramifiedNeutralCentralizerModel_integralPoints_le
      C D₂ D₁ Ω₂ Ω₁ hN₂ hN₁ hne₂)

include hN₁ hN₂ in
/-- Equal sharp fixers give equal neutral integral-point subgroups for
supplied full fixer models of two nonempty apartment subsets. -/
theorem unramifiedNeutral_integralPoints_eq_of_sharpFixer_eq
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : C.sharpFixer Ω₁ = C.sharpFixer Ω₂) :
    D₁.neutral.integralPoints = D₂.neutral.integralPoints := by
  rw [← unramifiedNeutralRootCentralizerGroup_eq_neutral C D₁ Ω₁ hN₁,
    ← unramifiedNeutralRootCentralizerGroup_eq_neutral C D₂ Ω₂ hN₂]
  unfold unramifiedNeutralRootCentralizerGroup
  rw [unramifiedNeutralCentralizerModel_integralPoints_eq
    C D₁ D₂ Ω₁ Ω₂ hN₁ hN₂ hne₁ hne₂, hsharp]

/-- The neutral point-group comparison preserves the ambient rational points. -/
def unramifiedNeutralSharpFixerEquiv
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : C.sharpFixer Ω₁ = C.sharpFixer Ω₂) :
    D₁.neutral.integralPoints ≃* D₂.neutral.integralPoints :=
  MulEquiv.subgroupCongr
    (unramifiedNeutral_integralPoints_eq_of_sharpFixer_eq
      C D₁ D₂ Ω₁ Ω₂ hN₁ hN₂ hne₁ hne₂ hsharp)

@[simp]
theorem coe_unramifiedNeutralSharpFixerEquiv
    (hne₁ : Ω₁.Nonempty) (hne₂ : Ω₂.Nonempty)
    (hsharp : C.sharpFixer Ω₁ = C.sharpFixer Ω₂) (g : D₁.neutral.integralPoints) :
    (unramifiedNeutralSharpFixerEquiv
      C D₁ D₂ Ω₁ Ω₂ hN₁ hN₂ hne₁ hne₂ hsharp g : rationalPoints G) = g := rfl

end Langlands.BruhatTits.IntegralModels

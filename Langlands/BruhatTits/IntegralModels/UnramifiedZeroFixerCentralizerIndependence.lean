import Langlands.BruhatTits.IntegralModels.UnramifiedZeroFixerCentralizerImage
import Langlands.GroupScheme.IntegralModel.GenericRigidity

/-! # Independence of the integral centralizer from the zero-fixer model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [Smooth M.group.X.hom]
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω'))

/-- The integral-point subgroup of the centralizer is independent of the nonempty
apartment subset and of the characterized smooth zero-fixer model. -/
theorem unramifiedZeroFixerCentralizer_integralPoints_eq
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty) :
    (unramifiedZeroFixerCentralizerModel C E N Ω hN).integralPoints =
      (unramifiedZeroFixerCentralizerModel C E M Ω' hM).integralPoints := by
  unfold unramifiedZeroFixerCentralizerModel
  rw [IntegralSplitTorusData.centralizerModel_integralPoints_eq_comap,
    IntegralSplitTorusData.centralizerModel_integralPoints_eq_comap,
    hN, hM, Subgroup.comap_inf, Subgroup.comap_inf,
    C.comap_pointwiseFixer_centralizer_eq Ω Ω' hne hne']

/-- The generic identity of the centralizer extends to the actual integral models. -/
def unramifiedZeroFixerCentralizerIdentityHom
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty) :
    (unramifiedZeroFixerCentralizerModel C E N Ω hN).Hom
      (unramifiedZeroFixerCentralizerModel C E M Ω' hM) (𝟙 C.centralizer.Z) := by
  apply Classical.choice
  apply IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F
    C.centralizer.Z C.centralizer.Z (𝟙 C.centralizer.Z)
    (unramifiedZeroFixerCentralizerModel C E N Ω hN)
    (unramifiedZeroFixerCentralizerModel C E M Ω' hM)
    ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).centralizerModel_isSmooth
      C.centralizer.j C.centralizer.isRepresentedBy)
  intro z hz
  have hid : rationalPoints.map (𝟙 C.centralizer.Z) z = z := by
    simp only [rationalPoints.map_apply, Grp.id_hom_hom, Category.comp_id]
  rw [hid, ← unramifiedZeroFixerCentralizer_integralPoints_eq C E N M Ω Ω' hN hM hne hne']
  exact hz

/-- The canonical centralizer isomorphism retains the specified generic identity. -/
def unramifiedZeroFixerCentralizerIso
    (hne : Ω.Nonempty) (hne' : Ω'.Nonempty) :
    (unramifiedZeroFixerCentralizerModel C E N Ω hN).Iso
      (unramifiedZeroFixerCentralizerModel C E M Ω' hM)
      (CategoryTheory.Iso.refl C.centralizer.Z) :=
  IntegralModel.Iso.ofHoms
    (unramifiedZeroFixerCentralizerIdentityHom C E N M Ω Ω' hN hM hne hne')
    (unramifiedZeroFixerCentralizerIdentityHom C E M N Ω' Ω hM hN hne' hne)

/-- The two constructed integral centralizers are isomorphic over the integers,
compatibly with the original identity of the generic centralizer. -/
def UnramifiedZeroFixerCentralizerIndependenceStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    [Smooth N.group.X.hom] [Smooth M.group.X.hom]
    (Ω Ω' : Set C.Apartment)
    (hN : N.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hM : M.integralPoints = E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω')),
    Ω.Nonempty → Ω'.Nonempty →
      Nonempty ((unramifiedZeroFixerCentralizerModel C E N Ω hN).Iso
        (unramifiedZeroFixerCentralizerModel C E M Ω' hM)
        (CategoryTheory.Iso.refl C.centralizer.Z))

/-- The integral centralizer independence statement holds without a facet assumption. -/
theorem unramifiedZeroFixerCentralizerIndependence :
    UnramifiedZeroFixerCentralizerIndependenceStatement.{u} := by
  intro F _ _ _ _ G _ C E N M _ _ Ω Ω' hN hM hne hne'
  exact ⟨unramifiedZeroFixerCentralizerIso C E N M Ω Ω' hN hM hne hne'⟩

end Langlands.BruhatTits.IntegralModels

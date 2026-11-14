import Langlands.BruhatTits.IntegralModels.UnramifiedIntegralRoots
import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots
import Langlands.Geometry.Building.UnramifiedSplitBoundedPoints

/-! # Actual integral tori and root models of unramified zero fixers -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)

/-- Bounded points of the apartment torus lie in every supplied zero fixer,
independently of the torus used to define its zero subgroup. -/
theorem map_apartmentTorus_characterValuationKernel_le_zeroFixer :
    (characterValuationKernel (MaximalUnramified.valuation F) C.S.toGrp).map
        (rationalPoints.map C.i) ≤
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) := by
  intro g hg
  exact ⟨E.map_split_characterValuationKernel_le_zeroPoints
      C.isConnectedReductive C.S C.i C.isMaximalSplitTorus.isSplitSubtorus hg,
    (map_apartmentTorus_characterValuationKernel_le_oneFixer C Ω hg).2⟩

/-- An actual closed integral apartment torus in a model characterized by
an arbitrary unramified zero fixer. No full one-fixer model is required. -/
theorem exists_unramifiedZeroFixerIntegralSplitTorusData
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    ∃ A : IntegralSplitTorusData N C.i, IsClosedSubgroup A.inclusion := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  have hv : ∀ a : (fixedFieldIntegers F)ˣ,
      MaximalUnramified.valuation F
        (algebraMap (fixedFieldIntegers F) (inertiaFixedField F) (a : fixedFieldIntegers F)) = 1 := by
    intro a
    have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
    have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
      (h.trans (map_one (fixedFieldValuation F)).symm)
    simpa only [map_one] using h'
  obtain ⟨T, j, e, hT, hj, hcomm⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      N (MaximalUnramified.valuation F) hv C.i
      C.isMaximalSplitTorus.isSplitSubtorus.1
      C.isMaximalSplitTorus.isSplitSubtorus.2
      (by rw [hN]; exact map_apartmentTorus_characterValuationKernel_le_zeroFixer C E Ω)
  exact ⟨⟨T, hT, j, e, hcomm⟩, hj⟩

/-- A chosen closed split torus, with actual generic identification and
commuting inclusion square, inside the supplied zero-fixer model. -/
def unramifiedZeroFixerIntegralSplitTorusData
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    IntegralSplitTorusData N C.i :=
  Classical.choose (exists_unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)

theorem unramifiedZeroFixerIntegralSplitTorusData_isClosedSubgroup
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    IsClosedSubgroup (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).inclusion :=
  Classical.choose_spec (exists_unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN)

variable [Smooth N.group.X.hom]

/-- The actual integral root-model image equals the root fixer for every
apartment subset, including the empty subset, and every zero datum. -/
theorem unramifiedZeroFixerRootModel_integralPoints_eq
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (a : relativeRoots C.i) :
    ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootModel a a.2.1).integralPoints.map
        (rationalPoints.map
          ((unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootInclusion a a.2.1)) =
      C.apartment.rootFixer a Ω := by
  rw [IntegralSplitTorusData.rootModel_integralPoints_eq, hN, inf_comm]
  exact rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω a

/-- A smooth affine geometrically connected filtration model constructed
from the actual zero-fixer model and its closed integral split torus. -/
def unramifiedZeroFixerRootFiltrationModelData
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      C.apartment x a (C.apartment.rootFixerDepth a x Ω) := by
  let A := unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN
  exact {
    rootGroup := A.rootGroup a a.2.1
    inclusion := A.rootInclusion a a.2.1
    isRootSubgroup := A.rootInclusion_isRootSubgroup a a.2.1
    model := A.rootModel a a.2.1
    smooth := IntegralModel.SplitRoot.model_isSmooth N A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
    geometricallyConnected := IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres
      N A.isSplit A.inclusion (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
    integralPoints_eq := (unramifiedZeroFixerRootModel_integralPoints_eq C E N Ω hN a).trans
      (C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb) }

/-- The constructed filtration model maps into the supplied zero-fixer
model by its actual integral root inclusion. -/
def unramifiedZeroFixerRootFiltrationModelMap
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    (unramifiedZeroFixerRootFiltrationModelData C E N Ω hN hne hb x a).model.Hom N
      (unramifiedZeroFixerRootFiltrationModelData C E N Ω hN hne hb x a).inclusion :=
  (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootModelMap a a.2.1

theorem unramifiedZeroFixerRootFiltrationModelMap_isClosedSubgroup
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    IsClosedSubgroup (unramifiedZeroFixerRootFiltrationModelMap C E N Ω hN hne hb x a).hom :=
  (unramifiedZeroFixerIntegralSplitTorusData C E N Ω hN).rootModelMap_isClosedSubgroup a a.2.1

end Langlands.BruhatTits.IntegralModels

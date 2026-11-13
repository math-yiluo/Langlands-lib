import Langlands.BruhatTits.IntegralModels.IntegralRootFiltration
import Langlands.GroupScheme.IntegralModel.SplitTorusBoundedPoints
import Langlands.Geometry.Building.ScalarTorusUnitsFixApartment
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData

/-! # Integral apartment tori and root models in a full unramified fixer model -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj ValuativeRel
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [ValuationRing R] [Infinite (IsLocalRing.ResidueField R)] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {v : Valuation K (WithZero (Multiplicative ℤ))}
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (C : IntegerValuationBuildingData v G)
    (N : IntegralModel R K G) (Ω : Set C.Apartment)

/-- Torus unit points belong to the full one-fixer of every apartment subset. -/
theorem map_apartmentTorus_characterValuationKernel_le_oneFixer :
    (characterValuationKernel v C.S.toGrp).map (rationalPoints.map C.i) ≤
      characterValuationKernel v G ⊓ C.pointwiseFixer (C.apartmentMap '' Ω) := by
  rintro _ ⟨t, ht, rfl⟩
  refine ⟨IntegerValuation.map_mem_characterValuationKernel v C.i ht, ?_⟩
  apply C.apartment.mem_pointwiseFixer.mpr
  rintro _ ⟨x, hx, rfl⟩
  have h := C.apartment.map_torusUnits_smul_apartmentMap v C.centralizer
    C.isOmegaCompatible (𝟙 C.S) t ht x
  change rationalPoints.map ((𝟙 C.S.toGrp) ≫ C.i) t • C.apartmentMap x =
    C.apartmentMap x at h
  simpa only [Category.id_comp] using h

/-- A full one-fixer model contains an actual closed integral split torus
with exactly the prescribed generic apartment torus and inclusion. -/
theorem exists_integralSplitTorusData_of_oneFixer
    (hv : ∀ a : Rˣ, v (algebraMap R K (a : R)) = 1)
    (hN : N.integralPoints =
      characterValuationKernel v G ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)) :
    ∃ A : IntegralSplitTorusData N C.i, IsClosedSubgroup A.inclusion := by
  obtain ⟨T, j, e, hT, hj, hcomm⟩ :=
    IntegralModel.SplitTorusClosure.exists_isSplitTorus_genericTorusMap_eq_of_bounded
      N v hv C.i C.isMaximalSplitTorus.isSplitSubtorus.1
      C.isMaximalSplitTorus.isSplitSubtorus.2
      (by rw [hN]; exact map_apartmentTorus_characterValuationKernel_le_oneFixer C Ω)
  exact ⟨⟨T, hT, j, e, hcomm⟩, hj⟩

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G)
    (N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G)
    (Ω : Set C.Apartment)

/-- The actual maximal-unramified integers have infinite residue field,
and all their units have normalized valuation one; thus the generic apartment
torus extends to a closed split torus of every full one-fixer model. -/
theorem exists_unramifiedIntegralSplitTorusData
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω)) :
    ∃ A : IntegralSplitTorusData N C.i, IsClosedSubgroup A.inclusion := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).1
  apply exists_integralSplitTorusData_of_oneFixer C N Ω ?_ hN
  intro a
  have h := (Valuation.valuationSubring.integers (fixedFieldValuation F)).valuation_unit a
  have h' := ((MaximalUnramified.valuation_isEquiv F).eq_iff).mpr
    (h.trans (map_one (fixedFieldValuation F)).symm)
  simpa only [map_one] using h'

/-- A chosen actual compatible integral apartment torus in the full model. -/
def unramifiedIntegralSplitTorusData
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω)) :
    IntegralSplitTorusData N C.i :=
  Classical.choose (exists_unramifiedIntegralSplitTorusData C N Ω hN)

theorem unramifiedIntegralSplitTorusData_isClosedSubgroup
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω)) :
    IsClosedSubgroup (unramifiedIntegralSplitTorusData C N Ω hN).inclusion :=
  Classical.choose_spec (exists_unramifiedIntegralSplitTorusData C N Ω hN)

variable [Smooth N.group.X.hom]

/-- Every relative root has an actual smooth affine geometrically connected
filtration model inside the full fixer model, with no supplied integral-torus
or root-image premise. -/
def unramifiedRootFiltrationModelData
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      C.apartment x a (C.apartment.rootFixerDepth a x Ω) :=
  (unramifiedIntegralSplitTorusData C N Ω hN).rootFiltrationModelData C.apartment
    C.isConnectedReductive C.isMaximalSplitTorus (MaximalUnramified.valuation F)
    x a Ω hne hb hN

/-- The actual root-filtration model has a compatible integral map into the
supplied full fixer model. -/
def unramifiedRootFiltrationModelMap
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    (unramifiedRootFiltrationModelData C N Ω hN hne hb x a).model.Hom N
      (unramifiedRootFiltrationModelData C N Ω hN hne hb x a).inclusion :=
  (unramifiedIntegralSplitTorusData C N Ω hN).rootFiltrationModelMap C.apartment
    C.isConnectedReductive C.isMaximalSplitTorus (MaximalUnramified.valuation F)
    x a Ω hne hb hN

theorem unramifiedRootFiltrationModelMap_isClosedSubgroup
    (hN : N.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F) G ⊓
        C.pointwiseFixer (C.apartmentMap '' Ω))
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    IsClosedSubgroup (unramifiedRootFiltrationModelMap C N Ω hN hne hb x a).hom :=
  (unramifiedIntegralSplitTorusData C N Ω hN).rootModelMap_isClosedSubgroup a a.2.1

end Unramified

end Langlands.BruhatTits.IntegralModels

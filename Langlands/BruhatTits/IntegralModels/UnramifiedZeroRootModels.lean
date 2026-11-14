import Langlands.BruhatTits.IntegralModels.UnramifiedZeroRoots

/-! # Root models in a characterized unramified zero-fixer model -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData

section General

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
    [Algebra R K] [IsFractionRing R K]
    {S : CommGroupScheme (Spec (CommRingCat.of K))}
    {G : GroupScheme (Spec (CommRingCat.of K))}
    {i : S.toGrp ⟶ G} {N : IntegralModel R K G}
    (A : IntegralSplitTorusData N i) [Smooth N.group.X.hom]

/-- The constructed root model represents the actual integral root functor,
not only its generic fibre or its integral-point image. -/
theorem rootModelMap_isRepresentedBy (a : characterLattice S) (ha : a ≠ 0) :
    (RelativeRoot.subgroup A.inclusion (A.integralCharacter a)).IsRepresentedBy
      (A.rootModelMap a ha).hom :=
  (IntegralModel.SplitRoot.integral_properties N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero ha)).1

end General

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    {N : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
    (A : IntegralSplitTorusData N C.i) [Smooth N.group.X.hom]
    (Ω : Set C.Apartment)
    (hN : N.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω))

include hN in
/-- For the exact zero-fixer characterization, the actual root model's
integral points have precisely the bounded-set root-filtration image. -/
theorem rootModel_integralPoints_eq_zeroFixerFiltration
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    (A.rootModel a a.2.1).integralPoints.map
        (rationalPoints.map (A.rootInclusion a a.2.1)) =
      C.apartment.filtration x a (C.apartment.rootFixerDepth a x Ω) := by
  rw [A.rootModel_integralPoints_eq a a.2.1, inf_comm, hN,
    rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer C E Ω a]
  exact C.apartment.rootFixer_eq_filtration_of_bounded a x hne hb

/-- A supplied compatible integral apartment torus in a smooth zero-fixer
model produces an actual smooth connected root-filtration model. No full
one-fixer model or separate filtration-image hypothesis is required. -/
def unramifiedZeroRootFiltrationModelData
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      C.apartment x a (C.apartment.rootFixerDepth a x Ω) where
  rootGroup := A.rootGroup a a.2.1
  inclusion := A.rootInclusion a a.2.1
  isRootSubgroup := A.rootInclusion_isRootSubgroup a a.2.1
  model := A.rootModel a a.2.1
  smooth := IntegralModel.SplitRoot.model_isSmooth N A.isSplit A.inclusion
    (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  geometricallyConnected :=
    IntegralModel.SplitRoot.model_hasGeometricallyConnectedFibres N A.isSplit A.inclusion
      (A.integralCharacter a) (A.integralCharacter_ne_zero a.2.1)
  integralPoints_eq :=
    A.rootModel_integralPoints_eq_zeroFixerFiltration C E Ω hN hne hb x a

/-- The constructed root-filtration model has its actual compatible integral
map into the supplied zero-fixer model. -/
def unramifiedZeroRootFiltrationModelMap
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    (A.unramifiedZeroRootFiltrationModelData C E Ω hN hne hb x a).model.Hom N
      (A.unramifiedZeroRootFiltrationModelData C E Ω hN hne hb x a).inclusion :=
  A.rootModelMap a a.2.1

theorem unramifiedZeroRootFiltrationModelMap_isClosedSubgroup
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    IsClosedSubgroup
      (A.unramifiedZeroRootFiltrationModelMap C E Ω hN hne hb x a).hom :=
  A.rootModelMap_isClosedSubgroup a a.2.1

theorem unramifiedZeroRootFiltrationModelMap_isRepresentedBy
    (hne : Ω.Nonempty) (hb : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (x : C.Apartment) (a : relativeRoots C.i) :
    (RelativeRoot.subgroup A.inclusion (A.integralCharacter a)).IsRepresentedBy
      (A.unramifiedZeroRootFiltrationModelMap C E Ω hN hne hb x a).hom :=
  A.rootModelMap_isRepresentedBy a a.2.1

end Unramified

end Langlands.BruhatTits.IntegralModels.IntegralSplitTorusData

import Langlands.Geometry.Building.KPUnramifiedComparisonExistenceStatement
import Langlands.Geometry.Building.UnramifiedBuildingDescentReduction
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof

/-! # Concrete special-torus apartment lifts for the unramified comparison -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

private instance unramifiedApartmentLiftAffineHom {F : Type u} [Field F]
    [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F (UnramifiedClosure F) G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F (UnramifiedClosure F)))
  infer_instance

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- A special torus containing the particular maximal split torus of `P`. -/
structure UnramifiedComparisonTorus where
  T : CommGroupScheme (Spec (CommRingCat.of F))
  iT : T.toGrp ⟶ G
  f : P.S ⟶ T
  factor : CommGroupScheme.groupHom f ≫ iT = P.i
  isClosedSubgroup : IsClosedSubgroup iT
  isMaximalSplitTorus : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map iT)

namespace UnramifiedComparisonTorus

variable {P} (t : P.UnramifiedComparisonTorus)

instance extendedMono :
    Mono ((GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map t.iT).hom.hom.left :=
  mono_of_isMaximalSplitTorus t.isMaximalSplitTorus

/-- The scalar extension `T_K` of the special torus. -/
abbrev upstairsTorus :=
  (CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).obj t.T

/-- The actual inclusion of `T_K` in `G_K`. -/
abbrev upstairsInclusion : t.upstairsTorus.toGrp ⟶ baseChanged F (UnramifiedClosure F) G :=
  (GroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map t.iT

set_option maxHeartbeats 1000000 in
/-- A compatible upstairs class together with the fixed-point lift of every point
of the supplied downstairs apartment. No root, Levi, zero or openness comparison
is part of this data. -/
structure ApartmentLift where
  apartment : KPApartmentData t.upstairsInclusion
    (IntegerValuation.order (MaximalUnramified.valuation F))
  centralizer : CentralizerDatum t.upstairsInclusion
  isOmegaCompatible :
    IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) apartment centralizer
  oppositeFactorPairs : RelativeRoot.HasOppositeFactorPairs t.upstairsInclusion
  e : P.Apartment → apartment.Apartment
  fixed : ∀ (y : P.Apartment) (σ : UnramifiedClosure F ≃ₐ[F] UnramifiedClosure F),
    RootFunctionFamily.galoisAction F (UnramifiedClosure F) t.T G σ (e y).val = (e y).val
  restrict :
    letI : Smooth G.X.hom := P.isConnectedReductive.smooth
    ∀ y : P.Apartment, y.val =
    torusFieldRestrictedRootFunctionFamily (k := F) (K := UnramifiedClosure F)
      P.isMaximalSplitTorus.isSplitSubtorus.1 t.isMaximalSplitTorus.isSplitSubtorus.1
      oppositeFactorPairs (apartment.isRootDatumValuation_of_mem (e y).mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (UnramifiedClosure F))).map t.f)
  normalizer : ∀ (n : normalizerPoints P.i) (y : P.Apartment),
    apartment.apartmentMap (e (n • y)) =
      rationalExtend F (UnramifiedClosure F) G (n : rationalPoints G) •
        apartment.apartmentMap (e y)

namespace ApartmentLift

variable {t} (L : t.ApartmentLift)

/-- The actual upstairs integer-valued building data of the lift. -/
abbrev buildingData :
    MaximalUnramified.BuildingData F (baseChanged F (UnramifiedClosure F) G) where
  isConnectedReductive :=
    connectedReductiveFieldExtensionStatement F (UnramifiedClosure F) G P.isConnectedReductive
  S := t.upstairsTorus
  i := t.upstairsInclusion
  isMaximalSplitTorus := t.isMaximalSplitTorus
  apartment := L.apartment
  centralizer := L.centralizer
  isOmegaCompatible := L.isOmegaCompatible

/-- Quasi-splitness of the actual unramified field group identifies the supplied
centralizer representative as a torus. -/
theorem centralizer_isTorus : IsTorus L.buildingData.centralizer.Z :=
  isTorus_of_quasiSplit_torusCentralizer
    quasiSplitTorusCentralizerExistence maximalSplitTorusConjugacy
    ((unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    F (baseChanged F (UnramifiedClosure F) G)
    L.buildingData.isConnectedReductive)
    t.isMaximalSplitTorus L.centralizer.isRepresentedBy

end ApartmentLift
end UnramifiedComparisonTorus
end ParahoricBuildingData

set_option maxHeartbeats 4000000 in
/-- Special-torus existence and valuation descent suffice to construct a concrete
apartment lift. The other inputs used here are published theorems. -/
theorem exists_unramifiedApartmentLift
    (hSpec : SpecialTorusExistenceStatement.{u})
    (hDesc : UnramifiedValuationDescentStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) :
    ∃ t : P.UnramifiedComparisonTorus, Nonempty t.ApartmentLift := by
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ :=
    hSpec F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus
  let t : P.UnramifiedComparisonTorus := ⟨T, iT, f, hf, hiTc, hiT⟩
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G P.isConnectedReductive
  obtain ⟨D, C, h6⟩ := UnramifiedBuildingDescent.exists_omegaCompatible
    (unramifiedQuasiSplit_of_henselianDiscrete henselianDiscreteQuasiSplit)
    quasiSplitIntegerApartmentExistence iT hGK hiT
  have hE : RelativeRoot.HasOppositeFactorPairs
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT) :=
    (RelativeRoot.hasRankOneFactorization_iff_hasOppositeFactorPairs _
      hiT.isSplitSubtorus.1).mp
      (rootRankOneFactorization (inertiaFixedField F) (baseChanged F (inertiaFixedField F) G)
        hGK _ _ hiT)
  obtain ⟨DS, CS, h6S, hcar, hinj, hnorm⟩ :=
    hDesc F G P.isConnectedReductive P.S P.i P.isMaximalSplitTorus T iT f hf hiT hE D C h6
  have hDS : DS = P.apartment :=
    omegaCompatibleApartmentUniqueness F G P.isConnectedReductive P.S P.i
      P.isMaximalSplitTorus P.centralizer DS P.apartment
      (h6S.of_centralizerDatum P.centralizer) P.isOmegaCompatible
  subst hDS
  let fixed : D.Apartment → Prop := fun x =>
    ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val
  let φ : D.Apartment → RootFunctionFamily P.S G := fun x =>
    torusFieldRestrictedRootFunctionFamily (k := F) (K := inertiaFixedField F)
      P.isMaximalSplitTorus.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE
      (D.isRootDatumValuation_of_mem x.mem)
      ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map f)
  refine ⟨t, ⟨{
    apartment := D
    centralizer := C
    isOmegaCompatible := h6
    oppositeFactorPairs := hE
    e := UnramifiedBuildingDescent.descentPoint P.toValuationBuildingData fixed φ hcar
    fixed := UnramifiedBuildingDescent.descentPoint_fixed P.toValuationBuildingData fixed φ hcar
    restrict := UnramifiedBuildingDescent.descentPoint_val P.toValuationBuildingData fixed φ hcar
    normalizer := ?_
  }⟩⟩
  exact UnramifiedBuildingDescent.descentPoint_normalizer'
    hGK hiT C h6 P.toValuationBuildingData fixed φ hcar hinj hnorm

end Langlands.Geometry.Building

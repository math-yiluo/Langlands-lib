import Langlands.Geometry.Building.UnramifiedFixedPointSplitTorusStatement
import Langlands.Geometry.Building.UnramifiedSpecialReferenceApartment
import Langlands.Geometry.Building.UnramifiedSpecialApartmentChamberProof
import Langlands.Geometry.Building.UnramifiedStableChamberResidue
import Langlands.BruhatTits.IntegralModels.UnramifiedRecoveredSplitSource
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedPairZeroModels
import Langlands.BruhatTits.IntegralModels.UnramifiedPairFacetSplitSource
import Langlands.Geometry.Building.TorusUnitFixationTransport

/-! # A maximal split torus whose unramified units fix the prescribed point -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option Elab.async false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 120000
set_option maxRecDepth 2500

open CategoryTheory AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj ValuativeRel Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

section ReferenceApartment

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]

private instance fixedPointTorusExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

local instance fixedPointSplitTorusIntegerAlgebra : Algebra ↥𝒪[F] (fixedFieldIntegers F) :=
  Valuation.HasExtension.instAlgebraInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance fixedPointSplitTorusIntegerScalarTower : IsScalarTower ↥𝒪[F] (fixedFieldIntegers F) (inertiaFixedField F) :=
  Valuation.HasExtension.instIsScalarTowerInteger
    (vR := ValuativeRel.valuation F) (vA := fixedFieldValuation F)
local instance fixedPointSplitTorusResidueAlgebra : Algebra 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (residueToFixedField F).toAlgebra
local instance fixedPointSplitTorusDiscreteValuationRing : IsDiscreteValuationRing (fixedFieldIntegers F) :=
  (separableUnramifiedArithmetic F).2.2.2.1
local instance fixedPointSplitTorusHenselianLocalRing : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
local instance fixedPointSplitTorusResidueIsAlgebraic : Algebra.IsAlgebraic 𝓀[F] (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).2
local instance fixedPointSplitTorusResidueFintype : Fintype 𝓀[F] := Fintype.ofFinite _
local instance fixedPointSplitTorusResidueIsAlgClosed : IsAlgClosed (ResidueField (fixedFieldIntegers F)) :=
  (fixedFieldResidueIsAlgClosure F).1

namespace KPApartmentData

variable (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))

/-- In a genuine special reference apartment, use its stable ordinary facet
as the source of the split torus lifted into the prescribed-point pair model. -/
theorem exists_maximalSplitTorus_fixing_of_specialApartment
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (h6 : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (hD : GaloisStable F (inertiaFixedField F) iT D)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hiS : IsMaximalSplitTorus iS) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS) (hj : IsClosedSubgroup iT)
    (q : D.ReducedBuilding)
    (hq : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      galoisQuotientAction F (inertiaFixedField F) iT D hD σ q = q) :
    ∃ (S' : CommGroupScheme (Spec (CommRingCat.of F))) (iS' : S'.toGrp ⟶ G),
      IsMaximalSplitTorus iS' ∧ IsFixedByUnramifiedTorusUnits F iS' q := by
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    hG.baseChange_of_algebraicExtension (K := inertiaFixedField F)
  let Z := UnramifiedZeroDatum.ofConnectedReductive
    (baseChanged F (inertiaFixedField F) G) hGK
  let B := integerBuildingData D hGK hiT C h6
  let M := unramifiedIntegerFacetModels Z B
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hgeom : GeometricallyConnected G.X.hom := G.geometricallyConnected_of_connected
  obtain ⟨x, hx, hstable⟩ := unramifiedSpecialApartmentChamber
    F G hG S iS hiS T iT f hf hj hiT D C h6 hD
  obtain ⟨Fc, N0, t, Q0, hFc, _hmax, hQ0, hpar⟩ :=
    unramifiedStableChamberResidue F iT D hD hGK hiT C h6 hgeom x hx hstable
  let R : RecoveredApartmentFixerModels D (AffineRootSystem.facet D.affineRoots x) :=
    { lower := N0
      upper := M.model Fc.val
      recovery := t
      full_integralPoints :=
        (unramifiedIntegerFacetModels_full_integralPoints Z B Fc.val).trans
          (congrArg (fun Ω => characterValuationKernel (MaximalUnramified.valuation F)
            (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer Ω) hFc) }
  obtain ⟨A, hA, a, ha, s, hs⟩ :=
    RecoveredApartmentFixerModels.exists_integralSplitSource hG C h6 hiS hf R Q0 hQ0
  obtain ⟨p, hpFc, hpfix⟩ := Fc.property
  obtain ⟨P, hPneutral⟩ := exists_recoveredFixedBuildingPairZeroModels
    D hG hiT C h6 hD Z p q hpfix hq
  obtain ⟨φ, j, _hjclosed, _hjresmap, _hjres, hjgen, hjfix⟩ :=
    unramifiedPairFacetSplitSource B Z P.lower N0 P.upper (M.model Fc.val) p q Fc.val
      ⟨P.recovery⟩ ⟨t⟩ hG hpFc P.full_integralPoints hPneutral
      (unramifiedIntegerFacetModels_neutral_integralPoints Z B Fc.val)
      Q0 hQ0 hpar A hA a ha s hs
  exact ⟨(CommGroupScheme.baseChange (Spec.algebraMap ↥𝒪[F] F)).obj A,
    P.lower.neutral.genericTorusMap A j, hjgen, hjfix⟩

end KPApartmentData
end ReferenceApartment

/-- The exact published fixed-point split-torus statement, with no added
hypotheses, in arbitrary universe and both characteristics. -/
theorem unramifiedFixedPointSplitTorus : UnramifiedFixedPointSplitTorusStatement.{u} := by
  intro F _ _ _ _ G hG T iT
  let : IsAffineHom G.X.hom := hG.isAffineHom
  intro hiT
  have := mono_of_isMaximalSplitTorus hiT
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left :=
    mono_of_isMaximalSplitTorus hiT
  intro D C h6 hD y hy
  obtain ⟨S, iS, hiS, T', j, f, hf, hj, hi', E, C', h6', hE, q, r, hqfix, hry, hr⟩ :=
    unramifiedSpecialReferenceApartment F G hG T iT hiT D C h6 hD y hy
  let := mono_of_isMaximalSplitTorus hi'
  have : Mono ((GroupScheme.baseChange
      (algebraBaseMap F (inertiaFixedField F))).map j).hom.hom.left :=
    mono_of_isMaximalSplitTorus hi'
  obtain ⟨S', iS', hiS', hfix⟩ :=
    KPApartmentData.exists_maximalSplitTorus_fixing_of_specialApartment
      E hG hi' C' h6' hE hiS f hf hj q hqfix
  refine ⟨S', iS', hiS', ?_⟩
  have hfixed : IsFixedByUnramifiedTorusUnits F iS' (r q) :=
    IsFixedByScalarTorusUnits.map hfix r hr
  rwa [hry] at hfixed

end Langlands.Geometry.Building

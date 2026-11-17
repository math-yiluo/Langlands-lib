import Langlands.BruhatTits.IntegralModels.UnramifiedParahoricModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedFixedBuildingPairRecovery
import Langlands.Geometry.Building.IntegerValuationCommonApartmentsProof

/-! # Recovered fixed building pairs with both exact fixer formulas -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 3200000

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))} {iT : T.toGrp ⟶ G}
  [Mono ((GroupScheme.baseChange
    (algebraBaseMap F (inertiaFixedField F))).map iT).hom.hom.left]
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT)
    (IntegerValuation.order (MaximalUnramified.valuation F)))

private instance fixedPairZeroExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- Actual compatible recovery of a building pair, retaining the neutral
zero-fixer identity as well as the full norm-one-fixer identity. -/
def HasRecoveredFixedBuildingPairZeroModels
    (Z : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (p q : D.ReducedBuilding) : Prop :=
  ∃ M : RecoveredBuildingFixerModels D {p, q},
    M.upper.neutral.integralPoints = Z.zeroPoints ⊓ D.pointwiseFixer {p, q}

/-- Choose one common translated apartment, construct both parahoric models
there, and descend the full model together with its actual neutral component. -/
theorem exists_recoveredFixedBuildingPairZeroModels
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (Z : UnramifiedZeroDatum F (baseChanged F (inertiaFixedField F) G))
    (p q : D.ReducedBuilding)
    (hp : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ p = p)
    (hq : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ q = q) :
    HasRecoveredFixedBuildingPairZeroModels D Z p q := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  obtain ⟨g, a, b, ha, hb⟩ := MaximalUnramified.commonApartments
    F (baseChanged F (inertiaFixedField F) G) B p q
  obtain ⟨E, hfull, hneutral⟩ := unramifiedParahoricModel
    F G B Z g {a, b} (Set.insert_nonempty a {b})
      (fun f => (((Set.finite_singleton b).insert a).image f).bddAbove)
  have himage : (fun x => g • B.apartmentMap x) '' ({a, b} : Set B.Apartment) =
      {p, q} := by
    simp only [Set.image_pair, IntegerValuationBuildingData.apartmentMap,
      KPApartmentData.apartmentMap, ha, hb]
  rw [himage] at hfull hneutral
  have hfull' : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {p, q} := by
    simpa only [B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer] using hfull
  have hneutral' : E.neutral.integralPoints =
      Z.zeroPoints ⊓ D.pointwiseFixer {p, q} := by
    simpa only [B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer] using hneutral
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hfixed : ∀ y ∈ ({p, q} : Set D.ReducedBuilding),
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hp
    · exact Set.mem_singleton_iff.mp hy ▸ hq
  obtain ⟨L, ⟨e⟩⟩ := exists_recovery_of_fixedBuildingSubset D
    G.geometricallyConnected_of_connected hD {p, q} hfixed E hfull'
  exact ⟨⟨L, E, e, hfull'⟩, hneutral'⟩

end Langlands.BruhatTits.IntegralModels

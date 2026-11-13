import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedChamberStatement
import Langlands.GroupScheme.SimplyConnected.LocalUnramifiedIwahoriModelStatement
import Langlands.Geometry.Building.MaximalUnramifiedAffineWeylStatement
import Langlands.Geometry.Building.UnramifiedTwistedChamberStatement
import Langlands.Geometry.Building.UnramifiedSpecialApartmentStatement
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.AffineChamberTransitivity

/-! # Assembly of the Galois-stable Iwahori chamber input from focused statements -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.LocalGalois.Separable
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.Geometry.Building

namespace Langlands.GroupScheme

/-- Quasi-splitness over the maximal unramified extension, special tori, the affine Weyl
group over that extension, twisted-stable chambers and the simply connected Iwahori model
imply `LocalSimplyConnectedUnramifiedChamberStatement`. -/
def LocalSimplyConnectedUnramifiedChamberAssemblyStatement : Prop :=
  UnramifiedQuasiSplitStatement.{u} →
  SpecialTorusExistenceStatement.{u} →
  MaximalUnramifiedAffineWeylStatement.{u} →
  UnramifiedTwistedChamberStatement.{u} →
  LocalSimplyConnectedUnramifiedIwahoriModelStatement.{u} →
  LocalSimplyConnectedUnramifiedChamberStatement.{u}

set_option maxHeartbeats 4000000 in
/-- Proof of the assembly: build the building data and its coefficient action from a special
torus, take the chamber stable under the trivial twist, its Iwahori model, and the chamber
transitivity coming from the affine Weyl group. -/
theorem localSimplyConnectedUnramifiedChamberAssembly :
    LocalSimplyConnectedUnramifiedChamberAssemblyStatement.{u} := by
  intro hQS hSpec hAW hTw hIw F _ _ _ _ G _ hSC
  have hG : IsConnectedReductive G := hSC.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  obtain ⟨S, iS, hiS⟩ := exists_maximalSplitTorus G
  obtain ⟨T, iT, f, hf, hiTc, hiT⟩ := hSpec F G hG S iS hiS
  have := mono_of_isMaximalSplitTorus hiT
  have hGK : IsConnectedReductive (baseChanged F (inertiaFixedField F) G) :=
    connectedReductiveFieldExtensionStatement F (inertiaFixedField F) G hG
  obtain ⟨D, C, h6⟩ := UnramifiedBuildingDescent.exists_omegaCompatible hQS
    quasiSplitIntegerApartmentExistence iT hGK hiT
  have hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D :=
    MaximalUnramified.galoisStable_of_isOmegaCompatible iT hiTc hGK hiT D C h6
  -- The chamber stable under the untwisted action.
  obtain ⟨Y₀, hY₀, hY₀σ⟩ := hTw F G hG T iT hiT D C h6 hD (fun _ => 1)
    (fun σ τ => by rw [map_one, mul_one])
    ⟨⊥, inferInstance, fun _ _ => rfl⟩
  have hY₀Γ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD).action σ '' Y₀ = Y₀ := by
    intro σ
    simpa only [one_smul] using hY₀σ σ
  obtain ⟨M, hMs, hMc, hMI⟩ := hIw F G hSC
    (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6)
    (UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD) Y₀ hY₀ hY₀Γ
  refine ⟨UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6,
    UnramifiedBuildingDescent.semilinearData iT hGK hiT C h6 hD, M, Y₀, hMs, hMc, hY₀, hY₀Γ,
    hMI, ?_, fun c hc hE => hTw F G hG T iT hiT D C h6 hD c hc hE⟩
  -- Chamber transitivity from the affine Weyl group.
  intro Y hY
  obtain ⟨hΨ, hW⟩ := hAW F (baseChanged F (inertiaFixedField F) G)
    (UnramifiedBuildingDescent.buildingData iT hGK hiT D C h6)
  obtain ⟨g₀, Ca₀, hCa₀, rfl⟩ := hY₀
  obtain ⟨g, Ca, hCa, rfl⟩ := hY
  obtain ⟨w, hw, -⟩ := affineChamberSimpleTransitivity _ _ _ hΨ Ca₀ Ca hCa₀ hCa
  obtain ⟨n, hn⟩ := hW w.2
  refine ⟨g * (n : rationalPoints (baseChanged F (inertiaFixedField F) G)) * g₀⁻¹, ?_⟩
  rw [Set.image_image, ← hw, Set.image_image]
  refine Set.image_congr fun x _ => ?_
  rw [← hn]
  simp only [mul_smul, inv_smul_smul, KPApartmentData.normalizerAffineEquiv_apply,
    IntegerValuationBuildingData.normalizer_smul_apartmentMap]

end Langlands.GroupScheme

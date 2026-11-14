import Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.Geometry.Building.UnramifiedApartmentModelInput
import Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly
import Langlands.Geometry.Building.UnramifiedVertexMaximalBoundedProof
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof
import Langlands.GroupScheme.IntegralModel.MaximalBoundedConstruction
import Langlands.GroupScheme.IntegralModel.SmoothIntersectionConstruction
import Langlands.GroupScheme.IntegralModel.UnramifiedSmoothDescentProof

/-! # Recovered full and neutral models of fixed building pairs -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u w

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building.KPApartmentData

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]
  {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
    ((GroupScheme.baseChange (algebraBaseMap k K)).map i) ω)

/-- The full character-kernel fixer of any coefficient-fixed building subset
is preserved and reflected by coefficient conjugation. -/
theorem rationalConjugate_mem_characterKernel_inf_buildingSubset_iff
    (hD : GaloisStable k K i D)
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation K Γ₀) (σ : K ≃ₐ[k] K)
    (hvaluation : ∀ t : K, valuation (σ t) = valuation t)
    (Y : Set D.ReducedBuilding)
    (hY : ∀ y ∈ Y, ∀ τ : K ≃ₐ[k] K,
      galoisQuotientAction k K i D hD τ y = y)
    (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈
        characterValuationKernel valuation (baseChanged k K G) ⊓ D.pointwiseFixer Y ↔
      g ∈ characterValuationKernel valuation (baseChanged k K G) ⊓
        D.pointwiseFixer Y := by
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    rationalConjugate_mem_characterValuationKernel_iff k K G valuation σ hvaluation,
    D.mem_pointwiseFixer, D.mem_pointwiseFixer]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  simpa only [hY y hy σ] using
    (galoisQuotientAction_smul_eq_iff k K i D hD σ g y)

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels

open Langlands.Geometry.Building

/-- Construct a smooth full model at any quotient point by choosing a translated
singleton in the supplied apartment. -/
theorem exists_smoothBuildingPointModel_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (B : MaximalUnramified.BuildingData F G) (y : B.ReducedBuilding) :
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G,
      M.IsSmooth ∧ M.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          B.pointwiseFixer {y} := by
  obtain ⟨g, x, rfl⟩ := B.exists_smul_apartmentMap y
  obtain ⟨M, hM, hMp⟩ := exists_smoothFullModel_of_vertexInputs
    hvertex MaximalUnramified.finiteVertexFixerApproximation hmaximal hintersection
    IntegralModel.finiteIndexEnlargement F G B g {x}
    (Set.singleton_nonempty x) (fun f => ((Set.finite_singleton x).image f).bddAbove)
  exact ⟨M, hM, by simpa only [Set.image_singleton] using hMp⟩

/-- The intersection of two separate singleton models realizes the exact pair
fixer. No common apartment for the endpoints is assumed. -/
theorem exists_smoothBuildingPairModel_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (B : MaximalUnramified.BuildingData F G) (y₁ y₂ : B.ReducedBuilding) :
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G,
      M.IsSmooth ∧ M.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          B.pointwiseFixer {y₁, y₂} := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    (fixedFieldResidueIsAlgClosure F).isAlgClosed
  obtain ⟨M, -, hMp⟩ := exists_smoothBuildingPointModel_of_vertexInputs
    hvertex hmaximal hintersection F G B y₁
  obtain ⟨N, -, hNp⟩ := exists_smoothBuildingPointModel_of_vertexInputs
    hvertex hmaximal hintersection F G B y₂
  obtain ⟨L, hL, -, -, hLp⟩ := hintersection (fixedFieldIntegers F)
    (inertiaFixedField F) G B.isConnectedReductive.smooth M N
  refine ⟨L, hL, ?_⟩
  rw [hLp, hMp, hNp]
  ext g
  simp only [Subgroup.mem_inf, IntegerValuationBuildingData.pointwiseFixer,
    B.apartment.mem_pointwiseFixer, Set.forall_mem_insert, Set.forall_mem_singleton]
  tauto

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

private instance buildingPairExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- Actual full and neutral models on both sides of the unramified extension,
with compatible recovery and the exact full fixer of a building subset. -/
structure RecoveredBuildingFixerModels (Y : Set D.ReducedBuilding) where
  lower : RelativeComponentModelData ↥𝒪[F] F G
  upper : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)
  recovery : UnramifiedComponentModelRecovery lower upper
  full_integralPoints : upper.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer Y

/-- The recovered lower full model has exactly the same upstairs fixer. -/
theorem RecoveredBuildingFixerModels.baseChange_full_integralPoints
    {Y : Set D.ReducedBuilding} (M : RecoveredBuildingFixerModels D Y) :
    M.lower.full.baseChangeUnramified.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer Y :=
  M.recovery.full_integralPoints_eq.trans M.full_integralPoints

/-- Every supplied component model with the full fixer of a coefficient-fixed
building subset descends by the published smooth-model descent theorem. -/
theorem exists_recovery_of_fixedBuildingSubset
    (hG : GeometricallyConnected G.X.hom)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (Y : Set D.ReducedBuilding)
    (hY : ∀ y ∈ Y, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hfull : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer Y) :
    ∃ L : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery L E) := by
  apply exists_unramified_componentModelRecovery
    IntegralModel.unramifiedSmoothModelDescent hG E
  intro σ g hg
  rw [hfull] at hg ⊢
  exact (D.rationalConjugate_mem_characterKernel_inf_buildingSubset_iff
    F (inertiaFixedField F) iT hD (MaximalUnramified.valuation F) σ
    (MaximalUnramified.valuation_galois F σ) Y hY g).mpr hg

/-- Three retained model-existence inputs suffice for compatible full and
neutral models of any two coefficient-fixed quotient points. -/
theorem exists_recoveredFixedBuildingPairModels_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (y₁ y₂ : D.ReducedBuilding)
    (hy₁ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₁ = y₁)
    (hy₂ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₂ = y₂) :
    Nonempty (RecoveredBuildingFixerModels D {y₁, y₂}) := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  obtain ⟨M, hM, hMp⟩ := exists_smoothBuildingPairModel_of_vertexInputs
    hvertex hmaximal hintersection F (baseChanged F (inertiaFixedField F) G) B y₁ y₂
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  have hgeom := G.geometricallyConnected_of_connected
  have hgeom' : GeometricallyConnected (baseChanged F (inertiaFixedField F) G).X.hom := by
    change GeometricallyConnected (CategoryTheory.Limits.pullback.snd G.X.hom
      (algebraBaseMap F (inertiaFixedField F)))
    infer_instance
  let E := M.relativeComponentModelDataOfSmooth hM hgeom'
  have hfull : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓ D.pointwiseFixer {y₁, y₂} := by
    simpa only [E, IntegralModel.relativeComponentModelDataOfSmooth_full,
      B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer] using hMp
  have hfixed : ∀ y ∈ ({y₁, y₂} : Set D.ReducedBuilding),
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y = y := by
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | hy
    · exact hy₁
    · exact Set.mem_singleton_iff.mp hy ▸ hy₂
  obtain ⟨L, ⟨e⟩⟩ := exists_recovery_of_fixedBuildingSubset D hgeom hD
    {y₁, y₂} hfixed E hfull
  exact ⟨⟨L, E, e, hfull⟩⟩

/-- Choose the actual recovered pair models from the three retained inputs;
the full integral-point equality and both recovery isomorphisms are fields. -/
def recoveredFixedBuildingPairModelsOfVertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (y₁ y₂ : D.ReducedBuilding)
    (hy₁ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₁ = y₁)
    (hy₂ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₂ = y₂) :
    RecoveredBuildingFixerModels D {y₁, y₂} :=
  Classical.choice (exists_recoveredFixedBuildingPairModels_of_vertexInputs
    D hvertex hmaximal hintersection hG hiT C hDC hD y₁ y₂ hy₁ hy₂)

/-- Construct compatible full and neutral models for any coefficient-fixed pair,
using the published proofs of all three model-existence inputs. -/
def recoveredFixedBuildingPairModels
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (hD : KPApartmentData.GaloisStable F (inertiaFixedField F) iT D)
    (y₁ y₂ : D.ReducedBuilding)
    (hy₁ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₁ = y₁)
    (hy₂ : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      KPApartmentData.galoisQuotientAction F (inertiaFixedField F) iT D hD σ y₂ = y₂) :
    RecoveredBuildingFixerModels D {y₁, y₂} :=
  recoveredFixedBuildingPairModelsOfVertexInputs D
    MaximalUnramified.vertexOneStabilizerMaximalBounded
    maximalBoundedIntegralModel IntegralModel.smoothIntersection
    hG hiT C hDC hD y₁ y₂ hy₁ hy₂

end Langlands.BruhatTits.IntegralModels

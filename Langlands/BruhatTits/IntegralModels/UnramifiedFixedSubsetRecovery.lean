import Langlands.BruhatTits.IntegralModels.UnramifiedFullModelConstruction
import Langlands.BruhatTits.IntegralModels.UnramifiedNeutralModelDescent
import Langlands.Geometry.Building.UnramifiedApartmentModelInput
import Langlands.Geometry.Building.UnramifiedFiniteVertexFixerAssembly
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementProof

/-! # Recovered models of coefficient-fixed apartment subsets -/

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

private instance fixedSubsetExtendedAffine :
    IsAffineHom (baseChanged k K G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

/-- A single coefficient-fixed representative makes its entire valuation class
stable under the actual coefficient action. -/
theorem galoisStable_of_fixed (x : D.Apartment)
    (hx : ∀ σ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G σ x.val = x.val) :
    GaloisStable k K i D := by
  apply (galoisStable_iff_equipollent k K i D x).mpr
  intro σ
  rw [hx σ]
  exact Equipollent.refl x.val

/-- Coefficient conjugation preserves and reflects the full norm-one fixer of
any subset whose apartment points are individually coefficient-fixed. -/
theorem rationalConjugate_mem_characterKernel_inf_pointwiseFixer_iff
    (hD : GaloisStable k K i D)
    {Γ₀ : Type w} [LinearOrderedCommGroupWithZero Γ₀]
    (valuation : Valuation K Γ₀) (σ : K ≃ₐ[k] K)
    (hvaluation : ∀ t : K, valuation (σ t) = valuation t)
    (Ω : Set D.Apartment)
    (hΩ : ∀ x ∈ Ω, ∀ τ : K ≃ₐ[k] K,
      RootFunctionFamily.galoisAction k K T G τ x.val = x.val)
    (g : rationalPoints (baseChanged k K G)) :
    rationalConjugate k K G σ g ∈
        characterValuationKernel valuation (baseChanged k K G) ⊓
          D.pointwiseFixer (D.apartmentMap '' Ω) ↔
      g ∈ characterValuationKernel valuation (baseChanged k K G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω) := by
  have hfixed (x : D.Apartment) (hx : x ∈ Ω) :
      galoisQuotientAction k K i D hD σ (D.apartmentMap x) = D.apartmentMap x := by
    rw [galoisQuotientAction_apartmentMap]
    congr 1
    apply Apartment.ext
    exact hΩ x hx σ
  rw [Subgroup.mem_inf, Subgroup.mem_inf,
    rationalConjugate_mem_characterValuationKernel_iff k K G valuation σ hvaluation,
    D.mem_pointwiseFixer, D.mem_pointwiseFixer]
  simp only [Set.forall_mem_image]
  apply and_congr_right
  intro _
  apply forall_congr'
  intro x
  apply forall_congr'
  intro hx
  simpa only [hfixed x hx] using
    (galoisQuotientAction_smul_eq_iff k K i D hD σ g (D.apartmentMap x))

end Langlands.Geometry.Building.KPApartmentData

namespace Langlands.BruhatTits.IntegralModels

open Langlands.Geometry.Building

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

private instance recoveryExtendedAffine :
    IsAffineHom (baseChanged F (inertiaFixedField F) G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom
    (algebraBaseMap F (inertiaFixedField F)))
  infer_instance

/-- Actual lower and upper component models, compatible full and neutral
recovery, and the exact upper full norm-one apartment-subset fixer. -/
structure RecoveredApartmentFixerModels (Ω : Set D.Apartment) where
  lower : RelativeComponentModelData ↥𝒪[F] F G
  upper : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G)
  recovery : UnramifiedComponentModelRecovery lower upper
  full_integralPoints : upper.full.integralPoints =
    characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) G) ⊓
      D.pointwiseFixer (D.apartmentMap '' Ω)

/-- A supplied upper full fixer model of a nonempty coefficient-fixed subset
descends together with its actual neutral component. -/
theorem exists_recovery_of_fixedSubset
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hG : GeometricallyConnected G.X.hom)
    (Ω : Set D.Apartment) (hne : Ω.Nonempty)
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (E : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hfull : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω)) :
    ∃ L : RelativeComponentModelData ↥𝒪[F] F G,
      Nonempty (UnramifiedComponentModelRecovery L E) := by
  obtain ⟨x, hx⟩ := hne
  have hD := D.galoisStable_of_fixed F (inertiaFixedField F) iT x (hΩ x hx)
  apply exists_unramified_componentModelRecovery hdescent hG E
  intro σ g hg
  rw [hfull] at hg ⊢
  exact (D.rationalConjugate_mem_characterKernel_inf_pointwiseFixer_iff
    F (inertiaFixedField F) iT hD (MaximalUnramified.valuation F) σ
    (MaximalUnramified.valuation_galois F σ) Ω hΩ g).mpr hg

/-- The published finite-vertex and finite-index-enlargement proofs reduce
recovered fixed-subset model existence to the three remaining full-model inputs
and smooth descent. -/
theorem exists_recoveredFixedSubsetModels_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
    (hG : IsConnectedReductive G)
    (hiT : IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (C : CentralizerDatum
      (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
      ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (Ω : Set D.Apartment) (hne : Ω.Nonempty)
    (hbounded : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    Nonempty (RecoveredApartmentFixerModels D Ω) := by
  let B := MaximalUnramified.buildingDataOfApartment hG hiT D C hDC
  obtain ⟨E, hE⟩ := exists_relativeComponentModelData_of_vertexInputs
    hvertex MaximalUnramified.finiteVertexFixerApproximation hmaximal hintersection
    IntegralModel.finiteIndexEnlargement F (baseChanged F (inertiaFixedField F) G)
    B 1 Ω hne hbounded
  have hfull : E.full.integralPoints =
      characterValuationKernel (MaximalUnramified.valuation F)
          (baseChanged F (inertiaFixedField F) G) ⊓
        D.pointwiseFixer (D.apartmentMap '' Ω) := by
    simpa only [B, MaximalUnramified.buildingDataOfApartment,
      IntegerValuationBuildingData.pointwiseFixer,
      IntegerValuationBuildingData.apartmentMap, one_smul] using hE
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨L, ⟨e⟩⟩ := exists_recovery_of_fixedSubset D hdescent
    G.geometricallyConnected_of_connected Ω hne hΩ E hfull
  exact ⟨⟨L, E, e, hfull⟩⟩

section Choice

variable
  (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
  (hmaximal : MaximalBoundedIntegralModelStatement.{u})
  (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
  (hdescent : IntegralModel.UnramifiedSmoothModelDescentStatement.{u})
  (hG : IsConnectedReductive G)
  (hiT : IsMaximalSplitTorus
    (T := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (C : CentralizerDatum
    (S := (CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj T)
    ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iT))
  (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)

/-- Choose actual compatible lower and upper models of a nonempty bounded
coefficient-fixed subset from the remaining full-model inputs and smooth descent. -/
def recoveredFixedSubsetModelsOfVertexInputs
    (Ω : Set D.Apartment) (hne : Ω.Nonempty)
    (hbounded : ∀ f : D.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω))
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D Ω :=
  Classical.choice (exists_recoveredFixedSubsetModels_of_vertexInputs
    D hvertex hmaximal hintersection hdescent hG hiT C hDC Ω hne hbounded hΩ)

/-- A finite subset needs no separately supplied affine boundedness proof. -/
def recoveredFixedFiniteSubsetModelsOfVertexInputs
    (Ω : Set D.Apartment) (hfinite : Ω.Finite) (hne : Ω.Nonempty)
    (hΩ : ∀ x ∈ Ω, ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D Ω :=
  recoveredFixedSubsetModelsOfVertexInputs D hvertex hmaximal hintersection
    hdescent hG hiT C hDC Ω hne (fun f => (hfinite.image f).bddAbove) hΩ

/-- In particular an actual recovered singleton model is available at every
coefficient-fixed point under the four retained global inputs. -/
def recoveredFixedPointModelsOfVertexInputs (x : D.Apartment)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val) :
    RecoveredApartmentFixerModels D {x} :=
  recoveredFixedFiniteSubsetModelsOfVertexInputs D hvertex hmaximal hintersection
    hdescent hG hiT C hDC {x} (Set.finite_singleton x) (Set.singleton_nonempty x)
    (by simpa only [Set.forall_mem_singleton] using hx)

/-- Two individually fixed endpoints give an actual two-point model. No
constancy of full point fixers on facet closures is required. -/
def recoveredFixedPairModelsOfVertexInputs (x y : D.Apartment)
    (hx : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ x.val = x.val)
    (hy : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      RootFunctionFamily.galoisAction F (inertiaFixedField F) T G σ y.val = y.val) :
    RecoveredApartmentFixerModels D {x, y} :=
  recoveredFixedFiniteSubsetModelsOfVertexInputs D hvertex hmaximal hintersection
    hdescent hG hiT C hDC {x, y} ((Set.finite_singleton y).insert x)
    (Set.insert_nonempty x {y}) (by
      intro z hz
      rcases Set.mem_insert_iff.mp hz with rfl | hz
      · exact hx
      · exact Set.mem_singleton_iff.mp hz ▸ hy)

end Choice

end Langlands.BruhatTits.IntegralModels

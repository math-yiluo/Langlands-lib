import Langlands.Geometry.Building.UnramifiedTorusUnitGaloisFixedPointStatement
import Langlands.Geometry.Building.UnramifiedSemilinearMetricActionStatement
import Langlands.Geometry.Building.QuasiSplitIntegerApartmentExistenceProof
import Langlands.Geometry.Building.UnramifiedQuasiSplitReduction
import Langlands.Geometry.Building.TorusUnitApartmentFixation
import Langlands.Geometry.Building.UnramifiedFixedPointStabilizer
import Langlands.Geometry.Metric.KPBoundedSetStabilizerProof
import Langlands.Geometry.Metric.KPCompleteNPCGeodesicProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof

/-! # A finite-orbit route to simultaneous fixation -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private instance finiteOrbitExtendedAffine
    {F : Type u} [Field F] {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom (Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

/-- A finite Galois orbit of a torus-unit-fixed point gives a simultaneous
fixed point when both actions are isometric on a complete NPC metric space. -/
theorem exists_commonFixedPoint_of_finiteOrbit
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    {S : CommGroupScheme (Spec (CommRingCat.of F))}
    (iS : S.toGrp ⟶ G)
    {Y : Type v} [MulAction (rationalPoints (baseChanged F (inertiaFixedField F) G)) Y]
    [MetricSpace Y] [CompleteSpace Y]
    (hNPC : Metric.KP.IsNonpositivelyCurved Y)
    (hGiso : ∀ g : rationalPoints (baseChanged F (inertiaFixedField F) G),
      Isometry (fun z : Y => g • z))
    (ρ : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →* Equiv.Perm Y)
    (hsemi : ∀ (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (g : rationalPoints (baseChanged F (inertiaFixedField F) G)) (z : Y),
      ρ σ (g • z) = rationalConjugate F (inertiaFixedField F) G σ g • ρ σ z)
    (hρiso : ∀ σ, Isometry (ρ σ))
    (x : Y) (hx : IsFixedByUnramifiedTorusUnits F iS x)
    (hfinite : (Set.range (fun σ => ρ σ x)).Finite) :
    ∃ y : Y, (∀ σ, ρ σ y = y) ∧ IsFixedByUnramifiedTorusUnits F iS y := by
  let O : Set Y := Set.range (fun σ => ρ σ x)
  have hO : O.Nonempty := ⟨ρ 1 x, ⟨1, rfl⟩⟩
  have hunit (t : rationalPoints (baseChanged F (inertiaFixedField F) S.toGrp))
      (ht : t ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) S.toGrp))
      (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F) :
      rationalPoints.map
        ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS) t •
          ρ σ x = ρ σ x := by
    let t' := rationalConjugate F (inertiaFixedField F) S.toGrp σ⁻¹ t
    have ht' : t' ∈ characterValuationKernel (MaximalUnramified.valuation F)
        (baseChanged F (inertiaFixedField F) S.toGrp) :=
      (rationalConjugate_mem_characterValuationKernel_iff F (inertiaFixedField F)
        S.toGrp (MaximalUnramified.valuation F) σ⁻¹
        (MaximalUnramified.valuation_galois F σ⁻¹) t).mpr ht
    have heq := congrArg (ρ σ) (hx t' ht')
    rw [hsemi, rationalConjugate_map] at heq
    simpa only [t', ← rationalConjugate_mul, mul_inv_cancel, rationalConjugate_one]
      using heq
  obtain ⟨y, hy⟩ := Metric.KP.boundedSetStabilizerFixedPoint Y hNPC
    (Metric.KP.isGeodesicSpace_of_complete_npc hNPC) O hO hfinite.isBounded
  refine ⟨y, ?_, ?_⟩
  · intro σ
    let e : Y ≃ᵢ Y := ⟨ρ σ, hρiso σ⟩
    apply hy e
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨τ, rfl⟩, rfl⟩
      exact ⟨σ * τ, by change (ρ (σ * τ)) x = _; rw [map_mul]; rfl⟩
    · rintro _ ⟨τ, rfl⟩
      refine ⟨ρ (σ⁻¹ * τ) x, ⟨σ⁻¹ * τ, rfl⟩, ?_⟩
      change (ρ σ * ρ (σ⁻¹ * τ)) x = ρ τ x
      rw [← map_mul, mul_inv_cancel_left]
  · intro t ht
    let g := rationalPoints.map
      ((GroupScheme.baseChange (baseMap F (inertiaFixedField F))).map iS) t
    let e : Y ≃ᵢ Y :=
      { toEquiv :=
          { toFun := fun z => g • z
            invFun := fun z => g⁻¹ • z
            left_inv := inv_smul_smul g
            right_inv := smul_inv_smul g }
        isometry_toFun := hGiso g }
    apply hy e
    apply Set.Subset.antisymm
    · rintro _ ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, (hunit t ht σ).symm⟩
    · rintro _ ⟨σ, rfl⟩
      exact ⟨ρ σ x, ⟨σ, rfl⟩, hunit t ht σ⟩

/-- The torus-specific fixed-point claim reduces to unramified quasi-splitness
and the semilinear metric action, without a bounded-subgroup theorem. -/
theorem unramifiedTorusUnitGaloisFixedPoint_of_semilinearMetricAction
    (hq : UnramifiedQuasiSplitStatement.{u})
    (hmetric : UnramifiedSemilinearMetricActionStatement.{u}) :
    UnramifiedTorusUnitGaloisFixedPointStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let K := inertiaFixedField F
  let GK := baseChanged F K G
  have hGK : IsConnectedReductive GK :=
    connectedReductiveFieldExtensionStatement F K G hG
  let : Smooth GK.X.hom := hGK.smooth
  let : LocallyOfFiniteType GK.X.hom := inferInstance
  let SK := (CommGroupScheme.baseChange (baseMap F K)).obj S
  let iSK : SK.toGrp ⟶ GK := (GroupScheme.baseChange (baseMap F K)).map iS
  have hiSK : IsSplitSubtorus iSK :=
    ⟨hiS.1.1.baseChange _, hiS.1.2.baseChange _⟩
  obtain ⟨A, iA, hiA, e, he⟩ := exists_maximalSplitTorus_extension GK iSK hiSK
  let := mono_of_isMaximalSplitTorus hiA
  obtain ⟨D, Z, hD⟩ := quasiSplitIntegerApartmentExistence K
    (MaximalUnramified.valuation F) (MaximalUnramified.valuation_surjective F)
    (MaximalUnramified.valuationSubring_isHenselian F) GK (hq F GK hGK) A iA hiA
  let C : MaximalUnramified.BuildingData F GK :=
    { isConnectedReductive := hGK
      S := A
      i := iA
      isMaximalSplitTorus := hiA
      apartment := D
      centralizer := Z
      isOmegaCompatible := hD }
  obtain ⟨m, hcomplete, hNPC, hGiso, ρ, hsemi, hρiso, hfinite⟩ := hmetric F G hG C
  let := m
  let := hcomplete
  obtain ⟨a⟩ := (inferInstance : Nonempty D.Apartment)
  have hx : IsFixedByUnramifiedTorusUnits F iS (C.apartmentMap a) := by
    intro t ht
    change rationalPoints.map iSK t • D.apartmentMap a = D.apartmentMap a
    rw [← he]
    exact torusUnitApartmentFixation K (MaximalUnramified.valuation F) SK.toGrp
      A GK iA D Z hD e t ht a
  obtain ⟨y, hy, hunits⟩ := exists_commonFixedPoint_of_finiteOrbit F iS
    hNPC (fun g => hGiso.isometry_smul g) ρ hsemi hρiso (C.apartmentMap a) hx (hfinite _)
  exact ⟨C, ρ, y, hsemi, hy, hunits⟩

/-- Published dimension-one quasi-splitness discharges the field-theoretic input,
leaving only the coherent finite-orbit metric action. -/
theorem unramifiedTorusUnitGaloisFixedPoint_of_metricAction
    (hmetric : UnramifiedSemilinearMetricActionStatement.{u}) :
    UnramifiedTorusUnitGaloisFixedPointStatement.{u} :=
  unramifiedTorusUnitGaloisFixedPoint_of_semilinearMetricAction
    (unramifiedQuasiSplit_of_henselianDiscrete
      (henselianDiscreteQuasiSplit_of_dimensionLEOne dimensionLEOneQuasiSplit)) hmetric

end Langlands.Geometry.Building

import Langlands.Geometry.Building.UnramifiedVertexFixerStatements
import Langlands.GroupScheme.IntegralModel.MaximalBounded
import Langlands.GroupScheme.IntegralModel.SmoothIntersection
import Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.BruhatTits.IntegralModels.RelativeComponentConstruction

/-! # Conditional construction of the full unramified fixer model -/

noncomputable section

set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped ValuativeRel CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.GroupScheme.IntegralModel

/-- Iterate a supplied binary smooth-intersection theorem over a nonempty
finite family of subgroups already realized by smooth integral models. -/
theorem exists_smoothModel_finset_iInf
    (hintersection : SmoothIntersectionStatement.{u})
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [HenselianLocalRing R] [IsAlgClosed (IsLocalRing.ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K]
    {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
    (hG : Smooth G.X.hom)
    {α : Type*} (B : α → Subgroup (rationalPoints G))
    (Y : Finset α) (hY : Y.Nonempty)
    (hmodels : ∀ y ∈ Y, ∃ M : IntegralModel R K G,
      M.IsSmooth ∧ M.integralPoints = B y) :
    ∃ M : IntegralModel R K G,
      M.IsSmooth ∧ M.integralPoints = ⨅ y ∈ Y, B y := by
  classical
  induction hY using Finset.Nonempty.cons_induction with
  | singleton y =>
    simpa only [Finset.mem_singleton, iInf_iInf_eq_left] using
      hmodels y (Finset.mem_singleton_self y)
  | cons y Y hy hY ih =>
    obtain ⟨M, hM, hMp⟩ := hmodels y (Finset.mem_cons_self y Y)
    obtain ⟨N, hN, hNp⟩ := ih (fun z hz => hmodels z (Finset.mem_cons_of_mem hz))
    obtain ⟨L, hL, -, -, hLp⟩ := hintersection R K G hG M N
    refine ⟨L, hL, ?_⟩
    rw [hLp, hMp, hNp]
    simp only [Finset.cons_eq_insert, Finset.iInf_insert]

end Langlands.GroupScheme.IntegralModel

namespace Langlands.BruhatTits.IntegralModels

private instance fullModelGenericAffine
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom] : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

/-- Maximal boundedness and the general maximal-bounded model theorem give an
actual vertex model over the published fixed-field integer ring. -/
theorem exists_smoothVertexModel_of_maximalBounded
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (y : C.ReducedBuilding)
    (hy : C.IsVertex y) :
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G,
      M.IsSmooth ∧ M.integralPoints = C.oneStabilizer y := by
  let := ValuativeRel.ofValuation (fixedFieldValued F).v
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  have hmodel (A : ValuationSubring (inertiaFixedField F))
      (hA : A = (ValuativeRel.valuation (inertiaFixedField F)).valuationSubring)
      [IsDiscreteValuationRing A] [HenselianLocalRing A]
      [IsAlgClosed (IsLocalRing.ResidueField A)] :
      ∃ M : IntegralModel A (inertiaFixedField F) G,
        M.IsSmooth ∧ M.integralPoints = C.oneStabilizer y := by
    subst A
    exact hmaximal (inertiaFixedField F) G C.isConnectedReductive.smooth
      (C.oneStabilizer y) (hvertex F G C y hy)
  exact hmodel (fixedFieldIntegers F) (fixedFieldIntrinsicIntegers_eq F).symm

/-- The five supplied geometric and schematic inputs construct the smooth
full model with exactly the norm-one pointwise fixer as its integral points. -/
theorem exists_smoothFullModel_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hfinite : MaximalUnramified.FiniteVertexFixerApproximationStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (henlargement : IntegralModel.FiniteIndexEnlargementStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (g : rationalPoints G)
    (Ωa : Set C.Apartment) (hne : Ωa.Nonempty)
    (hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) :
    ∃ M : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G,
      M.IsSmooth ∧ M.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : HenselianLocalRing (fixedFieldIntegers F) := fixedFieldIntegersIsHenselian F
  let := (residueToFixedField F).toAlgebra
  let : IsAlgClosure 𝓀[F] (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    fixedFieldResidueIsAlgClosure F
  let : IsAlgClosed (IsLocalRing.ResidueField (fixedFieldIntegers F)) :=
    IsAlgClosure.isAlgClosed 𝓀[F]
  obtain ⟨Y, hY, hvertices, hle, hnormal, hindex⟩ :=
    hfinite F G C g Ωa hne hbounded
  obtain ⟨M, hM, hMp⟩ := IntegralModel.exists_smoothModel_finset_iInf
    hintersection C.isConnectedReductive.smooth C.oneStabilizer Y hY
    (fun y hy => exists_smoothVertexModel_of_maximalBounded
      hvertex hmaximal F G C y (hvertices y hy))
  let H := characterValuationKernel (MaximalUnramified.valuation F) G ⊓
    C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa)
  have hle' : M.integralPoints ≤ H := by
    rw [hMp]
    exact hle
  have hnormal' : (M.integralPoints.subgroupOf H).Normal := by
    simpa only [hMp] using hnormal
  have hindex' : (M.integralPoints.subgroupOf H).FiniteIndex := by
    simpa only [hMp] using hindex
  obtain ⟨N, j, hN⟩ := henlargement (fixedFieldIntegers F) (inertiaFixedField F)
    G C.isConnectedReductive.smooth M hM H hle' hnormal' hindex'
  exact ⟨N, hN.1, hN.2.1⟩

/-- Package the conditionally constructed full model with its actual affine
relative identity component, retaining the exact full integral-point equality.
The neutral integral-point equality is a separate obligation. -/
theorem exists_relativeComponentModelData_of_vertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hfinite : MaximalUnramified.FiniteVertexFixerApproximationStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (henlargement : IntegralModel.FiniteIndexEnlargementStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (g : rationalPoints G)
    (Ωa : Set C.Apartment) (hne : Ωa.Nonempty)
    (hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) :
    ∃ D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G,
      D.full.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) := by
  let : IsDiscreteValuationRing (fixedFieldIntegers F) :=
    fixedFieldIntegersIsDVR_of_valuesFromBase F (fixedFieldValuesFromBase F)
  let : Smooth G.X.hom := C.isConnectedReductive.smooth
  let : ConnectedSpace G.X.left := C.isConnectedReductive.connectedSpace
  obtain ⟨M, hM, hMp⟩ := exists_smoothFullModel_of_vertexInputs hvertex hfinite
    hmaximal hintersection henlargement F G C g Ωa hne hbounded
  refine ⟨M.relativeComponentModelDataOfSmooth hM G.geometricallyConnected_of_connected, ?_⟩
  simpa only [IntegralModel.relativeComponentModelDataOfSmooth_full] using hMp

/-- Choose the actual compatible full and neutral models constructed from the
five closed vertex and model inputs. -/
def relativeComponentModelDataOfVertexInputs
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hfinite : MaximalUnramified.FiniteVertexFixerApproximationStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (henlargement : IntegralModel.FiniteIndexEnlargementStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (g : rationalPoints G)
    (Ωa : Set C.Apartment) (hne : Ωa.Nonempty)
    (hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) :
    RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G :=
  Classical.choose (exists_relativeComponentModelData_of_vertexInputs
    hvertex hfinite hmaximal hintersection henlargement F G C g Ωa hne hbounded)

/-- The chosen construction retains the exact full integral-point subgroup. -/
theorem relativeComponentModelDataOfVertexInputs_full_integralPoints
    (hvertex : MaximalUnramified.VertexOneStabilizerMaximalBoundedStatement.{u})
    (hfinite : MaximalUnramified.FiniteVertexFixerApproximationStatement.{u})
    (hmaximal : MaximalBoundedIntegralModelStatement.{u})
    (hintersection : IntegralModel.SmoothIntersectionStatement.{u})
    (henlargement : IntegralModel.FiniteIndexEnlargementStatement.{u})
    (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F))))
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (g : rationalPoints G)
    (Ωa : Set C.Apartment) (hne : Ωa.Nonempty)
    (hbounded : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ωa)) :
    (relativeComponentModelDataOfVertexInputs hvertex hfinite hmaximal
      hintersection henlargement F G C g Ωa hne hbounded).full.integralPoints =
        characterValuationKernel (MaximalUnramified.valuation F) G ⊓
          C.pointwiseFixer ((fun x => g • C.apartmentMap x) '' Ωa) :=
  Classical.choose_spec (exists_relativeComponentModelData_of_vertexInputs
    hvertex hfinite hmaximal hintersection henlargement F G C g Ωa hne hbounded)

end Langlands.BruhatTits.IntegralModels

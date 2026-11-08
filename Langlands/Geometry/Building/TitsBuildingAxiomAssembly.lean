import Langlands.Geometry.Building.TitsRestrictedRealization
import Langlands.Geometry.Building.TitsNormalizerApartmentStabilizer
import Langlands.GroupScheme.Rational.TorusTransporterOrbit

/-! # The torus correspondence and KP Axiom 4.1.1 for the restricted Tits realization -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.Group Langlands.Group.TitsSystem
open Langlands.BruhatTits.IntegralModels

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- `g S g⁻¹` is the conjugate of the subgroup functor `S` by `g`. -/
theorem conjTorus_eq_smul_range (g : rationalPoints G) :
    B.conjTorus g = g • SubgroupFunctor.range B.i :=
  (SubgroupFunctor.basePoint_smul_range B.i g).symm

/-- `g S g⁻¹ = h S h⁻¹` exactly when `h⁻¹ g` normalizes `S`. -/
theorem conjTorus_eq_conjTorus_iff (g h : rationalPoints G) :
    B.conjTorus g = B.conjTorus h ↔ h⁻¹ * g ∈ normalizerPoints B.i := by
  rw [B.conjTorus_eq_smul_range, B.conjTorus_eq_smul_range,
    ← stabilizer_range_eq_normalizerPoints B.i, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

/-- Under the normalizer-stabilizer clause, `g S g⁻¹ = h S h⁻¹` exactly when
`g · A(S) = h · A(S)`. -/
theorem conjTorus_eq_iff_of_normalizer (hnorm : B.HasNormalizerApartmentStabilizer)
    (g h : rationalPoints G) :
    B.conjTorus g = B.conjTorus h ↔ g • B.apartmentImage = h • B.apartmentImage := by
  rw [B.conjTorus_eq_conjTorus_iff, ← hnorm, MulAction.mem_stabilizer_iff, mul_smul,
    inv_smul_eq_iff]

/-- KP Corollary 7.6.9 as a bijection: under the normalizer-stabilizer clause,
`g S g⁻¹ ↦ g · A(S)` is a well-defined bijection from the conjugates of `S`
onto the apartments. -/
noncomputable def conjTorusApartmentEquiv (hnorm : B.HasNormalizerApartmentStabilizer) :
    Set.range B.conjTorus ≃ {Y : Set B.ReducedBuilding // B.IsApartment Y} where
  toFun T := ⟨T.2.choose • B.apartmentImage, ⟨_, rfl⟩⟩
  invFun Y := ⟨B.conjTorus Y.2.choose, ⟨_, rfl⟩⟩
  left_inv T := by
    apply Subtype.ext
    have hY := (⟨T.2.choose • B.apartmentImage, ⟨_, rfl⟩⟩ :
      {Y : Set B.ReducedBuilding // B.IsApartment Y}).2.choose_spec
    change B.conjTorus _ = T.1
    rw [← T.2.choose_spec, B.conjTorus_eq_iff_of_normalizer hnorm]
    exact hY.symm
  right_inv Y := by
    apply Subtype.ext
    have hT := (⟨B.conjTorus Y.2.choose, ⟨_, rfl⟩⟩ : Set.range B.conjTorus).2.choose_spec
    change _ • B.apartmentImage = Y.1
    rw [Y.2.choose_spec]
    exact (B.conjTorus_eq_iff_of_normalizer hnorm _ _).mp hT

theorem conjTorusApartmentEquiv_apply (hnorm : B.HasNormalizerApartmentStabilizer)
    (g : rationalPoints G) :
    ((B.conjTorusApartmentEquiv hnorm ⟨B.conjTorus g, ⟨g, rfl⟩⟩ :
      {Y : Set B.ReducedBuilding // B.IsApartment Y}) : Set B.ReducedBuilding) =
      g • B.apartmentImage := by
  have h := (⟨B.conjTorus g, ⟨g, rfl⟩⟩ : Set.range B.conjTorus).2.choose_spec
  exact (B.conjTorus_eq_iff_of_normalizer hnorm _ _).mp h

/-- KP Corollary 7.6.9: conjugacy of maximal split tori and the normalizer
stabilizer clause give the torus–apartment correspondence. -/
theorem hasTorusApartmentCorrespondence
    (hconj : MaximalSplitTorusConjugacyStatement.{u})
    (hnorm : B.HasNormalizerApartmentStabilizer) :
    B.HasTorusApartmentCorrespondence where
  exists_torusChart := B.exists_torusChart_of_maximalSplitTorusConjugacy hconj
  conjTorus_eq_iff := B.conjTorus_eq_iff_of_normalizer hnorm

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G) {Ca : Set P.Apartment}

variable [P.normalizerZero.Normal] [P.zeroSubgroup.Normal]

/-- KP Axiom 4.1.1 for the restricted Tits realization of the literal affine
Tits datum. The torus and normalizer clauses are derived from KP Fact 2.6.22
and the conjugacy of maximal split tori, both supplied as the published
statements. -/
theorem satisfiesBuildingAxiom_affineTitsRealization_of_statements
    (e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots)
    (hA : AffineRootSystem.IsAffineRootSystemWithRankZero P.affineRoots)
    (hCa : AffineRootSystem.IsChamber P.affineRoots Ca)
    (hT : P.IsBuildingTitsSystem Ca P.affineTitsProjection (P.chamberSimpleInAffinePart e Ca))
    (hfact : SimplyConnectedCentralizerProductStatement.{u})
    (hconj : MaximalSplitTorusConjugacyStatement.{u}) :
    P.SatisfiesBuildingAxiom hT.titsRealization :=
  have hnorm : P.HasNormalizerApartmentStabilizer :=
    hT.hasNormalizerApartmentStabilizer_of_simplyConnectedCentralizerProduct hCa.isFacet hfact
  P.satisfiesBuildingAxiom_affineTitsRealization e hA hCa hT
    (P.toValuationBuildingData.hasTorusApartmentCorrespondence hconj hnorm) hnorm

end ParahoricBuildingData

end Langlands.Geometry.Building

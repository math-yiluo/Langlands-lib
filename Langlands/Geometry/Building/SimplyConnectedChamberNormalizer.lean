import Langlands.Geometry.Building.ChamberIwahoriProof
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.Geometry.Building.AffineChamberTransitivity

/-! # Chamber stabilizers in the simply connected case -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building.ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

/-- Simple transitivity forces a chamber-preserving normalizer action in the
affine Weyl group to be the identity. -/
theorem normalizerAffineEquiv_eq_one_of_mem_affineWeylGroup_of_stabilizes_chamber
    (hP : P.SatisfiesApartmentAxioms)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : normalizerPoints P.i)
    (hnW : P.apartment.normalizerAffineEquiv n ∈
      AffineRootSystem.affineWeylGroup P.affineRoots)
    (hnC : n • C = C) :
    P.apartment.normalizerAffineEquiv n = 1 := by
  obtain ⟨w, hw, huniq⟩ := affineChamberSimpleTransitivity
    (TranslationSpace P.i) P.Apartment P.affineRoots
    hP.isAffineRootSystem_affineRoots C C hC hC
  let v : AffineRootSystem.affineWeylGroup P.affineRoots :=
    ⟨P.apartment.normalizerAffineEquiv n, hnW⟩
  have hv : (v : P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = C := by
    exact hnC
  have h1 : ((1 : AffineRootSystem.affineWeylGroup P.affineRoots) :
      P.Apartment ≃ᵃ[ℝ] P.Apartment) '' C = C := by
    simp
  have hv1 : v = 1 := (huniq v hv).trans (huniq 1 h1).symm
  exact congrArg (fun a : AffineRootSystem.affineWeylGroup P.affineRoots =>
    (a : P.Apartment ≃ᵃ[ℝ] P.Apartment)) hv1

/-- AS 5 supplies the affine Weyl inclusion for the ambient simply connected
group, so its chamber-preserving normalizer points act trivially. -/
theorem normalizerAffineEquiv_eq_one_of_stabilizes_chamber_of_isSimplyConnected
    (hP : P.SatisfiesApartmentAxioms) (hG : IsSimplyConnected G)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : normalizerPoints P.i) (hnC : n • C = C) :
    P.apartment.normalizerAffineEquiv n = 1 := by
  apply P.normalizerAffineEquiv_eq_one_of_mem_affineWeylGroup_of_stabilizes_chamber
    hP hC n ?_ hnC
  rw [← hP.range_eq_affineWeylGroup_of_isSimplyConnected hG]
  exact ⟨n, rfl⟩

/-- In the simply connected case, a chamber-preserving element of
`N(F) ∩ G(F)^0` lies in the actual centralizer-zero subgroup. -/
theorem mem_normalizerZero_of_stabilizes_chamber_of_isSimplyConnected
    (hP : P.SatisfiesApartmentAxioms) (hG : IsSimplyConnected G)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (n : normalizerPoints P.i) (hn : n ∈ P.normalizerZeroComponent)
    (hnC : n • C = C) : n ∈ P.normalizerZero := by
  apply (P.normalizerAffineEquiv_eq_one_iff_of_mem_normalizerZeroComponent
    (P.zeroDatum.coverImageCentralizerNormKernel_of_intersection
      (ZeroSubgroupDatum.minimalLeviZeroComparison P.zeroDatum).2) n hn).mp
  exact P.normalizerAffineEquiv_eq_one_of_stabilizes_chamber_of_isSimplyConnected
    hP hG hC n hnC

end Langlands.Geometry.Building.ParahoricBuildingData

namespace Langlands.Geometry.Building

/-- The chamber-normalizer bottleneck for simply connected ambient groups,
under the apartment axioms alone. -/
def SimplyConnectedChamberNormalizerStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G),
    P.SatisfiesApartmentAxioms → IsSimplyConnected G →
      ∀ C : Set P.Apartment, AffineRootSystem.IsChamber P.affineRoots C →
        ∀ n : normalizerPoints P.i, n ∈ P.normalizerZeroComponent →
          n • C = C → n ∈ P.normalizerZero

/-- The simply connected chamber-normalizer statement follows from AS 5,
affine chamber simple transitivity, and the published action-kernel comparison. -/
theorem simplyConnectedChamberNormalizer :
    SimplyConnectedChamberNormalizerStatement.{u} := by
  intro F _ _ _ _ G _ P hP hG C hC n hn hnC
  exact P.mem_normalizerZero_of_stabilizes_chamber_of_isSimplyConnected
    hP hG hC n hn hnC

end Langlands.Geometry.Building

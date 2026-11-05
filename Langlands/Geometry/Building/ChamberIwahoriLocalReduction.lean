import Langlands.Geometry.Building.ChamberIwahoriPrerequisiteReduction
import Langlands.Geometry.Building.PointParahoricCentralizer
import Langlands.Geometry.Building.ChamberParahoricIntersection

/-! # Chamber decompositions and intersections from local algebraic inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The sharp chamber decomposition only needs rank-one factorization for the
actual embedding in the supplied datum. -/
theorem chamberSharpDecomposition_of_rankOneFactorization
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    (hrank : RelativeRoot.HasRankOneFactorization B.i) :
    B.ChamberSharpDecompositionStatement := by
  intro hD C x ν hC hx hν
  have hG := B.isConnectedReductive
  have hi := B.isMaximalSplitTorus
  have hT : IsSplitTorus B.S.toGrp := hi.isSplitSubtorus.1
  have : LocallyOfFiniteType G.X.hom := by
    have := hG.smooth
    infer_instance
  have hfinite := hT.finite_relativeRoots B.i
  have hspan := relativeRootsRestrictedCharactersSpan F G hG B.S B.i hi
  have hsharp := B.apartment.chamberSharpConclusion_of_core hprod hG hi
    hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
    hD.mem_or_two_smul_mem hC hx
    (fun mu hmu => KPApartmentData.sharpFixer_subset_mul_of_mem_chamber hT hfinite hspan hrank
      hD.isAffineRootSystem_extendedAffineRoots hD.derivativeRoots_extendedAffineRoots
      hD.mem_or_two_smul_mem hC hx mu hmu) ν hν
  refine ⟨hsharp, fun Fa hFC hPos => ?_⟩
  exact B.apartment.chamberSharpFacetConclusion_of_chamberSharpConclusion
    hD.mem_or_two_smul_mem hD.isAffineRootSystem_affineRoots hC hFC hPos hx hsharp

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Actual rank-one factorization, the actual cover comparison and the Dynamic
ordered-product statement imply the existing full chamber decomposition. -/
theorem chamberIwahoriDecomposition_of_rankOneFactorization
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u}) :
    P.ChamberIwahoriDecompositionStatement :=
  chamberIwahoriDecomposition_of_sharp
    (P.toValuationBuildingData.chamberSharpDecomposition_of_rankOneFactorization hprod hrank)
    (P.centralizerParahoricIntersection_of_rankOneFactorization hrank hZ)

/-- The actual restricted-normalizer chamber intersection follows from the
three algebraic inputs, with no separate chamber-decomposition premise. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage hP hrank hprod
    (P.chamberIwahoriDecomposition_of_rankOneFactorization hrank hZ hprod) hC

/-- The membership form uses the original normalizer and zero-subgroup premise
of the existing conjugate-intersection input. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent hP hrank hprod
    (P.chamberIwahoriDecomposition_of_rankOneFactorization hrank hZ hprod) hC hg

/-- The identity on ambient rational points identifies the chamber intersection
with the centralizer-zero image under the three retained algebraic inputs. -/
def chamberConjugateParahoricEquivCentralizerZeroImage_of_rankOneFactorization
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) ≃*
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  P.chamberConjugateParahoricEquivCentralizerZeroImage hP hrank hprod
    (P.chamberIwahoriDecomposition_of_rankOneFactorization hrank hZ hprod) hC

/-- The equivalence preserves the ambient rational point. -/
@[simp] theorem chamberConjugateParahoricEquivCentralizerZeroImage_of_rankOneFactorization_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    (hprod : RelativeRoot.DynamicRootOrderedProductStatement.{u})
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (g : ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C))) :
    ((P.chamberConjugateParahoricEquivCentralizerZeroImage_of_rankOneFactorization
      hP hrank hZ hprod hC g :
        P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building

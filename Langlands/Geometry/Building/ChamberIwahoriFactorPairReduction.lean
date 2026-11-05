import Langlands.Geometry.Building.ChamberIwahoriPointReduction
import Langlands.Geometry.Building.LocalRootProductInjectivity
import Langlands.GroupScheme.Rational.RootFactorizationFromExistence

/-! # Chamber decomposition and saturation from opposite factor pairs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme

namespace Langlands.GroupScheme.RelativeRoot

/-- All-test injectivity from local opposite pairs specializes to the actual
rational-point injectivity used by the chamber decomposition and saturation. -/
theorem orderedRootPointInjectivity_of_hasOppositeFactorPairs
    {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (i : S.toGrp ⟶ G) [Mono i.hom.hom.left]
    (hS : IsSplitTorus S.toGrp) (hE : HasOppositeFactorPairs i) :
    OrderedRootPointInjectivity i := by
  intro ν n a ha hrange
  exact orderedRootSubgroupPoints_injective_of_hasOppositeFactorPairs
    i hS hE ν a ha hrange (Over.mk (𝟙 _))

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- Local opposite-pair existence supplies both inputs of the full sharp
chamber and facet decomposition. -/
theorem chamberSharpDecomposition_of_hasOppositeFactorPairs
    (hE : RelativeRoot.HasOppositeFactorPairs B.i) :
    B.ChamberSharpDecompositionStatement := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  have hS : IsSplitTorus B.S.toGrp := B.isMaximalSplitTorus.isSplitSubtorus.1
  exact B.chamberSharpDecomposition_of_localRootInjectivity
    (RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs B.i hS hE)
    (RelativeRoot.orderedRootPointInjectivity_of_hasOppositeFactorPairs B.i hS hE)

end ValuationBuildingData

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G)

/-- Opposite pairs and the actual cover comparison give the full chamber and
facet decomposition without separate rank-one or injectivity premises. -/
theorem chamberIwahoriDecomposition_of_hasOppositeFactorPairs
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement) :
    P.ChamberIwahoriDecompositionStatement := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hS : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  exact P.chamberIwahoriDecomposition_of_localRootInjectivity
    (RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs P.i hS hE)
    hZ
    (RelativeRoot.orderedRootPointInjectivity_of_hasOppositeFactorPairs P.i hS hE)

/-- The actual restricted-normalizer intersection equals the centralizer-zero
image under apartment axioms, local opposite pairs and the cover comparison. -/
theorem iInf_parahoric_normalizerZeroComponent_eq_of_hasOppositeFactorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    (⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) =
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  have : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hS : IsSplitTorus P.S.toGrp := P.isMaximalSplitTorus.isSplitSubtorus.1
  exact P.iInf_parahoric_normalizerZeroComponent_eq_of_localRootInjectivity
    hP
    (RelativeRoot.hasRankOneFactorization_of_hasOppositeFactorPairs P.i hS hE)
    hZ
    (RelativeRoot.orderedRootPointInjectivity_of_hasOppositeFactorPairs P.i hS hE)
    hC

/-- This two-input local reduction retains the exact normalizer and
zero-component membership quantifiers of the chamber-conjugate target. -/
theorem mem_centralizerZero_of_forall_mem_parahoric_of_hasOppositeFactorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    {g : rationalPoints G}
    (hg : ∀ n : normalizerPoints P.i, (n : rationalPoints G) ∈ P.zeroSubgroup →
      g ∈ P.parahoric (n • C)) :
    g ∈ P.centralizerZero.map (rationalPoints.map P.centralizer.j) := by
  rw [← P.iInf_parahoric_normalizerZeroComponent_eq_of_hasOppositeFactorPairs hP hE hZ hC]
  exact Subgroup.mem_iInf.mpr fun n => hg n n.property

/-- Subgroup congruence identifies the actual intersection with the actual
centralizer-zero image through the identity on ambient rational points. -/
def chamberConjugateParahoricEquivCentralizerZeroImage_of_hasOppositeFactorPairs
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C) :
    ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C)) ≃*
        P.centralizerZero.map (rationalPoints.map P.centralizer.j) :=
  MulEquiv.subgroupCongr
    (P.iInf_parahoric_normalizerZeroComponent_eq_of_hasOppositeFactorPairs hP hE hZ hC)

/-- The equivalence preserves the ambient rational point. -/
@[simp]
theorem chamberConjugateParahoricEquivCentralizerZeroImage_of_hasOppositeFactorPairs_apply_coe
    (hP : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hE : RelativeRoot.HasOppositeFactorPairs P.i)
    (hZ : P.zeroDatum.CoverImageCentralizerNormKernelStatement)
    {C : Set P.Apartment} (hC : AffineRootSystem.IsChamber P.affineRoots C)
    (g : ↥(⨅ n : P.normalizerZeroComponent,
      P.parahoric ((n : normalizerPoints P.i) • C))) :
    ((P.chamberConjugateParahoricEquivCentralizerZeroImage_of_hasOppositeFactorPairs
      hP hE hZ hC g :
        P.centralizerZero.map (rationalPoints.map P.centralizer.j)) : rationalPoints G) = g :=
  rfl

end ParahoricBuildingData

end Langlands.Geometry.Building

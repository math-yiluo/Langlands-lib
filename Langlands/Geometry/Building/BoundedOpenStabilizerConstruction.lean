import Langlands.Geometry.Building.CentralizerNormKernelConstruction
import Langlands.Geometry.Building.BoundedOpenStabilizerAssembly
import Langlands.Geometry.Building.PointSharpExchange
import Langlands.Geometry.Building.KPCentralizerZeroCompactOpenReduction
import Langlands.Geometry.Building.KPZeroOpenness
import Langlands.GroupScheme.Torus.GaloisNormSmoothnessProof

/-! # Bounded open stabilizers from rank-one exchange and open generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Plancherel
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Geometry.Building

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]

namespace ValuationBuildingData

variable (B : ValuationBuildingData G)

/-- Opposite factor pairs and the apartment axioms suffice for the existing
singleton sharp-fixer boundedness statement; centralizer boundedness is proved. -/
theorem sharpFixerBoundedness_of_rankOneFactorization
    (hrank : RelativeRoot.HasRankOneFactorization B.i) :
    B.SharpFixerBoundednessStatement := by
  apply B.sharpFixerBoundedness_of_cover B.isAlgebraicallyBounded_image_centralizerNormKernel
  intro hB x ν hν
  exact B.sharpFixer_subset_mul_sharpNormalizerStabilizer hB hrank x ν hν

end ValuationBuildingData

namespace ParahoricBuildingData

variable (P : ParahoricBuildingData G)

private instance stabilizerAmbientAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

private instance stabilizerCentralizerAffine : IsAffine P.centralizer.Z.X.left := by
  have : IsClosedImmersion P.centralizer.j.hom.hom.left := P.centralizer.isClosedSubgroup
  exact isAffine_of_isAffineHom P.centralizer.j.hom.hom.left

private instance stabilizerAmbientTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

private instance stabilizerCentralizerTopology :
    TopologicalSpace (rationalPoints P.centralizer.Z) :=
  rationalPointTopology F P.centralizer.Z.X

/-- Openness is the only additional input needed for compact openness of the
actual centralizer-zero subgroup. -/
theorem centralizerZeroCompactOpen_of_isOpen
    (hopen : IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z))) :
    P.CentralizerZeroCompactOpenStatement := by
  have hZ := P.toValuationBuildingData.isConnectedReductive_centralizer
  let : Smooth P.centralizer.Z.X.hom := hZ.smooth
  let : IsTopologicalGroup (rationalPoints P.centralizer.Z) :=
    rationalPoint_isTopologicalGroup F P.centralizer.Z
  exact ⟨P.toValuationBuildingData.isCompact_centralizerNormKernel_of_valuationData.of_isClosed_subset
      (P.centralizerZero.isClosed_of_isOpen hopen)
      P.zeroDatum.centralizerZero_le_rationalCommonNormKernel, hopen⟩

/-- The proved Galois norm smoothness removes that premise from centralizer-zero
openness; only derived-cover/torus product smoothness remains. -/
theorem centralizerZeroCompactOpen_of_productSmoothness
    (hprod : DerivedCoverTorusProductSmoothStatement.{u}) :
    P.CentralizerZeroCompactOpenStatement :=
  P.centralizerZeroCompactOpen_of_isOpen
    (P.isOpen_centralizerZero hprod GaloisNormSmoothnessProof.galoisNormSmoothness)

/-- The unchanged KP Axiom 4.1.2 follows from the apartment axioms, opposite
factor pairs, open root-centralizer generation and actual zero-subgroup openness. -/
theorem hasBoundedOpenStabilizers_of_rankOne_and_isOpen
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hgen : RelativeRoot.OpenRootCentralizerGenerationStatement.{u})
    (hZo : IsOpen (P.centralizerZero : Set (rationalPoints P.centralizer.Z))) :
    P.HasBoundedOpenStabilizers :=
  P.hasBoundedOpenStabilizers_of_prerequisites hD
    (P.toValuationBuildingData.sharpFixerBoundedness_of_rankOneFactorization hrank)
    P.toValuationBuildingData.isAlgebraicallyBounded_image_centralizerNormKernel hgen hZo

/-- The bounded-open predicate with only the remaining apartment, rank-one,
open-generation and product-smoothness premises. -/
theorem hasBoundedOpenStabilizers_of_rankOne_and_productSmoothness
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hgen : RelativeRoot.OpenRootCentralizerGenerationStatement.{u})
    (hprod : DerivedCoverTorusProductSmoothStatement.{u}) :
    P.HasBoundedOpenStabilizers :=
  P.hasBoundedOpenStabilizers_of_rankOne_and_isOpen hD hrank hgen
    (P.isOpen_centralizerZero hprod GaloisNormSmoothnessProof.galoisNormSmoothness)

/-- Every original norm-one point stabilizer, bundled as the same bounded open
subgroup under the remaining explicit prerequisites. -/
def boundedOpenStabilizerDataOfRankOne
    (hD : P.apartment.SatisfiesApartmentAxioms P.centralizer)
    (hrank : RelativeRoot.HasRankOneFactorization P.i)
    (hgen : RelativeRoot.OpenRootCentralizerGenerationStatement.{u})
    (hprod : DerivedCoverTorusProductSmoothStatement.{u})
    (y : P.ReducedBuilding) :
    {K : OpenSubgroup (rationalPoints G) // K.toSubgroup = P.compactStabilizer y ∧
      IsAlgebraicallyBounded F G.X (K : Set (rationalPoints G))} := by
  have h := P.hasBoundedOpenStabilizers_of_rankOne_and_productSmoothness
    hD hrank hgen hprod y
  exact ⟨⟨P.compactStabilizer y, h.1⟩, rfl, h.2⟩

end ParahoricBuildingData

end Langlands.Geometry.Building

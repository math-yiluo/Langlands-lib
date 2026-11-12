import Langlands.Geometry.Building.SimplyConnectedNormalizerAffineWeylAssembly
import Langlands.Geometry.Building.SimplyConnectedFacetFixingStatement
import Langlands.Geometry.Building.ReflectionTranslationLattice
import Langlands.Geometry.Building.SimplyConnectedReflectionTranslationReduction
import Langlands.GroupScheme.Rational.RelativeRootSystemProof
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerRankOneReduction
import Langlands.GroupScheme.SimplyConnected.RankOneCentralizerGenerationReduction

/-!
# Simply connected facet fixing from the translation-image equality

The facet-fixing target `SimplyConnectedFacetFixingStatement` follows from the
translation-image equality `SimplyConnectedReflectionTranslationStatement` alone.
The two other inputs of the published lattice criterion, actual opposite pairs and
the actual relative root system, are supplied by their published proofs.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The actual relative roots of the supplied maximal split torus form a relative
root system, by the published relative-root-system theorem. -/
theorem hasRelativeRootSystem : HasRelativeRootSystem B.i :=
  relativeRootSystem F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus

/-- Actual reflection products realize every finite relative-Weyl class. -/
theorem reflectionRelativeWeylMap_surjective' :
    Function.Surjective B.reflectionRelativeWeylMap :=
  B.reflectionRelativeWeylMap_surjective B.hasOppositeFactorPairs B.hasRelativeRootSystem

/-- Equality of the actual translation images is the only remaining input of the
facet-fixing criterion: a normalizer point preserving a facet of the apartment as
a set then fixes it pointwise. -/
theorem normalizer_facet_fixing_of_translationLattice_eq'
    (hL : B.reflectionTranslationLattice = B.centralizerTranslationLattice)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i)
    (hfix : (fun x : B.Apartment => n • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n • x = x :=
  B.normalizer_facet_fixing_of_translationLattice_eq B.hasOppositeFactorPairs
    B.reflectionRelativeWeylMap_surjective' hL hFa n hfix

end ValuationBuildingData

/-- The translation-image equality for simply connected groups implies pointwise
fixing of facets by their setwise stabilizers in the actual normalizer. -/
def SimplyConnectedFacetFixingReductionStatement : Prop :=
  SimplyConnectedReflectionTranslationStatement.{u} →
    SimplyConnectedFacetFixingStatement.{u}

/-- The reduction holds: the published lattice criterion, with opposite pairs and
the relative root system supplied by their published proofs. -/
theorem simplyConnectedFacetFixingReduction :
    SimplyConnectedFacetFixingReductionStatement.{u} := by
  intro hL F _ _ _ _ G _ B hsc Fa hFa n hfix
  exact B.normalizer_facet_fixing_of_translationLattice_eq' (hL F G B hsc) hFa n hfix

/-- Rank-one generation of split-torus centralizers in simply connected groups
implies the facet-fixing target. -/
theorem simplyConnectedFacetFixing_of_rankOneCentralizerGeneration
    (hgen : SimplyConnectedRankOneCentralizerGenerationStatement.{u}) :
    SimplyConnectedFacetFixingStatement.{u} :=
  simplyConnectedFacetFixingReduction
    (simplyConnectedReflectionTranslation_of_rankOneGeneration rootRankOneFactorization hgen)

/-- The Kneser–Tits centralizer statement for simply connected groups implies the
facet-fixing target. -/
theorem simplyConnectedFacetFixing_of_kneserTitsCentralizer
    (hKT : SimplyConnectedKneserTitsCentralizerStatement.{u}) :
    SimplyConnectedFacetFixingStatement.{u} :=
  simplyConnectedFacetFixing_of_rankOneCentralizerGeneration
    (simplyConnectedRankOneCentralizerGeneration_of_kneserTits
      (rootGeneratedCentralizerRankOneReduction rootRankOneFactorization) hKT)

end Langlands.Geometry.Building

import Langlands.Geometry.Building.PointSharpExchange
import Langlands.Geometry.Building.SharpFixerBoundednessAssembly
import Langlands.Geometry.Building.KPCentralizerNormKernelCompactness

/-!
# Singleton sharp-fixer boundedness from the remaining structural statements

KP Corollary 7.3.14 for one point, `B.SharpFixerBoundednessStatement`, for every actual
`B : ValuationBuildingData G`, assuming four Library statements that are not yet proved:
opposite factor pairs (`RootRankOneFactorizationStatement`, KP Proposition 2.11.17), the
structure of the centralizer of a maximal split torus (`ActualCentralizerStructureStatement`),
reductivity of central quotients (`CentralQuotientReductiveStatement`) and the criterion that
rational points are compact exactly for anisotropic groups (`AnisotropicCompactnessStatement`).
The last three give compactness of `Z(F)^1`; the first gives the cover of `PointSharpExchange`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (B : ValuationBuildingData G)

/-- The factorization `s : S → Z` supplied with the centralizer is central and a maximal
split torus of `Z`. -/
theorem centralizer_isCentral_maximalSplit :
    IsCentral B.centralizer.s ∧ IsMaximalSplitTorus B.centralizer.s := by
  constructor
  · apply isCentral_of_range_le_torusCentralizer B.centralizer.isRepresentedBy.1
    rw [B.centralizer.comp_eq]
    exact B.centralizer.isRepresentedBy.2.le
  · apply IsMaximalSplitTorus.of_comp B.centralizer.isClosedSubgroup
    rw [B.centralizer.comp_eq]
    exact B.isMaximalSplitTorus

/-- `Z(F)^1` is compact, assuming the three structural statements. -/
theorem isCompact_centralizerNormKernel
    (hstructure : BruhatTits.Cartan.ActualCentralizerStructureStatement.{u})
    (hquot : CentralQuotientReductiveStatement.{u})
    (hcompact : AnisotropicCompactnessStatement.{u}) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : IsAffine B.centralizer.Z.X.left := by
      have : IsClosedImmersion B.centralizer.j.hom.hom.left :=
        B.centralizer.isClosedSubgroup
      exact isAffine_of_isAffineHom B.centralizer.j.hom.hom.left
    letI : TopologicalSpace (rationalPoints B.centralizer.Z) :=
      rationalPointTopology F B.centralizer.Z.X
    IsCompact (rationalCommonNormKernel B.centralizer.Z :
      Set (rationalPoints B.centralizer.Z)) := by
  have hZ := (hstructure F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus
    B.centralizer.Z B.centralizer.j B.centralizer.isClosedSubgroup
    B.centralizer.isRepresentedBy B.centralizer.s B.centralizer.comp_eq).1
  obtain ⟨hc, hm⟩ := B.centralizer_isCentral_maximalSplit
  exact BruhatTits.RationalPoints.isCompact_rationalCommonNormKernel_of_central_maximalSplit
    hquot hcompact B.centralizer.Z hZ hm hc

/-- KP Corollary 7.3.14 for one point, assuming the four structural statements. -/
theorem sharpFixerBoundedness_of_structure
    (hrank : RootRankOneFactorizationStatement.{u})
    (hstructure : BruhatTits.Cartan.ActualCentralizerStructureStatement.{u})
    (hquot : CentralQuotientReductiveStatement.{u})
    (hcompact : AnisotropicCompactnessStatement.{u}) :
    B.SharpFixerBoundednessStatement :=
  B.sharpFixerBoundedness_of_cover
    (B.isAlgebraicallyBounded_image_centralizerNormKernel_of_isCompact
      (B.isCompact_centralizerNormKernel hstructure hquot hcompact))
    (fun hB x ν hν => B.sharpFixer_subset_mul_sharpNormalizerStabilizer hB
      (hrank F G B.isConnectedReductive B.S B.i B.isMaximalSplitTorus) x ν hν)

end Langlands.Geometry.Building.ValuationBuildingData

namespace Langlands.Geometry.Building

/-- The four structural statements `RootRankOneFactorizationStatement`,
`ActualCentralizerStructureStatement`, `CentralQuotientReductiveStatement` and
`AnisotropicCompactnessStatement` at universe `u` imply
`B.SharpFixerBoundednessStatement` for every actual `B : ValuationBuildingData G` over a
nonarchimedean local field `F : Type u`. -/
def SharpFixerBoundednessStructuralReductionStatement : Prop :=
  RootRankOneFactorizationStatement.{u} →
    BruhatTits.Cartan.ActualCentralizerStructureStatement.{u} →
      CentralQuotientReductiveStatement.{u} → AnisotropicCompactnessStatement.{u} →
        ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
          [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))
          [IsAffineHom G.X.hom] (B : ValuationBuildingData G),
          B.SharpFixerBoundednessStatement

theorem sharpFixerBoundednessStructuralReduction :
    SharpFixerBoundednessStructuralReductionStatement.{u} := by
  intro hrank hstructure hquot hcompact F _ _ _ _ G _ B
  exact B.sharpFixerBoundedness_of_structure hrank hstructure hquot hcompact

end Langlands.Geometry.Building

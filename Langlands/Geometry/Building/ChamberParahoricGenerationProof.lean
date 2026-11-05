import Langlands.Geometry.Building.ChamberGenerationOpenCell
import Langlands.Geometry.Building.ChamberRootGeneration
import Langlands.Geometry.Building.ApartmentRootRays
import Langlands.GroupScheme.Rational.DynamicRadicalRootGeneration

/-! # Generation by the actual chamber parahoric and zero normalizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

/-- The exact chamber-generation input of the actual affine Iwahori–Tits
system, at arbitrary universe and with the published apartment hypotheses. -/
theorem chamberParahoricGeneration : ChamberParahoricGenerationStatement.{u} := by
  intro F _ _ _ _ G _ P hA C hC
  apply P.zeroSubgroup_le_chamber_sup_of_dynamicRadicals hA C
  intro ν
  apply RelativeRoot.dynamicUnipotent_le_of_disjoint_positive_rays
    P.isConnectedReductive P.isMaximalSplitTorus ν
  · intro a ha b hb hne
    exact P.apartment.disjoint_cyclicTail_indivisibleRoots P.centralizer hA
      P.isMaximalSplitTorus.isSplitSubtorus.1 ha.1 hb.1 hne
  · intro a
    exact P.rootGroup_le_parahoric_sup_zeroNormalizer hA hC a

end Langlands.Geometry.Building

import Langlands.Representation.CuspidalSupport.BernsteinStandardStages
import Langlands.Representation.CuspidalSupport.StandardLeviInductionFixedVectorsStatement

/-! # Fixed vectors of normalized induction inside a standard Levi -/

noncomputable section

set_option maxHeartbeats 800000

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Aubert.General Langlands.Aubert.General.RationalPointFamily
open Langlands.GroupScheme Langlands.BruhatTits.SpecialCompact
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

local instance standardLeviInductionFixedAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardLeviInductionFixedTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance standardLeviInductionFixedFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F
local instance standardLeviInductionFixedT2 : T2Space (rationalPoints G) :=
  rationalPoint_t2Space F G

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
  (family : BernsteinStandardFamily i ν)

/-- Induction in stages and two ambient normal-level criteria give fixed-vector
detection inside each standard Levi. -/
theorem nontrivial_standardLeviInduction_fixedVectors_iff :
    StandardLeviInductionFixedVectorsStatement.{uF, uV} i ν family := by
  intro J I K hK K₀ hnormal hIwasawa hIwahori A
  let B := (leviNormalizedInductionFunctor (family.closedLevi J)
    (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
      family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
    (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))).obj A
  have houter := Jacquet.nontrivial_standardInduction_fixedVectors_iff
    i ν family J K hK K₀ hnormal hIwasawa (hIwahori J) B
  have hdirect := Jacquet.nontrivial_standardInduction_fixedVectors_iff
    i ν family (leviIndex J I) K hK K₀ hnormal hIwasawa (hIwahori _) A
  have hstages := (fixedVectorsEquiv
    (SmoothRep.equivOfIso ((bernsteinStandardInductionStagesIso i ν family J I).app A))
    K.toSubgroup).toEquiv.nontrivial_congr
  exact houter.symm.trans (hstages.trans hdirect)

end Langlands.CuspidalSupport

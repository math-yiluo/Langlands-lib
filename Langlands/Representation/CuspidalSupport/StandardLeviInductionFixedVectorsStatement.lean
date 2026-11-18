import Langlands.Representation.CuspidalSupport.BernsteinInductionRestrictionStatement
import Langlands.Representation.Jacquet.StandardNormalLevelFixedVectors

/-! # Statement of fixed-vector detection for induction inside a standard Levi -/

noncomputable section

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

local instance standardLeviInductionCriterionAffine : IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom
local instance standardLeviInductionCriterionTopology : TopologicalSpace (rationalPoints G) :=
  pointTopology
local instance standardLeviInductionCriterionFieldT2 : T2Space F :=
  BruhatTits.localField_t2Space F
local instance standardLeviInductionCriterionT2 : T2Space (rationalPoints G) :=
  rationalPoint_t2Space F G

/-- Nonzero fixed vectors of normalized induction inside a standard Levi are
detected in the coefficient at the literal intersection with the prescribed normal level. -/
def StandardLeviInductionFixedVectorsStatement
    {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of F))}
    (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
    (family : BernsteinStandardFamily i ν) : Prop :=
  ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J)
    (K : OpenSubgroup (rationalPoints G)) (_hK : IsCompact (K : Set (rationalPoints G)))
    (K₀ : Subgroup (rationalPoints G))
    (_hnormal : K₀ ≤ Subgroup.normalizer (K : Set (rationalPoints G)))
    (_hIwasawa : ∀ x : rationalPoints G, ∃ m ∈ standardLeviPoints i ν ∅,
      ∃ n ∈ standardUnipotentPoints i ν ∅, ∃ k ∈ K₀, x = m * n * k)
    (_hIwahori : ∀ L : Finset (SimpleRoot i ν),
      HasIwahoriIntersectionDecomposition K.toSubgroup (levi i ν L)
        (unipotent i ν L) (standardOppositeUnipotentPoints i ν (rootSet i ν L)))
    (A : SmoothRep.{0, uF, max uF uV} ℂ (levi i ν (leviIndex J I))),
    Nontrivial (fixedVectors
      ((leviNormalizedInductionFunctor (family.closedLevi J)
        (levi_le_of_subset i ν standardLeviIntersection family.connectedReductive
          family.maximalSplitTorus family.genericCocharacter _ J (leviIndex_subset J I))
        (family.leviDecomposition J I) (family.closedUnipotent (leviIndex J I))).obj A).representation
      (K.toSubgroup.comap (levi i ν J).subtype)) ↔
    Nontrivial (fixedVectors A.representation
      (K.toSubgroup.comap (levi i ν (leviIndex J I)).subtype))

end Langlands.CuspidalSupport

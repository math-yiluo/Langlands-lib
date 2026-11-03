import Langlands.GroupScheme.Rational.AssociatedRootImage
import Langlands.GroupScheme.Rational.StandardCocharacterStatement
import Langlands.GroupScheme.Rational.StandardRestrictedConjugation
import Langlands.Representation.Aubert.General.GroupTransport

/-! # Associated rational restricted parabolic and unipotent transport -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (ν : cocharacterLattice T)
  [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)

include hLength hSimple hMin hAssoc in
/-- The actual character action of every specified point lift maps the
associated coarse root set onto the target coarse root set. -/
theorem weylAction_image_associatedSubset
    (J : Finset (SimpleRoot i ν))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    weylAction i ((normalizerEquiv i hN).symm n) ''
        rootSet i ν (associatedSubset cs J) = rootSet i ν J := by
  rw [← weylCharacterAction_point_mk i hN hZ, hn,
    rootSet_associatedSubset i ν hN hZ cs hLength hSimple hMin hAssoc,
    Set.image_image]
  have hcancel :
      (fun α => weylCharacterAction i hN hZ (longestRep cs J)
        (weylCharacterAction i hN hZ (longestRep cs J)⁻¹ α)) = id := by
    funext α
    change (weylCharacterAction i hN hZ (longestRep cs J) *
      weylCharacterAction i hN hZ (longestRep cs J)⁻¹) α = α
    rw [← map_mul, mul_inv_cancel, map_one]
    rfl
  rw [hcancel, Set.image_id]

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

include hLength hSimple hMin hAssoc hG hi hν hStandard in
/-- Under the existing rational target's hypotheses, the same actual
normalizer lift transports both restricted standard families. -/
theorem associatedRestrictedParabolic_unipotent_mem
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) (x : levi i ν J) :
    ((x : RationalPoint k G.X) ∈
        parabolic i ν (leviIndex J (associatedFinsetEquiv cs J K)) ↔
      (n : RationalPoint k G.X)⁻¹ * (x : RationalPoint k G.X) *
        (n : RationalPoint k G.X) ∈
          parabolic i ν (leviIndex (associatedSubset cs J) K)) ∧
    ((x : RationalPoint k G.X) ∈
        unipotent i ν (leviIndex J (associatedFinsetEquiv cs J K)) ↔
      (n : RationalPoint k G.X)⁻¹ * (x : RationalPoint k G.X) *
        (n : RationalPoint k G.X) ∈
          unipotent i ν (leviIndex (associatedSubset cs J) K)) := by
  have hfinite : (simpleRelativeRoots i ν).Finite := by
    rw [← rootSet_univ i ν]
    exact rootSet_finite i ν Finset.univ
  have hI0 := (rootSet_subset_iff i ν _ _).mpr
    (leviIndex_subset (associatedSubset cs J) K)
  have hI1 := (rootSet_subset_iff i ν _ _).mpr
    (leviIndex_subset J (associatedFinsetEquiv cs J K))
  have hJ0 := (hStandard k G hG T i hi ν hν
    (rootSet i ν (associatedSubset cs J)) (rootSet_subset i ν _)).1
  have hJ1 := (hStandard k G hG T i hi ν hν
    (rootSet i ν J) (rootSet_subset i ν J)).1
  have hI := weylAction_image_associatedFinsetEquiv
    i ν hN hZ cs hLength hSimple J n hn K
  have hJ := weylAction_image_associatedSubset
    i ν hN hZ cs hLength hSimple hMin hAssoc J n hn
  have h := mem_standardParabolic_unipotent_inv_conj_iff_of_character_images
    i ν hfinite hI0 hI1 hJ0 hJ1 ((normalizerEquiv i hN).symm n)
    hI hJ (Over.mk (𝟙 _)) (x : RationalPoint k G.X) x.property
  have hnpoint : ((normalizerEquiv i hN).symm n : RationalPoint k G.X) = n := rfl
  simpa only [constantPoint_self, hnpoint] using h

section Topology

variable [TopologicalSpace (RationalPoint k G.X)]
  [IsTopologicalGroup (RationalPoint k G.X)]
  (hConj : StandardLeviConjugationStatement.{u})

/-- Restrict the actual associated-Levi equivalence to the literal
parabolic subgroupOf on each side. -/
def associatedRestrictedParabolicEquiv
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (parabolic i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf
        (levi i ν J) ≃ₜ*
      (parabolic i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
        (levi i ν (associatedSubset cs J)) :=
  GroupTransport.subgroupEquiv
    (associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs hLength hSimple
      hMin hAssoc J n hn)
    (fun x => (associatedRestrictedParabolic_unipotent_mem i ν hN hZ cs hLength hSimple
      hMin hAssoc hG hi hν hStandard J K n hn x).1)

/-- Restrict the actual associated-Levi equivalence to the literal
unipotent subgroupOf on each side. -/
def associatedRestrictedUnipotentEquiv
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (unipotent i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf
        (levi i ν J) ≃ₜ*
      (unipotent i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
        (levi i ν (associatedSubset cs J)) :=
  GroupTransport.subgroupEquiv
    (associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs hLength hSimple
      hMin hAssoc J n hn)
    (fun x => (associatedRestrictedParabolic_unipotent_mem i ν hN hZ cs hLength hSimple
      hMin hAssoc hG hi hν hStandard J K n hn x).2)

@[simp]
theorem associatedRestrictedParabolicEquiv_apply
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (x : (parabolic i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf
      (levi i ν J)) :
    ((associatedRestrictedParabolicEquiv i ν hN hZ cs hLength hSimple hMin hAssoc
        hG hi hν hStandard hConj J K n hn x :
      levi i ν (associatedSubset cs J)) : RationalPoint k G.X) =
      (n : RationalPoint k G.X)⁻¹ * ((x : levi i ν J) : RationalPoint k G.X) *
        (n : RationalPoint k G.X) := rfl

@[simp]
theorem associatedRestrictedUnipotentEquiv_apply
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (x : (unipotent i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf
      (levi i ν J)) :
    ((associatedRestrictedUnipotentEquiv i ν hN hZ cs hLength hSimple hMin hAssoc
        hG hi hν hStandard hConj J K n hn x :
      levi i ν (associatedSubset cs J)) : RationalPoint k G.X) =
      (n : RationalPoint k G.X)⁻¹ * ((x : levi i ν J) : RationalPoint k G.X) *
        (n : RationalPoint k G.X) := rfl

@[simp]
theorem associatedRestrictedParabolicEquiv_symm_apply
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (x : (parabolic i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
      (levi i ν (associatedSubset cs J))) :
    (((associatedRestrictedParabolicEquiv i ν hN hZ cs hLength hSimple hMin hAssoc
        hG hi hν hStandard hConj J K n hn).symm x :
      levi i ν J) : RationalPoint k G.X) =
      (n : RationalPoint k G.X) * ((x : levi i ν (associatedSubset cs J)) :
        RationalPoint k G.X) * (n : RationalPoint k G.X)⁻¹ := rfl

@[simp]
theorem associatedRestrictedUnipotentEquiv_symm_apply
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (x : (unipotent i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
      (levi i ν (associatedSubset cs J))) :
    (((associatedRestrictedUnipotentEquiv i ν hN hZ cs hLength hSimple hMin hAssoc
        hG hi hν hStandard hConj J K n hn).symm x :
      levi i ν J) : RationalPoint k G.X) =
      (n : RationalPoint k G.X) * ((x : levi i ν (associatedSubset cs J)) :
        RationalPoint k G.X) * (n : RationalPoint k G.X)⁻¹ := rfl

end Topology

end Langlands.Aubert.General.RationalPointFamily

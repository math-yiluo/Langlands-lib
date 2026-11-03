import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Langlands.Representation.Aubert.General.RationalLeviDecomposition
import Langlands.Group.RelativeWeylAssociatedIndexing

/-! # Descendant-Levi transport under the specified associated-Levi conjugation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

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

include hLength hSimple in
/-- Every literal associated-Levi subset has exactly the transported character
set prescribed by the finite-subset equivalence. -/
theorem rootSet_associatedFinsetEquiv
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J)) :
    weylCharacterAction i hN hZ (longestRep cs J) ''
        rootSet i ν (leviIndex (associatedSubset cs J) K) =
      rootSet i ν (leviIndex J (associatedFinsetEquiv cs J K)) := by
  have hpos : ∀ a ∈ leviIndex (associatedSubset cs J) K,
      weylCharacterAction i hN hZ (longestRep cs J) a.val ∈ positiveRelativeRoots i ν := by
    intro a ha
    apply (hLength _ a).mp
    apply (mem_positiveSimpleSet cs _ a).mp
    rw [positiveSimpleSet_longestRep]
    exact leviIndex_subset (associatedSubset cs J) K ha
  have hmap : RootMapsIntoSimple i ν hN hZ (longestRep cs J)
      (leviIndex (associatedSubset cs J) K) J := by
    apply (rootMapsIntoSimple_iff_of_positive i ν hN hZ cs hSimple _ _ _ hpos).mpr
    intro a ha
    apply mapsIntoSimple_longestRep cs J a
    rw [positiveSimpleSet_longestRep]
    exact leviIndex_subset (associatedSubset cs J) K ha
  have hroot := rootSet_rootSimpleImage_of_mapsIntoSimple i ν hN hZ _ _ J hmap
  rw [rootSimpleImage_eq_simpleImage_of_positive i ν hN hZ cs hSimple _ _ hpos,
    simpleImage_associatedFinsetEquiv cs J K] at hroot
  exact hroot.symm

variable (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})

include hN hZ hLength hSimple hG hi hν hConj in
/-- The actual normalizer lift carries each descendant standard Levi to its
corresponding descendant in the target Levi. -/
theorem associatedDescendantLevi_map_conj
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (levi i ν (leviIndex (associatedSubset cs J) K)).map
        (MulAut.conj (n : RationalPoint k G.X) : _ →* _) =
      levi i ν (leviIndex J (associatedFinsetEquiv cs J K)) := by
  have hchar : weylAction i ((normalizerEquiv i hN).symm n) ''
      rootSet i ν (leviIndex (associatedSubset cs J) K) =
        rootSet i ν (leviIndex J (associatedFinsetEquiv cs J K)) := by
    rw [← weylCharacterAction_point_mk i hN hZ, hn]
    exact rootSet_associatedFinsetEquiv i ν hN hZ cs hLength hSimple J K
  exact levi_map_conj_of_character_image i ν hG hi hν hConj
    (leviIndex J (associatedFinsetEquiv cs J K)) (leviIndex (associatedSubset cs J) K)
    ((normalizerEquiv i hN).symm n) hchar

variable [TopologicalSpace (RationalPoint k G.X)]
  [IsTopologicalGroup (RationalPoint k G.X)]
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)

/-- Exact membership compatibility for descendant Levis under the target's
specified ambient associated-Levi equivalence. -/
theorem associatedLeviConjugationEquiv_descendant_mem
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) (x : levi i ν J) :
    x ∈ (levi i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf (levi i ν J) ↔
      associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs hLength hSimple
          hMin hAssoc J n hn x ∈
        (levi i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
          (levi i ν (associatedSubset cs J)) := by
  change (x : RationalPoint k G.X) ∈ levi i ν (leviIndex J (associatedFinsetEquiv cs J K)) ↔
    (n : RationalPoint k G.X)⁻¹ * (x : RationalPoint k G.X) * (n : RationalPoint k G.X) ∈
      levi i ν (leviIndex (associatedSubset cs J) K)
  exact conjugationMembership_of_map_eq _
    (associatedDescendantLevi_map_conj i ν hN hZ cs hLength hSimple hG hi hν hConj J K n hn) x

/-- Restrict the target's actual continuous associated-Levi equivalence to
its literal descendant-Levi subgroupOf families. -/
def associatedRestrictedLeviEquiv
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (levi i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf (levi i ν J) ≃ₜ*
      (levi i ν (leviIndex (associatedSubset cs J) K)).subgroupOf
        (levi i ν (associatedSubset cs J)) :=
  let e := associatedLeviConjugationEquiv i ν hG hi hν hConj hN hZ cs hLength hSimple
    hMin hAssoc J n hn
  let hm := associatedLeviConjugationEquiv_descendant_mem i ν hN hZ cs hLength hSimple
    hG hi hν hConj hMin hAssoc J K n hn
  { toFun x := ⟨e x, (hm x).mp x.property⟩
    invFun y := ⟨e.symm y, (hm _).mpr (by
      change e (e.symm (y : levi i ν (associatedSubset cs J))) ∈ _
      simpa only [e.apply_symm_apply] using y.property)⟩
    left_inv x := Subtype.ext (e.symm_apply_apply x)
    right_inv y := Subtype.ext (e.apply_symm_apply y)
    map_mul' x y := Subtype.ext (e.map_mul x y)
    continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
    continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _ }

/-- The restricted equivalence uses the original actual conjugating element. -/
@[simp]
theorem associatedRestrictedLeviEquiv_apply
    (J : Finset (SimpleRoot i ν)) (K : Finset (associatedSubset cs J))
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (x : (levi i ν (leviIndex J (associatedFinsetEquiv cs J K))).subgroupOf (levi i ν J)) :
    ((associatedRestrictedLeviEquiv i ν hN hZ cs hLength hSimple hG hi hν hConj
        hMin hAssoc J K n hn x : levi i ν (associatedSubset cs J)) : RationalPoint k G.X) =
      (n : RationalPoint k G.X)⁻¹ * ((x : levi i ν J) : RationalPoint k G.X) *
        (n : RationalPoint k G.X) := rfl

end Langlands.Aubert.General.RationalPointFamily

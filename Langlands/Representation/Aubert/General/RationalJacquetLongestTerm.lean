import Langlands.Representation.Aubert.General.RationalJacquetCommonTerm
import Langlands.Representation.Aubert.General.RationalJacquetSurvivorTerm
import Langlands.Representation.Aubert.General.RationalAssociatedLeviRestriction
import Langlands.Representation.Aubert.General.RationalAssociatedParabolicRestriction
import Langlands.Representation.Aubert.General.RationalHaarModulus

/-! # Longest-representative specialization of the actual common Jacquet term -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)] [Fintype (Weyl i)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})
  (hInter : StandardLeviIntersectionStatement.{u})
  (hStandard : StandardCocharacterStatement.{u})

local instance rationalLongestTermPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] [Fintype (Weyl i)] in
private theorem commonTerm_of_indices
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (w : Weyl i) (A : Finset (SimpleRoot i ν)) (B : Finset J)
    (H : Finset (SimpleRoot i ν))
    (hsupported : ∃ I, IsMinimal cs J I w ∧ simpleImage cs w I ∩ J = A)
    (htarget : A.subtype (· ∈ J) = B)
    (hsource : simpleImage cs w⁻¹ A = H)
    (hfine : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J B) ↔
        (lift w : RationalPoint k G.X)⁻¹ * x * (lift w : RationalPoint k G.X) ∈
          levi i ν H) :
    rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift w A =
      standardConjugatedJacquetTerm.{u, v}
        i ν hInter hG hi hν hStandard hU hM hfl hLfl J B H
        (lift w : RationalPoint k G.X) hfine := by
  subst B
  subst H
  exact rationalCommonJacquetTerm_of_supported.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj hInter hStandard hU hM hfl hLfl
    J lift hlift w A hsupported hfine

/-- Restrict the actual common Jacquet term to the longest representative and
label its survivors by the literal finite subsets of the associated Levi. -/
def rationalLongestJacquetTerm
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (K : Finset (associatedSubset cs J)) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) :=
  rationalCommonJacquetTerm.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl J lift hlift (longestRep cs J)
    (simpleImage cs (longestRep cs J) (leviIndex (associatedSubset cs J) K))

include hMin hAssoc hproj hLUc in
/-- At the longest representative, the supported common term is exactly the
literal transported associated-Levi term. All geometric and modulus inputs
are derived from the existing rational target hypotheses. -/
theorem rationalLongestJacquetTerm_eq_transported
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (K : Finset (associatedSubset cs J)) :
    rationalLongestJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift K =
      transportedLeviJacquetTerm.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν) hU hfl hM J (associatedSubset cs J)
        (lift (longestRep cs J) : RationalPoint k G.X)
        (conjugationMembership_of_map_eq _
          (associatedLeviConjugation_of_standard i ν hG hi hν hConj
            hN hZ cs hLength hSimple hMin hAssoc J _ (hlift _)))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J))
        (hLfl (associatedSubset cs J)) K := by
  have himage :
      simpleImage cs (longestRep cs J) (leviIndex (associatedSubset cs J) K) =
        leviIndex J (associatedFinsetEquiv cs J K) :=
    simpleImage_associatedFinsetEquiv cs J K
  have hsub :
      simpleImage cs (longestRep cs J) (leviIndex (associatedSubset cs J) K) ⊆ J := by
    rw [himage]
    exact leviIndex_subset J (associatedFinsetEquiv cs J K)
  have hsupported : ∃ I, IsMinimal cs J I (longestRep cs J) ∧
      simpleImage cs (longestRep cs J) I ∩ J =
        simpleImage cs (longestRep cs J) (leviIndex (associatedSubset cs J) K) := by
    refine ⟨leviIndex (associatedSubset cs J) K, ?_, Finset.inter_eq_left.mpr hsub⟩
    apply (isMinimal_iff_right_subset_positiveSimpleSet cs _ _ _).mpr
    refine ⟨(mem_minimalReps cs J ∅ _).mp (longestRep_mem cs J), ?_⟩
    rw [positiveSimpleSet_longestRep]
    exact leviIndex_subset (associatedSubset cs J) K
  have htarget :
      (simpleImage cs (longestRep cs J)
        (leviIndex (associatedSubset cs J) K)).subtype (· ∈ J) =
      associatedFinsetEquiv cs J K := by
    apply Finset.map_injective (Function.Embedding.subtype (· ∈ J))
    rw [Finset.subtype_map_of_mem (fun _ ha => hsub ha)]
    exact himage
  have hinverse :
      simpleImage cs (longestRep cs J)⁻¹
        (simpleImage cs (longestRep cs J) (leviIndex (associatedSubset cs J) K)) =
      leviIndex (associatedSubset cs J) K := by
    have h := simpleImage_inv_inter cs (longestRep cs J)⁻¹
      J (leviIndex (associatedSubset cs J) K)
    simp only [inv_inv, Finset.inter_eq_left.mpr hsub] at h
    exact h.trans (Finset.inter_eq_right.mpr (leviIndex_subset (associatedSubset cs J) K))
  have hfine := conjugationMembership_of_map_eq _
    (associatedDescendantLevi_map_conj i ν hN hZ cs hLength hSimple hG hi hν hConj
      J K (lift (longestRep cs J)) (hlift _))
  have heval := commonTerm_of_indices.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj hInter hStandard hU hM hfl hLfl
    J lift hlift (longestRep cs J) _ (associatedFinsetEquiv cs J K)
    (leviIndex (associatedSubset cs J) K) hsupported htarget hinverse hfine
  refine heval.trans (standardConjugatedJacquetTerm_eq_transported.{u, v}
    i ν hInter hG hi hν hStandard hU hM hfl hLfl
    (associatedSubset cs J) J K (associatedFinsetEquiv cs J K)
    (lift (longestRep cs J) : RationalPoint k G.X) _ hfine ?_ ?_
    (hLUc (associatedSubset cs J) K)
    (standardJacquetModulus_stages i ν hInter hG hi hν hStandard hproj
      (associatedSubset cs J) K hU (hM _)))
  · intro x
    exact (associatedRestrictedParabolic_unipotent_mem
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hStandard
      J K (lift (longestRep cs J)) (hlift _) x).1
  · intro x
    exact (associatedRestrictedParabolic_unipotent_mem
      i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hStandard
      J K (lift (longestRep cs J)) (hlift _) x).2

include hMin hAssoc hproj hLUc in
/-- The actual common term satisfies the survivor comparison required by the
conditional Jacquet assembly, for every specified lift at the longest element. -/
theorem rationalJacquetLongestTermReduction
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (hlongest : lift (longestRep cs J) = n) :
    JacquetLongestTermReduction.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν) hU hfl hM (torusPoints i) cs J
      (rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift)
      (associatedLeviConjugation_of_standard i ν hG hi hν hConj
        hN hZ cs hLength hSimple hMin hAssoc) n hn
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J))
      (hLfl (associatedSubset cs J)) := by
  subst n
  intro K
  exact rationalLongestJacquetTerm_eq_transported.{u, v}
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hConj
    hInter hStandard hU hM hfl hLfl hproj hLUc J lift hlift K

end Langlands.Aubert.General.RationalPointFamily

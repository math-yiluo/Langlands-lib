import Langlands.GroupScheme.Derived.SemisimplePerfectGeneration
import Langlands.GroupScheme.Reductive.TorusGenerationProof
import Langlands.GroupScheme.Derived.SemisimpleReflectionReduction
import Langlands.GroupScheme.Reductive.GeometricRootReflectionIntrinsic
import Langlands.GroupScheme.Rational.WeylPositiveCocharacter
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness

/-! # Perfectness of semisimple field groups by integral Weyl averaging -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace Langlands.GroupScheme

section Commutators

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  [Fintype (relativeWeylGroup i)]

/-- A vanishing integral Weyl sum puts every cocharacter in each closed
subgroup containing all commutators. -/
theorem cocharactersLandingIn_eq_top_of_weylSum_eq_zero
    {j : H ⟶ G} (hj : IsClosedSubgroup j)
    (hcomm : (SubgroupFunctor.range j).ContainsCommutators)
    (hzero : ∀ ν : cocharacterLattice T, relativeWeylCocharacterSum i ν = 0) :
    cocharactersLandingIn i (SubgroupFunctor.range j) = ⊤ := by
  classical
  apply top_unique
  intro ν _
  have hdiff (w : relativeWeylGroup i) :
      relativeWeylCocharacterAction i w ν - ν ∈
        cocharactersLandingIn i (SubgroupFunctor.range j) := by
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
    have he :
        relativeWeylCocharacterAction i (QuotientGroup.mk n) ν - ν =
          ν ≫ torusCommutatorEnd i n := by
      rw [relativeWeylCocharacterAction_mk, cocharacterAut_apply,
        torusCommutatorEnd, Preadditive.comp_sub, Category.comp_id]
    rw [he]
    exact cocharacter_torusCommutatorEnd_mem i hcomm n ν
  have hsum :
      (∑ w : relativeWeylGroup i, (relativeWeylCocharacterAction i w ν - ν)) ∈
        cocharactersLandingIn i (SubgroupFunctor.range j) :=
    Submodule.sum_mem _ fun w _ => hdiff w
  have he :
      (∑ w : relativeWeylGroup i, (relativeWeylCocharacterAction i w ν - ν)) =
        (-(Fintype.card (relativeWeylGroup i) : ℤ)) • ν := by
    rw [Finset.sum_sub_distrib, ← relativeWeylCocharacterSum_apply, hzero]
    simp
  apply mem_cocharactersLandingIn_of_zsmul_mem i hj
    (m := -(Fintype.card (relativeWeylGroup i) : ℤ))
    (neg_ne_zero.mpr (Int.natCast_ne_zero.mpr Fintype.card_ne_zero))
  rwa [← he]

end Commutators

section AlgebraicallyClosed

variable {k : Type u} [Field k] [IsAlgClosed k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
  (hG : IsConnectedReductive G) (hi : IsMaximalTorus i)

include hT hG hi

/-- The actual rank-one cocharacter centralizer supplies an ambient
normalizer that negates the selected root character. -/
theorem exists_normalizer_weylAction_eq_neg
    (α : characterLattice T) (hα : α ∈ relativeRoots i) :
    haveI := hi.2.1.mono
    ∃ n : normalizerPoints i, weylAction i n α = -α := by
  let := hi.2.1.mono
  let t := RankOneCentralizerDetection.torusHom i hT α hα.1
  let z := RankOneCentralizerDetection.inclusion i hT α hα.1
  let := (RankOneCentralizerDetection.isClosedSubgroup_torusHom
    i hT α hα.1 hi.2.1).mono
  obtain ⟨n, hn, -⟩ :=
    RankOneCentralizerDetection.exists_normalizer_inverting_and_fixing i hT hG hi α hα
  have hinv : (normalizingAut t n).inv ≫ α = -α := by
    calc
      _ = (normalizingAut t n).inv ≫ (-((normalizingAut t n).hom ≫ α)) := by
        rw [hn, neg_neg]
      _ = -α := by simp
  refine ⟨normalizerPointsMap t z i
    (RankOneCentralizerDetection.torusHom_comp i hT α hα.1) n, ?_⟩
  rw [weylAction_normalizerPointsMap, weylAction_apply]
  exact hinv

variable [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)]

/-- Root inversion forces the integral Weyl sum to annihilate every root.
No integral coroot or full reflection formula is required. -/
theorem latticePairing_weylSum_eq_zero_of_intrinsic_normalizers
    (ν : cocharacterLattice T) (α : characterLattice T)
    (hα : α ∈ relativeRoots i) :
    latticePairing T α (relativeWeylCocharacterSum i ν) = 0 := by
  obtain ⟨n, hn⟩ := exists_normalizer_weylAction_eq_neg i hT hG hi α hα
  have h := latticePairing_relativeWeyl i (QuotientGroup.mk n) α
    (relativeWeylCocharacterSum i ν)
  rw [relativeWeylCharacterAction_mk, hn, relativeWeylCocharacterSum_fixed,
    map_neg, LinearMap.neg_apply] at h
  omega

end AlgebraicallyClosed

/-- Every maximal torus in an algebraically closed semisimple field group
lies in the full scheme-theoretic derived subgroup. -/
theorem algebraicallyClosedSemisimpleMaximalTorusDerived :
    AlgebraicallyClosedSemisimpleMaximalTorusDerivedStatement.{u} := by
  intro k _ _ G hG T i hi
  let := hG.isConnectedReductive.smooth
  let := hG.isConnectedReductive.isAffineHom
  let := hi.2.1.mono
  have hT := hi.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  let : Finite (relativeWeylGroup i) :=
    hG.isConnectedReductive.finite_relativeWeylGroup_of_isMaximalTorus i hi hT
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  have hzero (ν : cocharacterLattice T) : relativeWeylCocharacterSum i ν = 0 :=
    hG.cocharacter_eq_zero_of_annihilates_relativeRoots hT hi.2.1 _
      (fun α hα => latticePairing_weylSum_eq_zero_of_intrinsic_normalizers
        i hT hG.isConnectedReductive hi ν α hα)
  intro U x hx H j hj hcomm
  exact hT.range_le_of_cocharacters i (SubgroupFunctor.range j)
    (cocharactersLandingIn_eq_top_of_weylSum_eq_zero i hj hcomm hzero) U hx

/-- Semisimple groups over arbitrary fields are perfect on all test schemes. -/
theorem semisimplePerfect : SemisimplePerfectStatement.{u} :=
  semisimplePerfect_of_maximalTorusDerived_of_torusGeneration
    algebraicallyClosedSemisimpleMaximalTorusDerived reductiveFiniteTorusGeneration

end Langlands.GroupScheme

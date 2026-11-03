import Langlands.Representation.Aubert.General.RationalJacquetTermCommon
import Langlands.Representation.Aubert.General.RationalJacquetLongestTerm
import Langlands.Representation.Aubert.General.RationalJacquetTarget

/-! # Rational Jacquet compatibility from literal intersection expansion -/

noncomputable section

open Classical CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj BigOperators

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

private theorem exists_normalizerSection_at
    {H : Type*} [Group H] (A : Subgroup H)
    (w : Group.RelativeWeyl.Weyl A) (n : Group.RelativeWeyl.normalizer A)
    (hn : QuotientGroup.mk n = w) :
    ∃ lift : Group.RelativeWeyl.Weyl A → Group.RelativeWeyl.normalizer A,
      (∀ x, QuotientGroup.mk (lift x) = x) ∧ lift w = n := by
  choose base hbase using
    (fun x : Group.RelativeWeyl.Weyl A => QuotientGroup.mk_surjective x)
  refine ⟨fun x => if x = w then n else base x, ?_, ite_eq_left rfl⟩
  intro x
  by_cases hx : x = w
  · subst x
    simpa using hn
  · simp only [ite_eq_right hx, hbase x]

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

local instance instRationalJacquetCancellation1 : DecidableEq (SimpleRoot i ν) := Classical.decEq _

local instance rationalJacquetCancellationPointTopology :
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

/-- The literal restricted-intersection expansion of `r_J i_I`, for every
section of the actual normalizer quotient. This is an explicit remaining
representation-theoretic proposition, not a consequence of its definition. -/
def rationalIntersectionExpansion (J : Finset (SimpleRoot i ν)) : Prop :=
  ∀ (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (I : Finset (SimpleRoot i ν)),
    (standardAmbientJacquetK0.{u, v}
        i ν hG hi hν hStandard hU hfl J).comp
        (inductionK0.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I) (hfl I).1 (hfl I).2.1) =
      ∑ w : {w : Weyl i // w ∈ minimalReps cs J I},
        rationalIntersectionJacquetTerm.{u, v}
          i ν hN hZ cs hLength hSimple hG hi hν hConj
          hInter hU hM hLfl J lift hlift I w
          ((mem_minimalReps cs J I w).mp w.property)

variable
  (hproj : ∀ A, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A).projection)
  (hLUc : ∀ (A : Finset (SimpleRoot i ν)) (B : Finset A),
    Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex A B)).subgroupOf (levi i ν A)))

include hMin hAssoc hproj hLUc in
/-- The literal intersection expansion implies the Jacquet identity for
every specified longest-representative lift. Stages, common-label reduction,
weighted cancellation and the survivor comparison are discharged here. -/
theorem rationalJacquetCompatibility_of_intersectionExpansion
    (J : Finset (SimpleRoot i ν))
    (hExpansion : rationalIntersectionExpansion.{u, v}
      i ν hN hZ cs hLength hSimple hG hi hν hConj
      hInter hStandard hU hM hfl hLfl J)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J) :
    (standardAmbientJacquetK0.{u, v}
        i ν hG hi hν hStandard hU hfl J).comp
        (alternatingOperator.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) hU hfl) =
      (conjugationK0.{u, max (u + 1) v} (n : RationalPoint k G.X)
        (conjugationMembership_of_map_eq _
          (associatedLeviConjugation_of_standard i ν hG hi hν hConj
            hN hZ cs hLength hSimple hMin hAssoc J n hn))).comp
        ((leviAlternatingOperator.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (associatedSubset cs J) (hM (associatedSubset cs J))
          (isSemidirectDecomposition_in_levi
            i ν hInter hG hi hν (associatedSubset cs J))
          hU (hLfl (associatedSubset cs J))).comp
          (standardAmbientJacquetK0.{u, v}
            i ν hG hi hν hStandard hU hfl (associatedSubset cs J))) := by
  obtain ⟨lift, hlift, hlongest⟩ :=
    exists_normalizerSection_at (torusPoints i) (longestRep cs J) n hn
  let F := rationalCommonJacquetTerm.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj
    hInter hStandard hU hM hfl hLfl J lift hlift
  have hrow (I : Finset (SimpleRoot i ν)) :
      (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl J).comp
          (alternatingTerm.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν) hU hfl I) =
        ∑ w : {w : Weyl i // w ∈ minimalReps cs J I},
          F w (simpleImage cs w I ∩ J) := by
    unfold alternatingTerm
    rw [← LinearMap.comp_assoc, hExpansion lift hlift I]
    calc
      _ = ∑ w : {w : Weyl i // w ∈ minimalReps cs J I},
          (rationalIntersectionJacquetTerm.{u, v}
            i ν hN hZ cs hLength hSimple hG hi hν hConj
            hInter hU hM hLfl J lift hlift I w
            ((mem_minimalReps cs J I w).mp w.property)).comp
            (standardAmbientJacquetK0.{u, v}
              i ν hG hi hν hStandard hU hfl I) := by
        apply LinearMap.ext
        intro x
        simp only [LinearMap.comp_apply, LinearMap.sum_apply, standardAmbientJacquetK0]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        convert rationalIntersectionJacquetTerm_comp_ambient_eq_common.{u, v}
          i ν hN hZ cs hLength hSimple hG hi hν hConj
          hInter hStandard hU hM hfl hLfl hproj hLUc J lift hlift I w
          ((mem_minimalReps cs J I w).mp w.property) using 1
        congr 1
        ext a
        simp only [Finset.mem_inter]
  have hweighted :
      (standardAmbientJacquetK0.{u, v}
          i ν hG hi hν hStandard hU hfl J).comp
          (alternatingOperator.{u, u, max (u + 1) v}
            (parabolic i ν) (levi i ν) (unipotent i ν)
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν) hU hfl) =
        jacquetWeightedExpansion cs J F := by
    trans ∑ I : Finset (SimpleRoot i ν), ((-1 : ℤ) ^ I.card) •
      ∑ w : {w : Weyl i // w ∈ minimalReps cs J I},
        F w (simpleImage cs w I ∩ J)
    · apply LinearMap.ext
      intro x
      simp only [alternatingOperator, LinearMap.comp_apply, LinearMap.sum_apply,
        LinearMap.smul_apply, map_sum, map_zsmul]
      apply Finset.sum_congr rfl
      intro I _
      simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
        congrArg (fun f => ((-1 : ℤ) ^ I.card) • f x) (hrow I)
    · unfold jacquetWeightedExpansion
      apply Finset.sum_congr rfl
      intro I _
      exact congrArg (fun z => ((-1 : ℤ) ^ I.card) • z)
        (Finset.sum_coe_sort (minimalReps cs J I)
          (fun w => F w (simpleImage cs w I ∩ J)))
  have hLongest := rationalJacquetLongestTermReduction.{u, v}
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hConj
    hInter hStandard hU hM hfl hLfl hproj hLUc J lift hlift n hn hlongest
  calc
    _ = jacquetWeightedExpansion cs J F := hweighted
    _ = ∑ K ∈ J.powerset, ((-1 : ℤ) ^ K.card) • F (longestRep cs J) K :=
      jacquetWeightedExpansion_eq_longest cs J F
    _ = ∑ K : Finset (associatedSubset cs J), ((-1 : ℤ) ^ K.card) •
        F (longestRep cs J)
          (simpleImage cs (longestRep cs J)
            (leviIndex (associatedSubset cs J) K)) :=
      signed_sum_associatedFinsetEquiv cs J (F (longestRep cs J))
    _ = ∑ K : Finset (associatedSubset cs J), ((-1 : ℤ) ^ K.card) •
        transportedLeviJacquetTerm.{u, u, max (u + 1) v}
          (parabolic i ν) (levi i ν) (unipotent i ν)
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν) hU hfl hM J (associatedSubset cs J)
          (n : RationalPoint k G.X)
          (conjugationMembership_of_map_eq _
            (associatedLeviConjugation_of_standard i ν hG hi hν hConj
              hN hZ cs hLength hSimple hMin hAssoc J n hn))
          (isSemidirectDecomposition_in_levi
            i ν hInter hG hi hν (associatedSubset cs J))
          (hLfl (associatedSubset cs J)) K :=
      Finset.sum_congr rfl fun K _ =>
        congrArg (fun z => ((-1 : ℤ) ^ K.card) • z) (hLongest K)
    _ = _ := sum_transportedLeviJacquetTerm.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν)
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν) hU hfl hM J (associatedSubset cs J)
      (n : RationalPoint k G.X)
      (conjugationMembership_of_map_eq _
        (associatedLeviConjugation_of_standard i ν hG hi hν hConj
          hN hZ cs hLength hSimple hMin hAssoc J n hn))
      (isSemidirectDecomposition_in_levi
        i ν hInter hG hi hν (associatedSubset cs J))
      (hLfl (associatedSubset cs J))

/-- Literal intersection expansions at the complete hypothesis scope of the
published Jacquet target. No representation comparison is hidden in this
predicate: its conclusion is precisely `r_J i_I = ∑` actual intersection terms. -/
def RationalIntersectionExpansionStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    letI : TopologicalSpace (RationalPoint k G.X) := pointTopology
    ∀ [LocallyCompactSpace (RationalPoint k G.X)]
      [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
      (ν : cocharacterLattice T) (hν : IsGenericCocharacter i ν)
      (hStandard : StandardCocharacterStatement.{u}) (hRoots : HasRelativeRootSystem i)
      (hInter : StandardLeviIntersectionStatement.{u})
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
      (hproj : ∀ I, Continuous
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν I).projection)
      (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
      (hiFl : ∀ I, PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hrFl : ∀ I, PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_of_standardCocharacterStatement
            i ν hStandard hG hi hν I) (hU I)))
      (hM : ∀ J, IsClosed (levi i ν J : Set (RationalPoint k G.X)))
      (hLproj : ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J),
        Continuous (standardLeviProjection i ν hInter hG hi hν J I))
      (hLUc : ∀ (J : Finset (SimpleRoot i ν)) (I : Finset J),
        Jacquet.Localization.IsLimitOfCompactSubgroups
          ((unipotent i ν (leviIndex J I)).subgroupOf (levi i ν J)))
      (hiLFl : ∀ J, letI := (hM J).locallyCompactSpace
        ∀ I : Finset J, PreservesFiniteLength
          (normalizedInductionFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
            ((hU (leviIndex J I)).preimage continuous_subtype_val)))
      (hrLFl : ∀ J, letI := (hM J).locallyCompactSpace
        ∀ I : Finset J, PreservesFiniteLength
          (jacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
            ((hU (leviIndex J I)).preimage continuous_subtype_val))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      ∀ [Fintype (Weyl i)]
        (hConj : StandardLeviConjugationStatement.{u})
        (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
        (CM : CoxeterMatrix (SimpleRoot i ν))
        (cs : ActualCoxeterSystem (torusPoints i) CM)
        (hLength : RootLengthComparison i ν hN hZ cs)
        (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
        (_hMin : minimalityLengthCriterion cs) (_hAssoc : associatedSubsetLaws cs),
        let fl := standardParabolicFiniteLength.{u, v}
          i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
        let flL := fun J => standardLeviParabolicFiniteLength.{u, v}
          i ν hInter hG hi hν hU hP J (hM J)
          (hLproj J) (hLUc J) (hiLFl J) (hrLFl J)
        ∀ J, rationalIntersectionExpansion.{u, v}
          i ν hN hZ cs hLength hSimple hG hi hν hConj
          hInter hStandard hU hM fl flL J

/-- The exact published target follows from literal intersection expansion
at its displayed preservation scope. This remains a conditional assembly. -/
theorem rationalJacquetCompatibility_of_intersectionExpansions
    (hExpansion : RationalIntersectionExpansionStatement.{u, v}) :
    RationalJacquetCompatibilityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots hInter hU hP hproj hUc hiFl hrFl
    hM hLproj hLUc hiLFl hrLFl
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ hConj hN hZ CM cs hLength hSimple hMin hAssoc
  dsimp only
  intro J n hn
  exact rationalJacquetCompatibility_of_intersectionExpansion.{u, v}
    i ν hN hZ cs hLength hSimple hMin hAssoc hG hi hν hConj
    hInter hStandard hU hM
    (standardParabolicFiniteLength.{u, v}
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (fun A => standardLeviParabolicFiniteLength.{u, v}
      i ν hInter hG hi hν hU hP A (hM A)
      (hLproj A) (hLUc A) (hiLFl A) (hrLFl A))
    hproj hLUc J
    (hExpansion k G hG T i hi ν hν hStandard hRoots hInter hU hP
      hproj hUc hiFl hrFl hM hLproj hLUc hiLFl hrLFl
      hConj hN hZ CM cs hLength hSimple hMin hAssoc J) n hn

end Langlands.Aubert.General.RationalPointFamily

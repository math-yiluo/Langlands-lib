import Langlands.Representation.Aubert.General.RationalAlternatingOperator
import Langlands.Representation.Aubert.General.RationalLeviFiniteLength
import Langlands.Representation.Aubert.General.RationalAssociatedLeviConjugation
import Mathlib.NumberTheory.LocalField.Basic

/-! # Longest-representative Jacquet compatibility on actual rational points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The Jacquet equation of Aubert Theorem 1.7(2) for every lift of the
specified longest representative, with derived actual associated-Levi transport. -/
def RationalJacquetCompatibilityStatement : Prop :=
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
        (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs),
        let D := rationalAlternatingOperator.{u, v}
          i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots
        ∀ (J : Finset (SimpleRoot i ν))
          (n : Group.RelativeWeyl.normalizer (torusPoints i))
          (hn : QuotientGroup.mk n = longestRep cs J),
          let J' := associatedSubset cs J
          let hfl := standardParabolicFiniteLength.{u, v}
            i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
          let rJ := jacquetK0.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν J) (hU J) (hfl J).2.2.1 (hfl J).2.2.2
          let rJ' := jacquetK0.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν J') (hU J') (hfl J').2.2.1 (hfl J').2.2.2
          let DL' := rationalLeviAlternatingOperator.{u, v}
            i ν hInter hG hi hν hU hP J' (hM J')
            (hLproj J') (hLUc J') (hiLFl J') (hrLFl J')
          let transport := conjugationK0.{u, max (u + 1) v}
            (n : RationalPoint k G.X)
            (conjugationMembership_of_map_eq _
              (associatedLeviConjugation_of_standard i ν hG hi hν hConj
                hN hZ cs hLength hSimple hMin hAssoc J n hn))
          rJ.comp D = transport.comp (DL'.comp rJ')

end Langlands.Aubert.General.RationalPointFamily

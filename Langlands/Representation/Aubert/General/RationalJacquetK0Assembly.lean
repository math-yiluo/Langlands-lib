import Langlands.Representation.Aubert.General.JacquetK0Assembly
import Langlands.Representation.Aubert.General.RationalJacquetTarget

/-! # Conditional Jacquet assembly for the actual rational-point family -/

noncomputable section

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

local instance rationalJacquetAssemblyPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I) (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I) (hU I)))
  (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X)))
  (hRoots : HasRelativeRootSystem i)

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- The actual rational-point signed geometric sum after ambient Jacquet
restriction, at the target's canonical finite root enumeration. -/
def rationalJacquetGeometricSum :
  letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  ∀ [Fintype (Weyl i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM)
    (hGeom : GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
    (_hTermFl : ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
      (hw : IsMinimal cs I J w)
      (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w),
      GeometricTermFiniteLength.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : RationalPoint k G.X)
        (hGeom I J w hw n hn).1 (hGeom I J w hw n hn).2)
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (_hlift : ∀ w, QuotientGroup.mk (lift w) = w),
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) := by
  letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro instWeyl CM cs hGeom hTermFl J lift hlift
  exact jacquetGeometricSum.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hM
    (torusPoints i) cs hGeom hTermFl J lift hlift

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
/-- Specialize the conditional finite assembly to the exact rational-point
families and target's derived associated-Levi transport. The three extra
representation comparison inputs are not discharged by this theorem. -/
theorem rationalJacquetCompatibility_of_geometricExpansion :
  letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  ∀ [Fintype (Weyl i)]
    {CM : CoxeterMatrix (SimpleRoot i ν)}
    (cs : ActualCoxeterSystem (torusPoints i) CM)
    (hGeom : GeometricIntersectionDecompositions
      (parabolic i ν) (levi i ν) (unipotent i ν) (torusPoints i) cs)
    (hTermFl : ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i)
      (hw : IsMinimal cs I J w)
      (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w),
      GeometricTermFiniteLength.{u, u, max (u + 1) v}
        (parabolic i ν) (levi i ν) (unipotent i ν) hM hU I J (n : RationalPoint k G.X)
        (hGeom I J w hw n hn).1 (hGeom I J w hw n hn).2),
  let std := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  let fl := standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl
  ∀ (_hExpansion : GeometricK0ExpansionStatement.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) std hU fl hM (torusPoints i) cs hGeom hTermFl)
    (J : Finset (SimpleRoot i ν))
    (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
    (hlift : ∀ w, QuotientGroup.mk (lift w) = w)
    (F : Weyl i → Finset (SimpleRoot i ν) →
      (FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
        FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J)))
    (hInter : StandardLeviIntersectionStatement.{u})
    (hConj : StandardLeviConjugationStatement.{u})
    (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
    (hLength : RootLengthComparison i ν hN hZ cs)
    (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
    (hMin : minimalityLengthCriterion cs) (hAssoc : associatedSubsetLaws cs)
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (hn : QuotientGroup.mk n = longestRep cs J)
    (hLproj : ∀ I : Finset (associatedSubset cs J), Continuous
      (standardLeviProjection i ν hInter hG hi hν (associatedSubset cs J) I))
    (hLUc : ∀ I : Finset (associatedSubset cs J), Jacquet.Localization.IsLimitOfCompactSubgroups
      ((unipotent i ν (leviIndex (associatedSubset cs J) I)).subgroupOf (levi i ν (associatedSubset cs J))))
    (hiLFl : letI := (hM (associatedSubset cs J)).locallyCompactSpace
      ∀ I : Finset (associatedSubset cs J), PreservesFiniteLength
        (normalizedInductionFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J) I)
          ((hU (leviIndex (associatedSubset cs J) I)).preimage continuous_subtype_val)))
    (hrLFl : letI := (hM (associatedSubset cs J)).locallyCompactSpace
      ∀ I : Finset (associatedSubset cs J), PreservesFiniteLength
        (jacquetFunctor.{u, max (u + 1) v}
          (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J) I)
          ((hU (leviIndex (associatedSubset cs J) I)).preimage continuous_subtype_val))),
  let assoc := associatedLeviConjugation_of_standard
    i ν hG hi hν hConj hN hZ cs hLength hSimple hMin hAssoc
  let stdL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J)
  let flL := standardLeviParabolicFiniteLength.{u, v} i ν hInter hG hi hν hU hP
    (associatedSubset cs J) (hM (associatedSubset cs J)) hLproj hLUc hiLFl hrLFl
  ∀ (_hReduction : JacquetGeometricTermReduction.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) std hU fl hM
      (torusPoints i) cs hGeom hTermFl J lift hlift F)
    (_hLongest : JacquetLongestTermReduction.{u, u, max (u + 1) v}
      (parabolic i ν) (levi i ν) (unipotent i ν) std hU fl hM
      (torusPoints i) cs J F assoc n hn stdL flL),
    (jacquetK0.{u, max (u + 1) v}
      (std J) (hU J) (fl J).2.2.1 (fl J).2.2.2).comp
        (rationalAlternatingOperator.{u, v}
          i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots) =
      (conjugationK0.{u, max (u + 1) v} (n : RationalPoint k G.X)
        (conjugationMembership_of_map_eq _ (assoc J n hn))).comp
        ((rationalLeviAlternatingOperator.{u, v}
          i ν hInter hG hi hν hU hP (associatedSubset cs J) (hM (associatedSubset cs J))
          hLproj hLUc hiLFl hrLFl).comp
          (jacquetK0.{u, max (u + 1) v}
            (std (associatedSubset cs J)) (hU (associatedSubset cs J))
            (fl (associatedSubset cs J)).2.2.1 (fl (associatedSubset cs J)).2.2.2)) := by
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  dsimp only
  intro instWeyl CM cs hGeom hTermFl hExpansion J lift hlift F hInter hConj hN hZ
    hLength hSimple hMin hAssoc n hn hLproj hLUc hiLFl hrLFl hReduction hLongest
  exact jacquetCompatibility_of_geometricExpansion.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardParabolicFiniteLength.{u, v} i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hM
    (torusPoints i) cs hGeom hTermFl hExpansion J lift hlift F
    (associatedLeviConjugation_of_standard i ν hG hi hν hConj hN hZ cs hLength hSimple hMin hAssoc)
    n hn (isSemidirectDecomposition_in_levi i ν hInter hG hi hν (associatedSubset cs J))
    (standardLeviParabolicFiniteLength.{u, v} i ν hInter hG hi hν hU hP
      (associatedSubset cs J) (hM (associatedSubset cs J)) hLproj hLUc hiLFl hrLFl)
    hReduction hLongest

end Langlands.Aubert.General.RationalPointFamily

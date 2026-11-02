import Langlands.Representation.Aubert.General.RationalParabolicDecomposition
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.GroupScheme.Rational.RootFiniteness

/-! # The unadjusted operator on the standard rational-point family -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open SmoothRep

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
  (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
  (hP : ∀ I, IsClosed (parabolic i ν I : Set (RationalPoint k G.X)))
  (hproj : ∀ I, Continuous
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I).projection)
  (hUc : ∀ I, Jacquet.Localization.IsLimitOfCompactSubgroups (unipotent i ν I))
  (hiFl : ∀ I, PreservesFiniteLength
    (normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))
  (hrFl : ∀ I, PreservesFiniteLength
    (jacquetFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I)))

include hP hproj hUc hiFl hrFl in
/-- Exactness is supplied by the existing topological theorems; only the two
finite-length preservation premises are representation-theoretic inputs here. -/
theorem standardParabolicFiniteLength (I : Finset (SimpleRoot i ν)) :
    ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
      (hU I) :=
  ParabolicFiniteLength.of_preservesFiniteLength
    (compactOpenCofinal_of_nonarchimedean _)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
    (hU I) (hP I)
    (hproj I) (hUc I) (hiFl I) (hrFl I)

omit [T2Space (RationalPoint k G.X)] in
include hUc in
/-- The compact-limit premise also supplies precisely the unimodularity
needed for the source normalization of induction. -/
theorem standardUnipotent_isUnimodular (I : Finset (SimpleRoot i ν)) :
    IsUnimodularModulus (unipotent i ν I) (hU I) :=
  isUnimodularModulus_of_isLimitOfCompactSubgroups _ (hU I) (hUc I)

variable [Mono i.hom.hom.left] (hRoots : HasRelativeRootSystem i)

/-- Aubert's unadjusted operator on the exact rational-point family, using
the canonical evaluation topology and the actual simple-root enumeration. -/
def rationalAlternatingOperator :
    FiniteLengthGrothendieckGroup.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X) :=
  letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  alternatingOperator.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
    (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)

/-- Its class formula uses the actual normalized induction and Jacquet
functors, with coefficient `(-1)^|I|` and no further rank sign. -/
theorem rationalAlternatingOperator_ofRepresentation
    (A : SmoothRep.{0, _, max (u + 1) v} ℂ (RationalPoint k G.X))
    (hA : A.HasFiniteLength) :
    let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    rationalAlternatingOperator i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots
        (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
      ∑ I : Finset (SimpleRoot i ν), ((-1 : ℤ) ^ I.card) •
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((inductionJacquetFunctor.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν I)
            (hU I)).obj A)
          ((hiFl I) _ ((hrFl I) A hA)) := by
    let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    exact alternatingOperator_ofRepresentation.{u, u, max (u + 1) v} _ _ _ _ _ _ A hA

/-- With no simple roots the same construction has the single empty-index
term with coefficient `+1`; no endpoint subgroup equality is inferred. -/
theorem rationalAlternatingOperator_of_isEmpty [IsEmpty (SimpleRoot i ν)] :
    let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    rationalAlternatingOperator i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots =
      alternatingTerm.{u, u, max (u + 1) v} (parabolic i ν) (levi i ν) (unipotent i ν)
        (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν) hU
        (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) ∅ := by
    let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    exact alternatingOperator_of_isEmpty.{u, u, max (u + 1) v} _ _ _ _ _ _

end Langlands.Aubert.General.RationalPointFamily

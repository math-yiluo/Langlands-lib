import Langlands.Representation.Aubert.General.RationalContragredientTarget
import Langlands.Representation.Aubert.General.ContragredientReduction

/-! # Rational-point specialization of the exact-K0 duality reduction -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

section Family

variable {k : Type u} [Field k] [TopologicalSpace k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance : TopologicalSpace (RationalPoint k G.X) := pointTopology

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hRoots : HasRelativeRootSystem i)
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)] [T2Space (RationalPoint k G.X)]
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
  (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
    (RationalPoint k G.X))

/-- The additional term comparison on the literal standard rational-point
family. Its proof is a separate representation-theoretic obligation. -/
def standardContragredientTermComparison : Prop :=
  ContragredientTermComparison.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl) hc

/-- A proved term comparison suffices for the literal rational operator and
actual ambient smooth dual on the whole exact finite-length K0. -/
theorem rationalContragredientCommutation_of_standardTermComparison
    (hcompare : standardContragredientTermComparison
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hc) :
    (rationalAlternatingOperator.{u, v}
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots).comp
      (contragredientK0.{u, max (u + 1) v} (RationalPoint k G.X)
        (compactOpenCofinal_of_nonarchimedean _) hc) =
    (contragredientK0.{u, max (u + 1) v} (RationalPoint k G.X)
      (compactOpenCofinal_of_nonarchimedean _) hc).comp
      (rationalAlternatingOperator.{u, v}
        i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hRoots) := by
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact contragredientCommutation_of_termComparison.{u, u, max (u + 1) v}
    (parabolic i ν) (levi i ν) (unipotent i ν)
    (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν)
    hU (standardParabolicFiniteLength i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    (compactOpenCofinal_of_nonarchimedean _) hc hcompare

end Family

/-- A sufficient closed prerequisite, with exactly the field, group, topology,
universe and visible premises of the published commutation target. This is a
new statement of the outstanding class comparison, not its proof. -/
def RationalContragredientTermComparisonStatement : Prop :=
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
      (hStandard : StandardCocharacterStatement.{u}) (_hRoots : HasRelativeRootSystem i)
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
      (hc : ContragredientPreservesFiniteLength.{u, max (u + 1) v}
        (RationalPoint k G.X)),
      standardContragredientTermComparison
        i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hc

/-- This implication preserves the original closed target. A proof of the
antecedent is still required; the implication alone is not its proof. -/
theorem rationalContragredientCommutation_of_termComparison
    (hcompare : RationalContragredientTermComparisonStatement.{u, v}) :
    RationalContragredientCommutationStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl hc
  exact rationalContragredientCommutation_of_standardTermComparison (hRoots := hRoots)
    i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl hc
    (hcompare k G hG T i hi ν hν hStandard hRoots hU hP hproj hUc hiFl hrFl hc)

end Langlands.Aubert.General.RationalPointFamily

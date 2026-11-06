import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Category.SmoothCoproducts

/-! # A finite induced-cuspidal embedding target from Renard VI.7.2

This existential consequence of the actual I/R unit embedding is stated without
assuming any decomposition or embedding theorem. The source universe is free;
the full function and finite-sum target carriers are explicitly enlarged.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

universe uI uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {κ : Type uI} [Fintype κ]
  (P M U : Finset κ → Subgroup G)
  (h : ∀ I, IsSemidirectDecomposition (P I) (M I) (U I))
  (hU : ∀ I, IsClosed (U I : Set G))
  (hM : ∀ I, IsClosed (M I : Set G))
  (hL : ∀ (I : Finset κ) (J : Finset I),
    IsSemidirectDecomposition ((P (leviIndex I J)).subgroupOf (M I))
      ((M (leviIndex I J)).subgroupOf (M I)) ((U (leviIndex I J)).subgroupOf (M I)))

/-- Every smooth object embeds equivariantly into the actual finite direct sum
of normalized inductions of cuspidal objects from the standard Levis. -/
def FiniteCuspidalInducedEmbeddingTarget : Prop :=
  letI := Classical.decEq (Finset κ)
  ∀ E : SmoothRep.{0, uG, uV} ℂ G,
    ∃ τ : ∀ I : Finset κ, SmoothRep.{0, uG, max uI uG uV} ℂ (M I),
      (∀ I, IsLeviCuspidal P M U hU I (hM I) (hL I) (τ I)) ∧
      ∃ f : E.representation.IntertwiningMap
        (SmoothRep.directSum.{uG, uI, max uG uV} (fun I =>
          (normalizedInductionFunctor.{uG, max uI uG uV} (h I) (hU I)).obj (τ I))).representation,
        Function.Injective f

end Langlands.Aubert.General

namespace Langlands.Aubert.General.RationalPointFamily

universe u v

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

/-- The finite induced-cuspidal embedding on the actual standard rational-point
family. All structural family comparisons remain explicit; no representation
finiteness, category decomposition or I/R faithfulness is a premise. -/
def RationalCuspidalInducedEmbeddingStatement : Prop :=
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
      (hStandard : StandardCocharacterStatement.{u})
      (hInter : StandardLeviIntersectionStatement.{u})
      (hRoots : HasRelativeRootSystem i)
      (hU : ∀ I, IsClosed (unipotent i ν I : Set (RationalPoint k G.X)))
      (hM : ∀ I, IsClosed (levi i ν I : Set (RationalPoint k G.X))),
      letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
      FiniteCuspidalInducedEmbeddingTarget.{u, u, v}
        (P := parabolic i ν) (M := levi i ν) (U := unipotent i ν)
        (h := isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν)
        (hU := hU) (hM := hM)
        (hL := isSemidirectDecomposition_in_levi i ν hInter hG hi hν)

end Langlands.Aubert.General.RationalPointFamily

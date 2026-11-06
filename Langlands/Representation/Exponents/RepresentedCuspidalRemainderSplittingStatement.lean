import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport

/-! # The represented objectwise cuspidal/remainder splitting

A consequence of Renard VI.3.5, stated for all actual rational parabolics.
The existence statement is an open prerequisite. The implication to VI.5.2
below keeps that prerequisite explicit.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- The objectwise two-summand consequence of Renard VI.3.5: every smooth
representation of a connected reductive group over a nonarchimedean local
field has an actual cuspidal/remainder coproduct, where supercuspidality
is tested on every proper actual rational parabolic. -/
def RepresentedCuspidalRemainderSplittingStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      HasCuspidalRemainderSplitting A

/-- The exact represented VI.5.2 follows from the objectwise splitting.
No part of the splitting's existence is proved by this implication. -/
theorem leviInductionNoSupercuspidalSubquotient_of_cuspidalRemainderSplitting
    (hsplit : RepresentedCuspidalRemainderSplittingStatement.{u, max u v}) :
    LeviInductionNoSupercuspidalSubquotientStatement.{u, v} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul hproper
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro ρ σ hσ hsub
  let : σ.representation.IsIrreducible := hσ
  have hnontrivial : Nontrivial σ :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (rationalPoints G)) σ.representation.asModule
  exact no_supercuspidal_subquotient_of_induction_splitting
    hG p l r hp hl hr hmul hproper ρ
    (hsplit k G hG _) σ hnontrivial hsub

end Langlands.Aubert.General.RepresentedParabolic

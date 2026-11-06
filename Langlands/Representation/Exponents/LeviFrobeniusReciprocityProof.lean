import Langlands.Representation.Exponents.LeviFrobeniusReciprocityStatement
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Aubert.General.FirstAdjointness

/-! # Proof of Frobenius reciprocity for normalized parabolic induction

Renard 2026, VI.1.2 Proposition, adjunction part, for represented parabolics.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Intertwiners into an inverse pullback are intertwiners out of the pullback, with the
same underlying linear map. -/
def intertwiningPullbackEquiv {H N : Type*} [Group H] [Group N] [TopologicalSpace H]
    [TopologicalSpace N] (e : H ≃ₜ* N) {V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ N V) (σ : Representation ℂ H W) :
    ρ.IntertwiningMap (σ.comp e.symm.toMonoidHom) ≃ₗ[ℂ]
      Representation.IntertwiningMap (ρ.comp e.toMonoidHom) σ where
  toFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' h := by
        have hf := f.isIntertwining' (e h)
        change f.toLinearMap ∘ₗ ρ (e h) = σ (e.symm (e h)) ∘ₗ f.toLinearMap at hf
        rw [e.symm_apply_apply] at hf
        exact hf }
  invFun f :=
    { toLinearMap := f.toLinearMap
      isIntertwining' n := by
        have hf := f.isIntertwining' (e.symm n)
        change f.toLinearMap ∘ₗ ρ (e (e.symm n)) = σ (e.symm n) ∘ₗ f.toLinearMap at hf
        rw [e.apply_symm_apply] at hf
        exact hf }
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- Renard VI.1.2 Proposition, adjunction part: Frobenius reciprocity for the
normalized functors of a represented parabolic. -/
theorem leviFrobeniusReciprocity : LeviFrobeniusReciprocityStatement.{u, v, w} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  have := hl.isConnectedReductive.isAffineHom
  let : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
  have : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
  have : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
  intro π σ
  have hδ := isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1
  exact ⟨(FirstAdjointness.equiv
      (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
      (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup) hδ π
      (SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ)).trans
    (intertwiningPullbackEquiv (leviPointsEquiv p l hp hl) _ σ.representation),
    fun _ _ => rfl⟩

end Langlands.Aubert.General.RepresentedParabolic

import Langlands.Algebra.BrauerComparison.RelativeLaws
import Langlands.Algebra.BrauerSplitting

/-! # Two-torsion in the relative Brauer class -/

noncomputable section

open scoped TensorProduct

universe u v

namespace Langlands.Brauer

variable {K : Type u} [Field K] {A : CSA.{u, u} K}

/-- A central simple algebra isomorphic to its opposite has a Brauer class killed by two. -/
theorem two_nsmul_classOf_eq_zero_of_equiv_opposite (f : A ≃ₐ[K] Aᵐᵒᵖ) :
    2 • classOf A = 0 := by
  have h : classOf A = -classOf A :=
    (classOf_eq_of_algEquiv (B := opposite A) f).trans (classOf_opposite A)
  calc
    2 • classOf A = classOf A + classOf A := two_nsmul _
    _ = classOf A + -classOf A := congrArg (classOf A + ·) h
    _ = 0 := add_neg_cancel _

end Langlands.Brauer

namespace Langlands.BrauerComparison

open Langlands.Brauer Langlands.CentralSimple

variable {K L : Type u} [Field K] [Field L] [Algebra K L]
  {A : CSA.{u, u} K} {I : Type v} [Fintype I] [DecidableEq I] [Nonempty I]

/-- If the actual Brauer class is killed by two, so is the relative class
of every matrix splitting chart. -/
theorem two_nsmul_relativeClass_eq_zero (e : L ⊗[K] A ≃ₐ[L] Matrix I I L)
    (h : 2 • Brauer.classOf A = 0) : 2 • relativeClass e = 0 := by
  have hzero : Brauer.classOf (Brauer.tensor A A) = 0 := by
    rw [Brauer.classOf_tensor, ← two_nsmul, h]
  obtain ⟨m, hm, ⟨f₀⟩⟩ := (Brauer.classOf_eq_zero_iff _).mp hzero
  let : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  let f : A ⊗[K] A ≃ₐ[K] Matrix (Fin m) (Fin m) K := f₀
  rw [two_nsmul, ← relativeClass_tensor]
  exact (relativeClass_eq_of_indices _ (splitPresentationChart (L := L) f)).trans
    (relativeClass_eq_zero_of_split _ f)

/-- Actual Brauer two-torsion gives relative two-torsion in a splitting chart. -/
def RelativeBrauerTwoTorsionStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    (A : CSA.{u, u} K) (I : Type v) [Fintype I] [DecidableEq I] [Nonempty I]
    (e : L ⊗[K] A ≃ₐ[L] Matrix I I L), 2 • Brauer.classOf A = 0 → 2 • relativeClass e = 0

/-- The tensor square of the chart computes twice its relative class. -/
theorem relativeBrauerTwoTorsion : RelativeBrauerTwoTorsionStatement.{u, v} := by
  intro K L _ _ _ A I _ _ _ e h
  exact two_nsmul_relativeClass_eq_zero e h

end Langlands.BrauerComparison

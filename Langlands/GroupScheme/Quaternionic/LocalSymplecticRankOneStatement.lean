import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.ElementarySubgroup
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Quaternionic symplectic groups of rank one over local fields

Statement only: the symplectic group of a nondegenerate antihermitian form of rank 2 or 3
and Witt index 1 over a quaternion division algebra with an involution of the first kind
whose symmetric elements have dimension 3 is simply connected, almost simple and of split
rank one, over every nonarchimedean local field.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- Over every nonarchimedean local field `K`, let `D` be a quaternion central division
`K`-algebra and `σ` an involution of the first kind of `D` with `dim_K D^σ = 3`. For
`m = 2` or `3`, the symplectic group of every nondegenerate `σ`-antihermitian form on `D^m`
of Witt index `1` is simply connected, almost simple and of split rank one. -/
def LocalSymplecticRankOneStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ (m : ℕ) [NeZero m], (m = 2 ∨ m = 3) →
    ∀ H : Matrix (Fin m) (Fin m) D, σ.IsAntihermitian H → IsUnit H → σ.wittIndex H = 1 →
      IsSimplyConnected (σ.symplecticGroup H) ∧ IsAlmostSimple (σ.symplecticGroup H) ∧
        splitRank (σ.symplecticGroup H) = 1

end Langlands.GroupScheme.Quaternionic

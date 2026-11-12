import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Rational.ElementarySubgroup
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Quaternionic spin groups of rank one over local fields

Statement only: a nondegenerate quadratic form, in the sense of Tits, of rank 4 or 5 and Witt
index 1 over a quaternion division algebra with an involution of the first kind whose
symmetric elements have dimension 3 has a spin group, and every spin group of such a form is
simply connected, almost simple and of split rank one, over every nonarchimedean local field.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- Over every nonarchimedean local field `K`, let `D` be a quaternion central division
`K`-algebra and `σ` an involution of the first kind of `D` with `dim_K D^σ = 3`. For
`m = 4` or `5` and every nondegenerate `σ`-quadratic form `q` on `D^m` of Witt index `1`,
a spin group of `q` exists, and every spin group of `q` is simply connected, almost simple and
of split rank one. -/
def LocalSpinRankOneStatement : Prop :=
  ∀ (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (D : Type u) [DivisionRing D] [Algebra K D] [Algebra.IsCentral K D]
    [FiniteDimensional K D],
    Module.finrank K D = 4 →
    ∀ σ : FirstKindInvolution K D, Module.finrank K σ.symmetricSubspace = 3 →
    ∀ m : ℕ, (m = 4 ∨ m = 5) →
    ∀ q : σ.QuadraticForms (Fin m), σ.IsNondegenerateQuadratic q →
      σ.quadraticWittIndex q = 1 →
      (∃ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
          σ.IsSpinCover q π) ∧
        ∀ (S : GroupScheme (Spec (CommRingCat.of K))) (π : S ⟶ σ.isometryGroup q),
          σ.IsSpinCover q π →
            IsSimplyConnected S ∧ IsAlmostSimple S ∧ splitRank S = 1

end Langlands.GroupScheme.Quaternionic

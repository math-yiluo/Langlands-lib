import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.SchemeAction
import Langlands.GroupScheme.GeneralLinear
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # A proper `GL_N`-scheme whose point stabilizers are solvable -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, `GL_N` acts on a nonempty proper scheme in which every
closed subgroup fixing a rational point is solvable (for instance the scheme of full flags). -/
def GeneralLinearSolvableStabilizerStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] (N : ℕ),
    ∃ (X : Over (Spec (CommRingCat.of k)))
      (a : SchemeAction (GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)) X),
      IsProper X.hom ∧ Nonempty X.left ∧
        ∀ (x : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ X)
          (H : GroupScheme (Spec (CommRingCat.of k)))
          (i : H ⟶ GeneralLinear.groupScheme (Fin N) (CommRingCat.of k)),
          IsClosedSubgroup i → (a.restrict i).IsFixed x → IsSolvableGroupScheme H

end Langlands.GroupScheme

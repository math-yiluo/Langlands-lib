import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Topology.Sheaves.Flasque

/-!
# Abelian sheaves with finite closed support

A derived statement about actual abelian stalks, flasqueness, and detection
of the zero sheaf by global sections.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.Cohomology

/-- An abelian sheaf whose nonzero stalks lie in a finite set of closed points
is flasque, and its global-section object is zero exactly when the sheaf is zero. -/
def FiniteClosedSupportSheafStatement : Prop :=
  ∀ (X : TopCat.{u}) (F : TopCat.Sheaf AddCommGrpCat.{u} X) (S : Set X),
    S.Finite →
    (∀ x ∈ S, IsClosed ({x} : Set X)) →
    (∀ x, x ∉ S →
      IsZero ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).obj F.obj)) →
    TopCat.Presheaf.IsFlasque F.obj ∧
      (IsZero (F.obj.obj (Opposite.op (⊤ : TopologicalSpace.Opens X))) ↔
        IsZero F)

end Langlands.Cohomology

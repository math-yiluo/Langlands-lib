import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Monicity over finite coefficient subalgebras -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteCoefficient

/-- Monicity of a specified scheme map descends to finite coefficients
when its source is of finite type and its target is quasi-separated over
the coefficient base. -/
def MonomorphismStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (X Y : Over (Spec (CommRingCat.of R)))
    [QuasiCompact X.hom] [LocallyOfFiniteType X.hom] [QuasiSeparated Y.hom]
    (f : X ⟶ Y),
    Mono ((Over.pullback (Spec.algebraMap R A)).map f).left →
    ∀ (s : Finset A), ∃ T : Subalgebra R A, T.FG ∧ (s : Set A) ⊆ T ∧
      Mono ((Over.pullback (Spec.algebraMap R T)).map f).left

end Langlands.AlgebraicGeometry.FiniteCoefficient

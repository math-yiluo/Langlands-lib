import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Descent of ample existence along finite field extensions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- If the base change of a scheme over a field `K` to a finite field extension `L`
admits an actual ample line bundle, then so does the scheme itself.
This proposition is a statement target, not a proof. -/
def FiniteFieldExtensionAmpleExistenceDescentStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K)),
    (∃ M : LineBundle
        (CategoryTheory.Limits.pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))),
      M.IsAmple) →
      ∃ N : LineBundle X, N.IsAmple

end Langlands.AlgebraicGeometry.Picard

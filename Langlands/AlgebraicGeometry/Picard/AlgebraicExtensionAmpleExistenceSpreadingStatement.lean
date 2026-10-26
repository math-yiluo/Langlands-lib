import Langlands.AlgebraicGeometry.Picard.Ample
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.FieldTheory.IntermediateField.Algebraic

/-! # Spreading ample existence to a finite intermediate field -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a proper scheme over a field `K` and an algebraic extension `Ω / K`, if the base
change to `Ω` admits an actual ample line bundle, then so does the base change to some
finite-dimensional intermediate field `K ⊆ E ⊆ Ω`.
This proposition is a statement target, not a proof. -/
def AlgebraicExtensionAmpleExistenceSpreadingStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [Algebra.IsAlgebraic K Ω]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K)),
    IsProper p →
    (∃ M : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))),
      M.IsAmple) →
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
      ∃ M : LineBundle (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K E)))),
        M.IsAmple

end Langlands.AlgebraicGeometry.Picard

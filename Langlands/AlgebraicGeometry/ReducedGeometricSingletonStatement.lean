import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Statement: descent of a reduced geometric singleton -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A locally finite type scheme over a field is isomorphic to its base if its
base change to an algebraically closed extension is reduced and has exactly one
underlying topological point. This definition states the descent target; it does
not supply a proof. -/
def ReducedGeometricSingletonStatement : Prop :=
  ∀ (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K)),
    LocallyOfFiniteType f →
    let XΩ := pullback f (Spec.map (CommRingCat.ofHom (algebraMap K Ω)))
    _root_.AlgebraicGeometry.IsReduced XΩ →
      Nonempty XΩ → Subsingleton XΩ → IsIso f

end Langlands.AlgebraicGeometry

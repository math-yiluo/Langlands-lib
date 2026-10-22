import Langlands.AbelianScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Pointed-morphism rigidity over an arbitrary base -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- A morphism from a geometrically abelian group scheme to a group scheme
of finite presentation is a homomorphism if it preserves the unit. -/
def PointedMorphismRigidity : Prop :=
  ∀ (S : Scheme.{u}) (A H : GroupScheme S),
    GroupScheme.IsAbelian A →
    LocallyOfFinitePresentation H.X.hom →
    QuasiCompact H.X.hom →
    QuasiSeparated H.X.hom →
    ∀ (f : A.X ⟶ H.X), η[A.X] ≫ f = η[H.X] → IsMonHom f

end Langlands.AbelianScheme

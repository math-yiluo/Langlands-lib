import Langlands.AbelianScheme.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # Pointed-morphism rigidity over an arbitrary field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

/-- Over the spectrum of any field, a morphism from a geometrically abelian group scheme
to a group scheme of finite presentation is a homomorphism if it preserves the unit. -/
def FieldPointedMorphismRigidity : Prop :=
  ∀ (K : Type u) [Field K] (A H : GroupScheme (Spec (CommRingCat.of K))),
    GroupScheme.IsAbelian A →
    LocallyOfFinitePresentation H.X.hom →
    QuasiCompact H.X.hom →
    QuasiSeparated H.X.hom →
    ∀ (f : A.X ⟶ H.X), η[A.X] ≫ f = η[H.X] → IsMonHom f

end Langlands.AbelianScheme

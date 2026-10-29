import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

/-! # Descent of compatible global units -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- A global unit that has equal pullbacks along every equal-composite pair
of maps descends uniquely along a quasi-compact flat surjection. -/
def CompatibleUnitsDescentStatement : Prop :=
  ∀ (X Y : AlgebraicGeometry.Scheme.{u}) (p : X ⟶ Y),
    QuasiCompact p → Flat p → Surjective p →
      ∀ (s : Γ(X, ⊤)ˣ),
        (∀ (U : AlgebraicGeometry.Scheme.{u}) (a b : U ⟶ X), a ≫ p = b ≫ p →
          Units.map a.appTop.hom.toMonoidHom s = Units.map b.appTop.hom.toMonoidHom s) →
        ∃! t : Γ(Y, ⊤)ˣ, Units.map p.appTop.hom.toMonoidHom t = s

end Langlands.Scheme

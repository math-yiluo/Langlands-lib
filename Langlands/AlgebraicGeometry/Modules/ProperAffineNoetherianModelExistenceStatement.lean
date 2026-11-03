import Langlands.AlgebraicGeometry.Modules.ProperNoetherianModel

/-! # Noetherian approximation for a proper scheme with two modules -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- A proper finitely presented scheme over an arbitrary affine base, together
with two finitely presented modules and target relative flatness, descends to
an actual noetherian model preserving all these properties. -/
def ProperAffineNoetherianModelExistenceStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (Y : Scheme.{u}) (p : Y ⟶ Spec R),
    IsProper p → LocallyOfFinitePresentation p →
      ∀ (M N : Y.Modules),
        M.IsFinitePresentation → N.IsFinitePresentation →
          IsFlatOver p N → HasAffineNoetherianModel p M N

end Langlands.AlgebraicGeometry.Modules

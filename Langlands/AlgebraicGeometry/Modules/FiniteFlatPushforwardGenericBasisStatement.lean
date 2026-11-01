import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Generic free charts with the native finite-flat rank -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- The actual structure-module pushforward is free on a nonempty affine
open, with basis size given by the native rank at any specified point. -/
def FiniteFlatPushforwardGenericBasisStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → Flat f →
    IsIntegral Y → IsLocallyNoetherian Y → ∀ x : Y,
      ∃ U : Y.affineOpens, Set.Nonempty (U.1 : Set Y) ∧
        Nonempty (((Scheme.Modules.pushforward f).obj
            (Langlands.Scheme.Modules.structureSheaf X)).restrict U.1.ι ≅
          SheafOfModules.free (R := U.1.toScheme.ringCatSheaf)
            (ULift.{u} (Fin (f.finrank x))))

end Langlands.AlgebraicGeometry.Modules

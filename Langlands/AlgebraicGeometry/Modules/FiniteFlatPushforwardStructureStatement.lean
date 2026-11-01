import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Actual finite-flat pushforward of the structure module -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

/-- The actual finite-flat structure-module pushforward is quasi-coherent,
with finite flat affine sections whose rank is the native rank. -/
def FiniteFlatPushforwardStructureStatement : Prop :=
  ∀ (X Y : Scheme.{u}) (f : X ⟶ Y), IsFinite f → Flat f →
    let P := (Scheme.Modules.pushforward f).obj (Langlands.Scheme.Modules.structureSheaf X)
    P.IsQuasicoherent ∧
      (∀ U : Y.affineOpens,
        Module.Finite Γ(Y, U.1) Γ(P, U.1) ∧ Module.Flat Γ(Y, U.1) Γ(P, U.1)) ∧
      (IsIntegral Y → ∀ (U : Y.affineOpens) (x : Y), x ∈ U.1 →
        Module.finrank Γ(Y, U.1) Γ(P, U.1) = f.finrank x)

end Langlands.AlgebraicGeometry.Modules

import Langlands.AlgebraicGeometry.Picard.MumfordBundle

/-! # The geometric Picard-zero condition for the Mumford family -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

/-- The theorem-of-the-square consequence needed to classify the actual
Mumford family: each geometric fibre is invariant under every translation. -/
def MumfordBundlePicardZeroStatement : Prop :=
  ∀ (preservation : pullbackTensorComparisonIsIsoStatement.{u})
    (S : Scheme.{u}) (A : AbelianScheme S)
    (L : RigidifiedLineBundle (unitSection A))
    (M : LineBundle A.X.left)
    (evaluation : tensorObj L.obj.carrier M.obj ≅ structureSheaf A.X.left),
    IsPicardZeroFamily A (mumfordBundle A preservation L M evaluation)

end Langlands.AbelianScheme

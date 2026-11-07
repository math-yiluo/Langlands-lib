import Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianQuasiAffineSourceAFStatement

/-! # Reduction of quasi-affine-source AF representability to Noetherian sources

Noetherian approximation reduces `FiniteSurjectiveQuasiAffineSourceAFStatement` to its case with
a Noetherian source, `NoetherianQuasiAffineSourceAFStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The Noetherian-source case of AF representability from a finite surjection with
quasi-affine source, over all base schemes, implies the general case over `Spec R`. -/
def QuasiAffineSourceAFApproximationStatement : Prop :=
  NoetherianQuasiAffineSourceAFStatement.{u} → FiniteSurjectiveQuasiAffineSourceAFStatement.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace

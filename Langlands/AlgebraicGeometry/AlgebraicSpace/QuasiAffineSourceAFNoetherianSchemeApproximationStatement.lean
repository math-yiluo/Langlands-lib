import Langlands.AlgebraicGeometry.AlgebraicSpace.NoetherianSchemeQuasiAffineSourceAFStatement

/-! # Reduction of quasi-affine-source AF representability to Noetherian scheme sources

Noetherian approximation reduces `FiniteSurjectiveQuasiAffineSourceAFStatement` to its case with
a Noetherian scheme as source, `NoetherianSchemeQuasiAffineSourceAFStatement`.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- The Noetherian-scheme-source case of AF representability from a finite surjection with
quasi-affine source, over all base schemes, implies the general case over `Spec R`. -/
def QuasiAffineSourceAFNoetherianSchemeApproximationStatement : Prop :=
  NoetherianSchemeQuasiAffineSourceAFStatement.{u} →
    FiniteSurjectiveQuasiAffineSourceAFStatement.{u}

end Langlands.AlgebraicGeometry.AlgebraicSpace

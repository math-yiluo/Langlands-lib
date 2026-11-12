import Langlands.AlgebraicGeometry.QuasiAffineApproximation.Presentation
import Langlands.AlgebraicGeometry.QuasiAffineApproximation.Approximation
import Langlands.AlgebraicGeometry.QuasiAffineApproximation.QuotientSpace

/-! # Reduction of quasi-affine-source AF representability to Noetherian scheme sources

Gross, Proposition 3.5, Step 3: Noetherian approximation of the finite quasi-affine cover,
assembled from the three parts of `QuasiAffineApproximation`.
-/

universe u

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open QuasiAffineApproximation

/-- The Noetherian-scheme-source case of AF representability from a finite surjection with
quasi-affine source implies the general case over `Spec R`. -/
theorem quasiAffineSourceAFNoetherianSchemeApproximation :
    QuasiAffineSourceAFNoetherianSchemeApproximationStatement.{u} :=
  approximation_of_interfaces presentationInterface approximationInterface quotientInterface

end Langlands.AlgebraicGeometry.AlgebraicSpace

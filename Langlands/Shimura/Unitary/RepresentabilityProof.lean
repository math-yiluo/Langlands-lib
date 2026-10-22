import Langlands.Shimura.Unitary.RepresentabilityStatement
import Langlands.Shimura.Unitary.SimilitudeCoordinates

/-! # Affine representability of the rational similitude functor

A chosen rational basis of the finite-dimensional algebra gives the finitely
presented coordinate ring of `SimilitudeCoordinates`, which corepresents the
similitude functor.
-/

universe u

namespace Langlands.Shimura

/-- The rational similitude functor of every finite-dimensional rational
algebra with involution is corepresented by a finitely presented algebra. -/
theorem similitudeRepresentability : SimilitudeRepresentabilityStatement.{u} := by
  intro A _ _ _ σ
  let b := Module.Free.chooseBasis ℚ A
  exact ⟨σ.similitudeCoordinateAlgebra b, inferInstance, ⟨σ.similitudeCoyonedaIso b⟩⟩

end Langlands.Shimura

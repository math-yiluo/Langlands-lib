import Langlands.GroupScheme.SpanningLineStabilizerStatement
import Langlands.GroupScheme.MatrixRepresentation.SpanningOrbitCoordinates

/-! # Proof of the spanning representation reduction preserving a line stabilizer -/

universe u

namespace Langlands.GroupScheme

/-- Every coordinate line of a finite representation of a smooth affine group over an
algebraically closed field has the same all-test unit-scalar stabilizer as a coordinate line of a
finite representation in which the rational orbit of the distinguished vector spans. -/
theorem spanningLineStabilizer : SpanningLineStabilizerStatement.{u} := by
  intro k _ _ G _ _ n j ρ
  obtain ⟨d, s, σ, hsame, hspan⟩ :=
    MatrixRepresentation.exists_spanning_sameCoordinateLineStabilizer ρ j
  exact ⟨d, s, σ, hsame, hspan⟩

end Langlands.GroupScheme

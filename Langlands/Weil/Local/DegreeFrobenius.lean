import Langlands.Weil.Local.Assembly

namespace Langlands.Weil.Local

universe uF

variable {p : ℕ} [Fact p.Prime]

theorem localDegreeInt_localGeometricFrobenius (F : PadicField.{uF} p) :
    localDegreeInt F (localGeometricFrobenius F) = 1 := by
  change (localDegree F (localGeometricFrobenius F)).toAdd = 1
  rw [localGeometricFrobenius_degree]
  rfl

end Langlands.Weil.Local

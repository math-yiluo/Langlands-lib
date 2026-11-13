import Langlands.VirtualRepresentation.Weil.Local
import Langlands.VirtualRepresentation.Supercuspidal.Basic

/-! # Degrees of unitary Weil and supercuspidal generators -/

noncomputable section

namespace Langlands.VirtualRepresentation

universe uK uW uV

variable {p : ℕ} [Fact p.Prime] (K : PadicField.{uK} p)

/-- The degree of a unitary Weil generator is its rank. -/
theorem _root_.Langlands.VirtualRepresentation.LocalWeil.unitaryDegree_generator
    (b : LocalWeil.UnitaryBasis.{uK, uW} K) :
    LocalWeil.unitaryDegree K (generator b) = ((b.val.1 : ℕ) : ℤ) := by
  simp [LocalWeil.unitaryDegree, VirtualRepresentation.Weil.unitaryDegree,
    VirtualRepresentation.Weil.degree, rankedDegree,
    VirtualRepresentation.Weil.includeUnitary, includeSubset, VirtualRepresentation.map,
    generator, degree, extend]

/-- The degree of a unitary supercuspidal generator is its rank. -/
theorem _root_.Langlands.VirtualRepresentation.PadicSupercuspidal.unitaryDegree_generator
    (b : PadicSupercuspidal.UnitaryBasis.{uK, uV} K) :
    PadicSupercuspidal.unitaryDegree K (generator b) = ((b.val.1 : ℕ) : ℤ) := by
  simp [PadicSupercuspidal.unitaryDegree, PadicSupercuspidal.degree,
    PadicSupercuspidal.includeUnitary, Supercuspidal.degree, rankedDegree,
    Supercuspidal.includeUnitary, includeSubset, VirtualRepresentation.map, generator,
    degree, extend]

end Langlands.VirtualRepresentation

import Langlands.Representation.Unramified.OrderedSphericalDualEmbedding
import Langlands.Representation.Category.SphericalDualQuotient

/-! Actual spherical irreducible quotients of ordered unramified principal series. -/

noncomputable section

namespace Langlands.Unramified

open Correspondence Classification

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sphericalQuotientFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance sphericalQuotientGLTopology (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n
local instance sphericalQuotientGLGroup (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- A Langlands-ordered actual unramified principal series has an actual
irreducible spherical quotient, including at repeated parameters. -/
theorem exists_spherical_irreducible_quotient
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    ∃ Q : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) F.Carrier),
      IsIrreducibleQuotient (principalSeriesOfTuple F z) Q.representation ∧
      fixedVectors Q.representation (sphericalSubgroup F r) ≠ ⊥ := by
  obtain ⟨B, hB, ⟨hBi, j, hj⟩, hBK⟩ :=
    exists_spherical_irreducible_subrepresentation_smoothDual F z hz
  let A := SmoothRep.of (principalSeriesOfTuple F z) (SphericalExistence.principalSeriesOfTuple_isAdmissible F z).1
  have hq := SmoothRep.isIrreducibleSphericalQuotient_of_dual_embedding
    (GeneralLinear.compactOpen_cofinal F F.canonicalTopologicalData (r + 1)) A B
    (SphericalExistence.principalSeriesOfTuple_isAdmissible F z) hB hBi
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) hBK j hj
  exact ⟨B.contragredient, hq⟩

/-- A chosen actual irreducible spherical quotient of a Langlands-ordered
unramified principal series, with its actual surjective intertwiner. -/
def sphericalQuotientDatum
    {r : ℕ} (z : Fin (r + 1) → ℂˣ)
    (hz : Monotone (fun i => ‖(z i : ℂ)‖)) :
    { Q : SmoothRep.{0, uF, uF} ℂ (GeneralLinear (r + 1) F.Carrier) //
      IsIrreducibleQuotient (principalSeriesOfTuple F z) Q.representation ∧
      fixedVectors Q.representation (sphericalSubgroup F r) ≠ ⊥ } :=
  Classical.indefiniteDescription _ (exists_spherical_irreducible_quotient F z hz)

end Langlands.Unramified

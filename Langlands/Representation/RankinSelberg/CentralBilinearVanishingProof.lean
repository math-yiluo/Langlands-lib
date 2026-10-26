import Langlands.Representation.RankinSelberg.CentralBilinearVanishingStatement
import Langlands.Representation.RankinSelberg.CentralSpectralElement
import Langlands.Representation.Smooth.IntertwinerFiniteness
import Langlands.LinearAlgebra.BilinearSpectralSupport

/-! Finite spectral support of determinant-twisted bilinear forms. -/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Twisted bilinear forms have one finite spectral exceptional set. -/
theorem centralBilinearVanishing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    CentralBilinearVanishingStatement.{uF,uV,uW} F T n := by
  let := T.topology
  intro V _ _ W _ _ ρ σ hρ hρfin hσ hσfin
  let z := centralSpectralElement T (n + 1)
  have hz : z ∈ Submonoid.center (Langlands.GeneralLinear (n + 1) F.Carrier) :=
    centralSpectralElement_mem_center T (n + 1)
  obtain ⟨E, hE⟩ := exists_finite_bilinear_power_spectral_support
    (ρ z) (σ z)
    (isIntegral_centralAction_of_admissible_finiteType ρ hρ hρfin z hz)
    (isIntegral_centralAction_of_admissible_finiteType σ hσ hσfin z hz)
    (n + 1) (Nat.succ_pos n)
  refine ⟨E, ?_⟩
  intro s hs β hβ
  apply hE (spectralPoint T.residueCardinality s) hs β
  intro v w
  simpa only [z, determinantWeight_centralSpectralElement] using hβ z v w

end Langlands.RankinSelberg

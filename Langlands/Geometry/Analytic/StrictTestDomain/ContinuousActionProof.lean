import Langlands.Geometry.Analytic.StrictTestDomain.ContinuousActionStatement
import Langlands.Geometry.Analytic.Spectrum.JointContinuityProof

/-! # Joint continuity of the inverse-pullback spectrum action -/

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Continuous forward algebra orbits give continuous inverse algebra orbits. -/
theorem continuous_inv_apply (ρ : G →* Aut P)
    (hρ : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) (a : P) :
    Continuous (fun g : G => (ρ g).inv.toAlgHom a) := by
  apply ((hρ a).comp continuous_inv).congr
  intro g
  change (ρ (g⁻¹)).hom.toAlgHom a = (ρ g).inv.toAlgHom a
  rw [map_inv]
  rfl

/-- Pointwise norm-continuity on the algebra implies joint continuity of the
existing inverse-pullback action on its bounded spectrum. -/
theorem continuous_spectrumAction (ρ : G →* Aut P)
    (hρ : ∀ a : P, Continuous (fun g : G => (ρ g).hom.toAlgHom a)) :
    Continuous (fun p : G × BanachSpectrum P => (ρ p.1) • p.2) := by
  exact BanachSpectrum.continuous_comap_of_continuous_apply
    (fun g : G => (ρ g).inv.toBoundedRingHom) (continuous_inv_apply ρ hρ)

/-- The exact published strict-affinoid continuity target, with independent
field and group universes and no additional hypotheses. -/
theorem pointwiseContinuousSpectrumAction :
    PointwiseContinuousSpectrumActionStatement.{u, v} := by
  intro K _ _ P G _ _ _ ρ hρ
  exact continuous_spectrumAction ρ hρ

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism

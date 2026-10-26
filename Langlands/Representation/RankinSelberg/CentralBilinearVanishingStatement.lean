import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Finite spectral support of twisted bilinear forms

This proposition defines an internal central-polynomial formulation of the
residual bilinear obstruction in JPSS Section 2.10, printed page 398.
It is a statement, not a proof.
-/

namespace Langlands.RankinSelberg

universe uF uV uW

/-- Outside one finite set of spectral values, every determinant-twisted
bilinear form on two admissible finite-type representations of positive-rank
GL vanishes. The exceptional set is chosen before the parameter and form. -/
def CentralBilinearVanishingStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
  ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
  ∀ (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    IsAdmissible ρ →
    Module.Finite (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
      ρ.asModule →
    IsAdmissible σ →
    Module.Finite (MonoidAlgebra ℂ (Langlands.GeneralLinear (n + 1) F.Carrier))
      σ.asModule →
    ∃ E : Finset ℂ, ∀ s : ℂ, spectralPoint T.residueCardinality s ∉ E →
      ∀ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ,
        (∀ g v w, β (ρ g v) (σ g w) =
          determinantWeight (normalizedAbsoluteValue T) g (-s) * β v w) →
        β = 0

end Langlands.RankinSelberg

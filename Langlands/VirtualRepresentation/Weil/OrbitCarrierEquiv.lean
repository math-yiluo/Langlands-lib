import Langlands.VirtualRepresentation.Weil.Twist
import Langlands.Weil.Representation.ContinuousIrreducibleCarrierEquiv

/-!
# Changing the carrier universe of unramified-twist orbits

The coordinate-model equivalence on continuous irreducible classes
commutes with character twists and descends to the orbit quotient.
-/

noncomputable section

set_option autoImplicit false

universe uG uV uW

namespace Langlands.VirtualRepresentation.Weil

open FiniteRepresentation

variable {G : Type uG} [Group G] [TopologicalSpace G]

private def basisCarrierEquiv : IrreducibleBasis.{uG, uV} G ≃ IrreducibleBasis.{uG, uW} G :=
  Equiv.sigmaCongrRight fun n => continuousIrreducibleCarrierEquiv G (n : ℕ)

private theorem basisCarrierEquiv_twist (χ : G →ₜ* ℂˣ) (b : IrreducibleBasis.{uG, uV} G) :
    basisCarrierEquiv.{uG, uV, uW} (twistBasisEquiv χ b) =
      twistBasisEquiv χ (basisCarrierEquiv b) := by
  obtain ⟨n, c⟩ := b
  exact congrArg (Sigma.mk n) (continuousIrreducibleCarrierEquiv_twist χ c)

/-- Change the carrier universe of the unramified-twist orbits of continuous
irreducible classes for one topological group and degree map. -/
def unramifiedOrbitCarrierEquiv (d : G →ₜ* Langlands.Weil.Degree) :
    UnramifiedOrbitClasses.{uG, uV} d ≃ UnramifiedOrbitClasses.{uG, uW} d := by
  apply Quotient.congr basisCarrierEquiv
  intro a b
  simp only [← Quotient.eq]
  change unramifiedOrbitClass d a = unramifiedOrbitClass d b ↔
    unramifiedOrbitClass d (basisCarrierEquiv a) = unramifiedOrbitClass d (basisCarrierEquiv b)
  simp only [unramifiedOrbitClass_eq_iff, ← basisCarrierEquiv_twist, Equiv.apply_eq_iff_eq]

@[simp]
theorem unramifiedOrbitCarrierEquiv_class (d : G →ₜ* Langlands.Weil.Degree)
    (n : ℕ+) (σ : ContinuousIrreducibleClasses.{uG, uV} G (n : ℕ)) :
    unramifiedOrbitCarrierEquiv.{uG, uV, uW} d (unramifiedOrbitClass d ⟨n, σ⟩) =
      unramifiedOrbitClass d ⟨n, continuousIrreducibleCarrierEquiv G (n : ℕ) σ⟩ :=
  rfl

end Langlands.VirtualRepresentation.Weil

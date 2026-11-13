import Langlands.Representation.Derivative.MirabolicMinusIrreducibleStatement
import Langlands.AllField.Representation.Derivative.MirabolicMinus
/-!
# Irreducibility of unnormalized `Φ⁻`

The unnormalized Bernstein–Zelevinsky functor `Φ⁻ : P_(m+2) → P_(m+1)` sends an
irreducible smooth representation to an irreducible representation or to zero.
-/

noncomputable section

namespace Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative.Mirabolic hiding PhiMinusIrreducibleStatement phiMinusQuotient phiMinusQuotient_radical phiMinusQuotient_surjective phiMinusUnnormalized phiMinusUnnormalized_action
open Langlands.AllField.Derivative.Mirabolic
open Langlands.Derivative
open Langlands.AllField.Derivative

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis

universe uF uV

/-- For an irreducible smooth representation `ξ` of `mirabolic (m + 1) F`, every
subrepresentation of the unnormalized `Φ⁻ ξ` is `⊥` or `⊤`: the representation
`Φ⁻ ξ` of `mirabolic m F` is irreducible or zero. -/
def PhiMinusIrreducibleStatement 
    (F : Type uF) [Field F] (T : LocalFieldData F) (m : ℕ) : Prop :=
  letI := T.topology
  ∀ ψ : UnitaryAdditiveCharacter F,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ξ : Representation ℂ (mirabolic (m + 1) F) V) (hs : IsSmooth ξ),
      ξ.IsIrreducible →
        ∀ σ : Subrepresentation ((phiMinusUnnormalized T ψ m).obj
          (SmoothRep.of ξ hs)).representation, σ = ⊥ ∨ σ = ⊤

end Langlands.AllField.Derivative.Mirabolic

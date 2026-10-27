import Langlands.Representation.Derivative.MirabolicMinus

/-!
# Irreducibility of unnormalized `Φ⁻`

The unnormalized Bernstein–Zelevinsky functor `Φ⁻ : P_(m+2) → P_(m+1)` sends an
irreducible smooth representation to an irreducible representation or to zero.
-/

noncomputable section

namespace Langlands.Derivative.Mirabolic

open GeneralLinear HarmonicAnalysis

universe uF uV

/-- For an irreducible smooth representation `ξ` of `mirabolic (m + 1) F`, every
subrepresentation of the unnormalized `Φ⁻ ξ` is `⊥` or `⊤`: the representation
`Φ⁻ ξ` of `mirabolic m F` is irreducible or zero. -/
def PhiMinusIrreducibleStatement {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (m : ℕ) : Prop :=
  letI := T.topology
  ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ξ : Representation ℂ (mirabolic (m + 1) F.Carrier) V) (hs : IsSmooth ξ),
      ξ.IsIrreducible →
        ∀ σ : Subrepresentation ((phiMinusUnnormalized T ψ m).obj
          (SmoothRep.of ξ hs)).representation, σ = ⊥ ∨ σ = ⊤

end Langlands.Derivative.Mirabolic

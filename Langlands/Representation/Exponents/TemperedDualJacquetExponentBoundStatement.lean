import Langlands.Representation.Exponents.DualJacquet
import Langlands.Representation.Classification.Tempered

/-!
# Weak bounds for opposite Jacquet dual exponents of tempered representations

The proposition definition states the necessity half of the exponent
criterion for temperedness on `GL_n`, read through dual eigenfunctionals on
normalized opposite Jacquet quotients. It states the bound; it does not prove it.
-/

namespace Langlands

universe uF uV

/-- Every opposite Jacquet dual exponent of an irreducible tempered
representation of `GL_n` has absolute value at most one on block scalars whose
normalized absolute values decrease along the blocks. -/
def GLTemperedDualJacquetExponentBoundStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (C : GeneralLinear.BlockShape n)
      (A : Rep.{uV} ℂ (GeneralLinear n F.Carrier)),
      Representation.IsIrreducible A.ρ → T.IsTempered A.ρ →
        ∀ ψ : (Fin C.length → F.Carrierˣ) →* ℂˣ, T.IsDualJacquetExponent C A ψ →
          ∀ a : Fin C.length → F.Carrierˣ,
            Antitone (fun i => T.normalizedAbs (a i : F.Carrier)) →
            ‖(ψ a : ℂ)‖ ≤ 1

end Langlands

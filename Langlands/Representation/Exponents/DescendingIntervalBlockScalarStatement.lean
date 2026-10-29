import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.LocalField.Normalization.Definitions
import Langlands.Representation.Classification.ConstituentRelations
import Langlands.Representation.Classification.SupercuspidalTwist
import Langlands.Representation.Induction.BlockFactors

/-! # Descending interval characters on the actual block tensor -/

namespace Langlands

open scoped BigOperators

universe uF uV

/-- The split-centre scalar action and norm for arbitrary descending intervals.
Block `i` receives the interval of length `k i` that starts after the natural
prefix `K i`, with determinant exponents `m - 1 - (K i + j)` for `j < k i`.
This concerns the actual tensor and characters, not a Jacquet identification. -/
def DescendingIntervalBlockScalarFormula {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  ∀ (n : ℕ) (B : GeneralLinear.BlockShape n)
    (V : Fin B.length → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i))
    (ω : F.Carrierˣ →* ℂˣ) (r m : ℕ) (k : Fin B.length → ℕ),
    (∑ i, k i) = m →
    let K : Fin B.length → ℕ := fun i => ∑ j : Fin B.length with j < i, k j
    let c : Fin B.length → (F.Carrierˣ →* ℂˣ) := fun i =>
      ∏ j : Fin (k i), ω * (T.determinantPowerCharacter r
        ((m - 1 - (K i + (j : ℕ)) : ℕ) : ℝ)).comp GeneralLinear.scalar
    let cB : (Fin B.length → F.Carrierˣ) →* ℂˣ :=
      ∏ i, (c i).comp (Pi.evalMonoidHom (fun _ : Fin B.length => F.Carrierˣ) i)
    (∀ i, Classification.HasScalarCharacter (σ i) GeneralLinear.scalar (c i)) →
    Classification.HasScalarCharacter (B.blockTensor σ) (B.blockScalarLevi F.Carrier) cB ∧
    ∀ a : Fin B.length → F.Carrierˣ,
      ‖(cB a : ℂ)‖ =
        ∏ i, (‖(ω (a i) : ℂ)‖ ^ k i *
          T.normalizedAbs (a i : F.Carrier) ^
            ((r : ℝ) * (k i : ℝ) *
              (((2 * (m : ℝ) - (k i : ℝ) - 1) / 2) - (K i : ℝ))))

end Langlands

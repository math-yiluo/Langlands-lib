import Langlands.Group.GL.BlockIwahoriDefinitions
import Langlands.Group.GL.BlockModulus
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-!
# Strict L2 decay for one exactly extracted normalized coefficient

The concrete deep-chamber coefficient identity and square-integrability of its
descended norm force strict decay on every nonconstant closed chamber direction.
-/

namespace Langlands

universe uF uV

/-- A smooth coefficient equal to the positive half modulus times one smooth
character throughout a deep block-scalar chamber can have a square-integrable
descended norm only if that character strictly decays on every nonconstant
direction of the closed negative chamber. -/
def GLExtractedCoefficientL2ObstructionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      letI := T.topology
      IsSmooth ρ →
      ∀ (c : UnitaryCentralCharacter ρ)
        [MeasurableSpace (GeneralLinear n F.Carrier ⧸
          Subgroup.center (GeneralLinear n F.Carrier))]
        [BorelSpace (GeneralLinear n F.Carrier ⧸
          Subgroup.center (GeneralLinear n F.Carrier))]
        (μ : MeasureTheory.Measure (GeneralLinear n F.Carrier ⧸
          Subgroup.center (GeneralLinear n F.Carrier))) [μ.IsHaarMeasure]
        (B : GeneralLinear.BlockShape n)
        (χ : (Fin B.length → F.Carrierˣ) →* ℂˣ),
        IsOpen (χ.ker : Set (Fin B.length → F.Carrierˣ)) →
        ∀ (v : V) (ℓ : SmoothDual ρ) (ε : ℝ), 0 < ε → ε ≤ 1 →
          (∀ b : Fin B.length → F.Carrierˣ,
            (∀ i j : Fin B.length, i < j →
              T.normalizedAbs ((b i : F.Carrier) / (b j : F.Carrier)) < ε) →
            ℓ.1 (ρ (B.leviEmbedding F.Carrier (B.blockScalarLevi F.Carrier b)) v) =
              (T.leviHalfModulus B (B.blockScalarLevi F.Carrier b) : ℂ) * (χ b : ℂ)) →
          MeasureTheory.MemLp (c.coefficientNorm ℓ.1 v) 2 μ →
          ∀ a : Fin B.length → F.Carrierˣ,
            Monotone (fun i => T.normalizedAbs (a i : F.Carrier)) →
            (∃ i j, T.normalizedAbs (a i : F.Carrier) ≠
              T.normalizedAbs (a j : F.Carrier)) →
            ‖(χ a : ℂ)‖ < 1

end Langlands

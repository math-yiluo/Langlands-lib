import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.Unitary.Basic

/-!
# Unitarizability of normalized parabolic induction

These are closed statement targets for actual normalized upper parabolic
induction and actual invariant positive Hermitian forms. The product target
uses the published external tensor and induction functors. No preservation
result is proved here.
-/

namespace Langlands

universe uF uV

/-- Normalized induction preserves unitarizability of every smooth actual
representation of the standard block Levi, with its supplied product topology. -/
def GLNormalizedParabolicInductionUnitarityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopology B
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (B.Levi F.Carrier) V),
        IsSmooth σ → IsUnitarizable σ →
          IsUnitarizable (T.normalizedParabolicInduced B σ)

/-- The actual normalized product induction of smooth unitarizable blocks is
unitarizable. Block carriers lie in `Type (max uF uV)`. -/
def GLNormalizedProductInductionUnitarityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      ∀ σ : ∀ i, SmoothRep.{0, uF, max uF uV} ℂ
        (GeneralLinear (B.size i) F.Carrier),
        (∀ i, IsUnitarizable (σ i).representation) →
          IsUnitarizable (((T.normalizedProductInductionFunctor B).obj σ).representation)

/-- Both preservation statements, with independent field and carrier universes. -/
def GLNormalizedInductionUnitarityStatement : Prop :=
  GLNormalizedParabolicInductionUnitarityStatement.{uF, uV} ∧
    GLNormalizedProductInductionUnitarityStatement.{uF, uV}

end Langlands

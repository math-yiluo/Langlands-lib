import Langlands.LocalFactor.NonabelianSystem

/-!
# Induction of local constants in arbitrary degree (Tate 1979, 3.4.8)

Statement only; no proof is claimed. A local-constant system in the sense of
`Langlands.LocalFactor.NonabelianSystem.IsSystem` is inductive in degree zero
with the trace characters `ψ ∘ Tr_{L/E}` (Tate 3.4.1, 3.4.8). In arbitrary degree
the induced constant differs from the constant of the inducing representation by
the power `λ^{dim V}` of the correction factor
`λ = ε_E(Ind_{L/E} 1_L, ψ, μ_E) / ε_L(1_L, ψ ∘ Tr_{L/E}, μ_L)`.
-/

noncomputable section

namespace Langlands.LocalFactor.Inductive

universe uF uV

open LocalFactor.CommonClosure LocalFactor.NonabelianSystem VirtualRepresentation

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Tate 3.4.8 with the degree correction: for a local-constant system `ε`, nested
finite extensions `E ⊆ L` of `F`, an additive character `ψ` of `E`, Haar measures
`μ_E` on `E` and `μ_L` on `L`, and every virtual representation `x` of `W_L`,
`ε_E(Ind_{L/E} x, ψ, μ_E) = λ^{dim x} ε_L(x, ψ ∘ Tr_{L/E}, μ_L)` with
`λ = ε_E(Ind_{L/E} 1_L, ψ, μ_E) / ε_L(1_L, ψ ∘ Tr_{L/E}, μ_L)`. Here `[1_L]` is the
Library's character line of the trivial character of `W_L`. -/
def SystemInductionCorrectionStatement : Prop :=
  ∀ (e : ReciprocityFamily F) (ε : Assignment.{uF, uV} F), IsSystem F e ε →
    ∀ (E L : CommonClosure.Extension F) (h : E.field ≤ L.field)
      (ψ : AdditiveCharacter F E) (μ : HaarMeasure F E) (μL : HaarMeasure F L)
      (x : Virtual.{uF, uV} F L),
      let ψL := traceCharacter F E L h ψ
      let one : Virtual.{uF, uV} F L :=
        ExactGrothendieckGroup.characterClass (1 : weilSubgroup F L →ₜ* ℂˣ)
      let lam := ε E ψ μ (induce F E L h one) * (ε L ψL μL one)⁻¹
      ε E ψ μ (induce F E L h x) = lam ^ degree F L x * ε L ψL μL x

end Langlands.LocalFactor.Inductive

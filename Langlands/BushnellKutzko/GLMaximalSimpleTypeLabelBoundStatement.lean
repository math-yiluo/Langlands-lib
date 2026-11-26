import Langlands.BushnellKutzko.GLMaximalSimpleTypeSets
import Langlands.BushnellKutzko.Labels

/-! # Labels bounding the maximal simple type classes (BK94 (3.7)–(3.8)) -/

open ValuativeRel

namespace Langlands.BushnellKutzko

universe uF uρ

/-- In positive depth and at level zero, maximal simple type pairs admit
labels whose fibers lie in single `GL_N(F)`-conjugacy classes. In positive
depth the labels satisfy `e(p) = 1`. -/
def GLMaximalSimpleTypeLabelBoundStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (N : ℕ), 1 ≤ N →
    let qF := Nat.card 𝓀[F]
    (∀ (t m : ℕ), 1 ≤ t → t ∣ N → 1 ≤ m →
      let T := glMaximalSimpleTypesAt.{uF, uρ} N F t m
      ∃ L : T → extendedLabelSet m t (N / t) qF,
        (∀ x : T, (L x).1.1.e = 1) ∧
        (∀ x₁ x₂ : T, L x₁ = L x₂ →
          AreConjugatePairs x₁.1.2.representation x₂.1.2.representation)) ∧
    (let T₀ := glMaximalLevelZeroSimpleTypes.{uF, uρ} N F
     ∃ L₀ : T₀ → degenerateLabelSet N qF,
       ∀ x₁ x₂ : T₀, L₀ x₁ = L₀ x₂ →
         AreConjugatePairs x₁.1.2.representation x₂.1.2.representation)

end Langlands.BushnellKutzko

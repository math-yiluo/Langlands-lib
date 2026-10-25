import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement

/-! # Refined induction and coarse real-character twists

The character restriction, actual function equivalence, and specified quotient
transport are stated here. No proof is supplied in this module.
-/

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW

/-- Character restriction, normalized refined induction twist, and
transport of a specified fine-to-coarse surjection. No proof is supplied. -/
def RefinedLeviRealTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier))
      (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ),
      letI := T.leviTopologicalGroup B
      (∀ q : refinedParabolic F.Carrier B S,
        T.leviRealPowerCharacter B t q.val =
          T.leviRealPowerCharacter (B.flatten S)
            (fun k => t ((B.flattenBlockEquiv S).symm k).1)
            ((flattenedLeviEquiv F.Carrier B S).symm
              (refinedLeviProjection F.Carrier B S q))) ∧
      ∃ E : (T.leviRealPowerTwist B t
          (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ).Equiv
          (innerInduced T B S (fineTwist T B S ω v₀ t)).ρ,
        (∀ f (m : B.Levi F.Carrier),
          Induction.eval _ _ (E f) m =
            (T.leviRealPowerCharacter B t m : ℂ) • Induction.eval _ _ f m) ∧
        (∀ f (m : B.Levi F.Carrier),
          Induction.eval _ _ (E.symm f) m =
            ((T.leviRealPowerCharacter B t m)⁻¹ : ℂˣ) •
              Induction.eval _ _ f m) ∧
        ∀ (π : Rep.{uW} ℂ (B.Levi F.Carrier))
          (q₀ : (innerInduced T B S (fineTwist T B S ω v₀ 0)).ρ.IntertwiningMap π.ρ),
          Function.Surjective q₀ →
          ∃ qₜ : (innerInduced T B S (fineTwist T B S ω v₀ t)).ρ.IntertwiningMap
              (T.leviRealPowerTwist B t π.ρ),
            Function.Surjective qₜ ∧ ∀ f, qₜ f = q₀ (E.symm f)

end Langlands

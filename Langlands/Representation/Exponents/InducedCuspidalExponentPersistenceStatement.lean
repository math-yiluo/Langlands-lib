import Langlands.Representation.Exponents.RealTwistFamilies

/-!
# Persistence of cuspidal opposite-Jacquet exponents of real-twisted inductions

A statement only. For a coarse representation that is a quotient of a fine
cuspidal induction, every irreducible cuspidal opposite-Jacquet class exponent
of the real-twisted outer induction is an actual Weyl transport of the twisted
fine representation, and the same transport also occurs at the untwisted point.
-/

noncomputable section

namespace Langlands

open GeneralLinear Geometric RelativeJacquetMultiplicity

universe uF uV uW uM

/-- Let `π` be an irreducible quotient of the inner induction of the fine
cuspidal representation `ω` twisted by `-v`. If an irreducible cuspidal `τ`
occurs as an opposite-Jacquet class exponent along `E` of the outer induction
of `π` twisted by `t`, then one permutation `s` with one conjugacy witness `hs`
transports the fine twist by `nestedParameter B S v t` to a representation
equivalent to `τ`, and the same `s, hs` transport the fine twist by
`nestedParameter B S v 0 = -v` to an actual class exponent of the untwisted
outer induction of `π`. -/
def GLInducedCuspidalExponentPersistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B : BlockShape n) (S : BlockRefinement B)
      (ω : Rep.{uV} ℂ ((B.flatten S).Levi F.Carrier)),
      Representation.IsIrreducible ω.ρ →
      CuspidalSupport.IsLeviCuspidal (B.flatten S) ω.ρ →
      ∀ (v : Fin (B.flatten S).length → ℝ) (π : Rep.{uW} ℂ (B.Levi F.Carrier)),
        Representation.IsIrreducible π.ρ →
        (∃ q : (innerInduced T B S (fineTwist T B S ω v 0)).ρ.IntertwiningMap π.ρ,
          Function.Surjective q) →
        ∀ (t : Fin B.length → ℝ) (E : BlockShape n)
          (τ : Rep.{uM} ℂ (E.Levi F.Carrier)),
          CuspidalSupport.IsLeviCuspidal E τ.ρ →
          T.IsOppositeJacquetClassExponent E (RealTwistFamilies.induced T B π t) τ →
          ∃ (s : Equiv.Perm (Fin n))
            (hs : CuspidalSupport.ConjugatesLevi (F := F.Carrier) (B.flatten S) E s),
            Nonempty ((RealTwistFamilies.transported T B (B.flatten S) E s hs ω
                (RealTwistFamilies.nestedParameter B S v) t).ρ.Equiv τ.ρ) ∧
            RealTwistFamilies.Occurs T B (B.flatten S) E π s hs ω
              (RealTwistFamilies.nestedParameter B S v) 0

end Langlands

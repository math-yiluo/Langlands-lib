import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-! Standard Langlands data recovery for arbitrary whole-Levi inputs. -/

namespace Langlands

open GeneralLinear RelativeRegularComparison

universe uF uV uW uJ uK

/-- Equivalent irreducible quotients of regular positive standard inductions
recover the ordered shape, real parameter and untwisted whole-Levi input.
All four representation carrier universes are independent of the field. -/
def GLWholeLeviLanglandsRecoveryStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ (B C : BlockShape n)
      (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
      (τ : Rep.{uW} ℂ (C.Levi F.Carrier)),
      Representation.IsIrreducible σ.ρ → IsLeviTempered T B σ →
      Representation.IsIrreducible τ.ρ → IsLeviTempered T C τ →
      ∀ (t : Fin B.length → ℝ) (u : Fin C.length → ℝ),
        StrictAnti t → StrictAnti u →
        ∀ (J : Rep.{uJ} ℂ (GeneralLinear n F.Carrier))
          (K : Rep.{uK} ℂ (GeneralLinear n F.Carrier)),
          Representation.IsIrreducible J.ρ →
          Representation.IsIrreducible K.ρ →
          (∃ q : (T.normalizedParabolicInduced B
              (T.leviRealPowerTwist B t σ.ρ)).IntertwiningMap J.ρ,
            Function.Surjective q) →
          (∃ q : (T.normalizedParabolicInduced C
              (T.leviRealPowerTwist C u τ.ρ)).IntertwiningMap K.ρ,
            Function.Surjective q) →
          Nonempty (J.ρ.Equiv K.ρ) →
          ∃ h : B = C,
            let tC : Fin C.length → ℝ :=
              Eq.rec (motive := fun D _ => Fin D.length → ℝ) t h
            let σC : Rep.{uV} ℂ (C.Levi F.Carrier) :=
              Eq.rec (motive := fun D _ => Rep.{uV} ℂ (D.Levi F.Carrier)) σ h
            tC = u ∧ Nonempty (@Representation.Equiv ℂ (C.Levi F.Carrier)
              σC.V τ.V inferInstance inferInstance
              σC.hV1.toAddCommMonoid τ.hV1.toAddCommMonoid σC.hV2 τ.hV2 σC.ρ τ.ρ)

end Langlands

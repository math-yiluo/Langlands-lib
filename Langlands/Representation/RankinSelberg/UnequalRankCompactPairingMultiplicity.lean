import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingFunctionals
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Whittaker.MultiplicityOneStatement
import Langlands.LocalField.Normalization.Proof

/-!
# The unequal-rank compact generic pairing from Whittaker multiplicity one

Whittaker multiplicity one, stated in the Library for the canonical normed topology and
the standard character, gives multiplicity one for the inverse standard character under
any topology equal to the canonical one. Combined with the line criterion of
`UnequalRankCompactPairingFunctionals`, it gives the exact-dimension statement
`UnequalRankCompactGenericPairingStatement`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

namespace UnequalRankCompactPairing

/-- Whittaker multiplicity one, transported to the inverse standard character and to the
supplied topology of a p-adic field. -/
theorem inverseFunctionals_line_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W],
    ∀ η : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W,
      IsAdmissible η → Representation.IsIrreducible η →
      ∀ ℓ₁ ℓ₂ : Whittaker.functionals (GeneralLinear.upperUnipotent (n + 1) F.Carrier)
        (inverseStandardCharacter ψ n) η, ℓ₁.val ≠ 0 → ∃ c : ℂ, ℓ₂ = c • ℓ₁ := by
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  intro ψ W _ _ η hadm hirr ℓ₁ ℓ₂ h1
  have hχ := Langlands.RankinSelberg.standardCharacter_scale_neg_one ψ n
  have m₁ : ℓ₁.val ∈ glFunctionals (ψ.scale (-1)) n η := by
    rw [glFunctionals, hχ]
    exact ℓ₁.property
  have m₂ : ℓ₂.val ∈ glFunctionals (ψ.scale (-1)) n η := by
    rw [glFunctionals, hχ]
    exact ℓ₂.property
  obtain ⟨c, hc, -⟩ := hmult p inferInstance F n W (ψ.scale (-1)) η hadm hirr
    ⟨ℓ₁.val, m₁⟩ ⟨ℓ₂.val, m₂⟩ h1
  have hv : ℓ₂.val = c • ℓ₁.val := congrArg Subtype.val hc
  exact ⟨c, Subtype.ext hv⟩

/-- Whittaker multiplicity one implies the exact-dimension statement for the unequal-rank
compact generic pairing. -/
theorem unequalRankCompactGenericPairing_of_multiplicityOne
    (hmult : Whittaker.MultiplicityOneStatement.{uF, uW}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r := by
  intro hnr ψ W _ _ η hadm hirr hWh s
  exact nonempty_equiv_complex_padic F T n r hnr ψ W η hadm.1 hWh
    (inverseFunctionals_line_of_multiplicityOne hmult F T n ψ W η hadm hirr) s

end UnequalRankCompactPairing

end Langlands.RankinSelberg

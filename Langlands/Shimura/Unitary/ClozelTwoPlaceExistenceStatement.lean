import Langlands.Shimura.Unitary.FiniteModels

/-! # Clozel's prescribed two-split-place division-existence target -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- Unproved two-split-place option of Clozel 1991, Proposition 2.3(i),(iii),
with both exceptional places prescribed as allowed by the following remark. -/
def ClozelTwoPlaceExistenceStatement (n : ℕ)
    (v₀ v₁ : Langlands.Global.FinitePlace E) : Prop :=
  1 < n → v₀ ≠ v₁ →
  IsSplitPlace E K v₀ → IsSplitPlace E K v₁ →
  (∃ m : ℕ, n = 2 * m ∧ Odd m) → Odd (Module.finrank ℚ E) →
  ∃ (A : Type (max u v)) (ringA : Ring A),
    letI : Ring A := ringA
    ∃ algE : Algebra E A,
      letI : Algebra E A := algE
      ∃ algK : Algebra K A,
        letI : Algebra K A := algK
        ∃ tower : IsScalarTower E K A,
          letI : IsScalarTower E K A := tower
          ∃ D : CentralSimpleUnitaryData E K A n,
            D.IsDivision ∧ HasHarrisSignature D.toSecondKindInvolution n ∧
              IsDivisionAbove (K := K) (A := A) v₀ ∧
              IsDivisionAbove (K := K) (A := A) v₁ ∧
              ∀ v : Langlands.Global.FinitePlace E, v ≠ v₀ → v ≠ v₁ →
                IsQuasiSplitAt D.toSecondKindInvolution n v

end Langlands.Shimura.FiniteUnitary

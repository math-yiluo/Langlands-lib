import Langlands.Shimura.Unitary.FiniteModels

/-! # Clozel's prescribed one-split-place division-existence target -/

noncomputable section

universe u v

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global

variable (E : Type u) (K : Type v)
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K]
  [Algebra E K] [IsQuadraticExtension E K]

/-- Unproved arithmetic existence target from Clozel 1991, Proposition 2.3(i),(ii)
and the remark allowing the exceptional split place to be prescribed. -/
def ClozelOnePlaceExistenceStatement (n : ℕ) (v₀ : Langlands.Global.FinitePlace E) : Prop :=
  1 < n →
  IsSplitPlace E K v₀ →
  (Odd n ∨ 4 ∣ n ∨ (Even n ∧ Even (Module.finrank ℚ E))) →
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
              ∀ v : Langlands.Global.FinitePlace E, v ≠ v₀ →
                IsQuasiSplitAt D.toSecondKindInvolution n v

end Langlands.Shimura.FiniteUnitary

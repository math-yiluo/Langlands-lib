import Langlands.BushnellKutzko.GLSplitTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Jacquet nonvanishing from a split type of level `(x, y)` with `x > y > 0` -/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- **BK93 (8.2.5)(iv), case `x > y > 0`, nonvanishing.** An irreducible admissible smooth
representation containing a split type of level `(x, y)` with `x > y > 0` has a nonzero
proper Jacquet module. -/
def UnequalPositiveSplitTypeJacquetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)),
      π.IsIrreducible → IsAdmissible π.representation →
    ∀ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K) (x y : ℚ),
      IsUnequalPositiveSplitType (V := Fin n → F) ψF x y (glRepresentationToAut ρ) →
      ContainsType π ρ →
      ∃ B : GeneralLinear.BlockShape n, B.parabolic F ≠ ⊤ ∧
        ∃ g : GeneralLinear n F,
          ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g))

end Langlands.BushnellKutzko

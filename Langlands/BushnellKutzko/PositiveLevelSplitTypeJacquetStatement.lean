import Langlands.BushnellKutzko.GLSplitTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Jacquet nonvanishing from a split type of positive level -/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- **BK93 (8.2.5)(iv), nonvanishing.** An irreducible admissible smooth representation
containing a split type with positive second level has a nonzero proper Jacquet module. -/
def PositiveLevelSplitTypeJacquetStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)),
      π.IsIrreducible → IsAdmissible π.representation →
    ∀ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K),
      IsGLPositiveLevelSplitType (n := n) ψF ρ → ContainsType π ρ →
      ∃ B : GeneralLinear.BlockShape n, B.parabolic F ≠ ⊤ ∧
        ∃ g : GeneralLinear n F,
          ¬ Subsingleton (Jacquet.Coinvariants π.representation (B.conjugateUnipotent g))

end Langlands.BushnellKutzko

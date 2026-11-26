import Langlands.BushnellKutzko.GLSplitTypes
import Langlands.BushnellKutzko.TypeContainment

/-! # A representation containing no simple type contains a split type -/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- **BK93 (8.1.5).** An irreducible smooth representation of `GL_n(F)` with no simple
type contains a split type, for the same choice of additive character. -/
def SplitTypeExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)), π.IsIrreducible →
    (¬ ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K),
      IsGLSimpleType (n := n) ψF ρ ∧ ContainsType π ρ) →
    ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K),
      IsGLSplitType (n := n) ψF ρ ∧ ContainsType π ρ

end Langlands.BushnellKutzko

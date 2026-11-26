import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Every irreducible supercuspidal representation contains a simple type -/

namespace Langlands.BushnellKutzko

universe uF uπ uρ

/-- **BK93 (8.4.1), existence.** Every irreducible supercuspidal representation of
`GL_n(F)` contains a simple type. -/
def SupercuspidalSimpleTypeExistenceStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ), IsBKAdditiveCharacter ψF →
    ∀ (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)),
      GeneralLinear.supercuspidalProperty π →
      ∃ (K : Subgroup (GeneralLinear n F)) (ρ : SmoothRep.{0, uF, uρ} ℂ K),
        IsGLSimpleType (n := n) ψF ρ ∧ ContainsType π ρ

end Langlands.BushnellKutzko

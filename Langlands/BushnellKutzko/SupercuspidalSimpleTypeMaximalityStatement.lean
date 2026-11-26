import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.Representation.Classification.Supercuspidal

/-! # Maximality of a simple type occurring in a supercuspidal representation -/

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **BK93 (6.2.1).** If a supercuspidal representation contains a simple type, the period
of every choice of data exhibiting the type is one. -/
def SupercuspidalSimpleTypeMaximalityStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ) (J : Subgroup (GeneralLinear n F))
      (ρ : SmoothRep.{0, uF, uρ} ℂ J) (d : GLSimpleTypeData ψF ρ)
      (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)),
      GeneralLinear.supercuspidalProperty π → ContainsType π ρ → d.period = 1

end Langlands.BushnellKutzko

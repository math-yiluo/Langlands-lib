import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.BushnellKutzko.UnramifiedQuasicharacter
import Langlands.Representation.Classification.Supercuspidal

/-! # Orders of unramified self-twists of a supercuspidal representation -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uρ uπ

/-- **BK93 (6.2.5).** An unramified quasicharacter fixes an irreducible supercuspidal
representation containing the exhibited simple type if and only if its order is finite
and divides `n / e(E|F)`. -/
def SimpleTypeSelfTwistStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ) (J : Subgroup (GeneralLinear n F))
      (ρ : SmoothRep.{0, uF, uρ} ℂ J) (d : GLSimpleTypeData ψF ρ)
      (π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F)),
      GeneralLinear.supercuspidalProperty π → ContainsType π ρ →
      ∀ (χ : Fˣ →* ℂˣ) (hχ : IsUnramifiedQuasicharacter χ),
        (Nonempty ((unramifiedTwist π χ hχ).representation.Equiv π.representation) ↔
          IsOfFinOrder χ ∧ orderOf χ ∣ n / d.ramificationIndex)

end Langlands.BushnellKutzko

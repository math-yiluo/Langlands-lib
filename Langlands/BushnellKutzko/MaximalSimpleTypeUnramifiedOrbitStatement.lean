import Langlands.BushnellKutzko.GLSimpleTypes
import Langlands.BushnellKutzko.TypeContainment
import Langlands.BushnellKutzko.UnramifiedQuasicharacter

/-! # Unramified twisting of representations containing a maximal simple type -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uρ uπ uπ'

/-- **BK93 (6.2.3), last assertion.** The irreducible smooth representations containing a
fixed maximal simple type form one orbit under unramified determinant twists. -/
def MaximalSimpleTypeUnramifiedOrbitStatement : Prop :=
  ∀ (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ), 0 < n →
    ∀ (ψF : AddChar F ℂ) (J : Subgroup (GeneralLinear n F))
      (ρ : SmoothRep.{0, uF, uρ} ℂ J) (d : GLSimpleTypeData ψF ρ),
      d.period = 1 →
      ∀ π : SmoothRep.{0, uF, uπ} ℂ (GeneralLinear n F),
        π.IsIrreducible → ContainsType π ρ →
        ∀ π' : SmoothRep.{0, uF, uπ'} ℂ (GeneralLinear n F), π'.IsIrreducible →
          (ContainsType π' ρ ↔ ∃ (χ : Fˣ →* ℂˣ) (hχ : IsUnramifiedQuasicharacter χ),
            Nonempty (π'.representation.Equiv (unramifiedTwist π χ hχ).representation))

end Langlands.BushnellKutzko

import Langlands.Representation.Category.Basic
import Mathlib.Basic.Complex.Basic

/-! # Containment of a representation on restriction -/

namespace Langlands.BushnellKutzko

universe uG uK uπ uρ

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {K : Type uK} [Group K] [TopologicalSpace K]

/-- `π` contains `ρ` on restriction along `i` if there is a nonzero intertwining map from `ρ`
to the restriction. For a subgroup of `G`, take `i` to be its inclusion. -/
def ContainsRepresentation (π : SmoothRep.{0, uG, uπ} ℂ G) (i : K →* G)
    (ρ : SmoothRep.{0, uK, uρ} ℂ K) : Prop :=
  ∃ f : ρ.representation.IntertwiningMap (π.representation.comp i), f ≠ 0

/-- Containment of the pair `(J, λ)` in `π`. -/
abbrev ContainsType (π : SmoothRep.{0, uG, uπ} ℂ G) {J : Subgroup G}
    (ρ : SmoothRep.{0, uG, uρ} ℂ J) : Prop :=
  ContainsRepresentation π J.subtype ρ

end Langlands.BushnellKutzko

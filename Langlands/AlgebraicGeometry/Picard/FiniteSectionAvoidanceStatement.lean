import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Finite-set section avoidance from a basis of section generation opens -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- If the generation opens `X_s` of sections `s` of positive tensor powers of a line
bundle `L` form a basis of the topology, then every finite set `E` of points contained
in an open `W` lies in the generation open `X_s` of one section `s` of a positive tensor
power of `L`, with `X_s` contained in `W`.
This proposition is a derived statement target, not a proof. -/
def FiniteSectionAvoidanceStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X),
    (∀ (W : X.Opens) (x : X), x ∈ W →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
        x ∈ L.sectionOpen s ∧ L.sectionOpen s ≤ W) →
    ∀ (E : Set X) (W : X.Opens), E.Finite → E ⊆ (W : Set X) →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
        E ⊆ (L.sectionOpen s : Set X) ∧ L.sectionOpen s ≤ W

end Langlands.AlgebraicGeometry.Picard

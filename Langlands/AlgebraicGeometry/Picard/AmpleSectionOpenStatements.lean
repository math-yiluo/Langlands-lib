import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Generation opens of sections of powers of an ample line bundle -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For an ample line bundle `L`, the generation opens `X_s` of sections `s` of
positive tensor powers of `L` form a basis of the topology: every open
neighbourhood `W` of a point `x` contains such an `X_s` containing `x`.
This proposition is a statement target, not a proof. -/
def AmpleSectionOpenBasisStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X), L.IsAmple →
    ∀ (W : X.Opens) (x : X), x ∈ W →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n, x ∈ L.sectionOpen s ∧ L.sectionOpen s ≤ W

/-- For an ample line bundle `L`, every finite set `E` of points contained in an
open `W` lies in the generation open `X_s` of one section `s` of a positive tensor
power of `L`, with `X_s` contained in `W`.
This proposition is a statement target, not a proof. -/
def AmpleFiniteSetSectionStatement : Prop :=
  ∀ (X : Scheme.{u}) (L : LineBundle X), L.IsAmple →
    ∀ (E : Set X) (W : X.Opens), E.Finite → E ⊆ (W : Set X) →
      ∃ n : ℕ, 1 ≤ n ∧ ∃ s : L.powSections n,
        E ⊆ (L.sectionOpen s : Set X) ∧ L.sectionOpen s ≤ W

end Langlands.AlgebraicGeometry.Picard

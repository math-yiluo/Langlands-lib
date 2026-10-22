import Langlands.Representation.Filtration.ObjectDefinitions

/-! Deletion of prescribed zero factors from an actual representation filtration. -/

namespace Langlands.ObjectRepFiltration

universe uR uG uV

/-- An actual finite filtration can omit any prescribed set of zero graded
quotients while retaining every selected index exactly once, even when its
graded quotient is zero. This proposition states the existence claim only. -/
def ZeroFactorDeletionTheorem : Prop :=
  ∀ (R : Type uR) [CommRing R] (G : Type uG) [Monoid G]
    (A : Rep.{uV} R G) (m : ℕ) (s : ObjectRepFiltration A m)
    (P : Fin m → Prop),
    (∀ i : Fin m, ¬ P i → Subsingleton (s.gradedRepresentation i)) →
      ∃ (r : ℕ) (e : Fin r ≃ {i : Fin m // P i})
        (t : ObjectRepFiltration A r),
        ∀ j : Fin r,
          Nonempty (Representation.Equiv (t.gradedRepresentation j).ρ
            (s.gradedRepresentation (e j).val).ρ)

end Langlands.ObjectRepFiltration

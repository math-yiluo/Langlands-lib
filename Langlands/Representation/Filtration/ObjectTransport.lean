import Langlands.Representation.Filtration.LengthTwoMatching

/-! Pullback and equivalence transport of supplied actual object filtrations. -/

namespace Langlands.ObjectRepFiltration

universe uR uG uH uV uW

section Pullback

variable {R : Type uR} [CommRing R] {G : Type uG} [Monoid G]
  {H : Type uH} [Monoid H] {A : Rep.{uV} R G} {n : ℕ}

/-- Pull back a supplied filtration, retaining every underlying submodule.
The group homomorphism need not be surjective. -/
def comp (s : ObjectRepFiltration A n) (f : H →* G) :
    ObjectRepFiltration (Rep.of (A.ρ.comp f)) n :=
  ofSubrepresentations
    (fun i => {
      toSubmodule := (s.subrepresentation i).toSubmodule
      apply_mem_toSubmodule h := (s.subrepresentation i).apply_mem_toSubmodule (f h) })
    (fun _ _ hij => s.monotone_subrepresentation hij)
    (by
      apply Subrepresentation.toSubmodule_injective
      change (s.subrepresentation 0).toSubmodule = ⊥
      rw [s.subrepresentation_zero]
      rfl)
    (by
      apply Subrepresentation.toSubmodule_injective
      change (s.subrepresentation (Fin.last n)).toSubmodule = ⊤
      rw [s.subrepresentation_last]
      rfl)

@[simp]
theorem comp_subrepresentation_toSubmodule (s : ObjectRepFiltration A n)
    (f : H →* G) (i : Fin (n + 1)) :
    ((s.comp f).subrepresentation i).toSubmodule =
      (s.subrepresentation i).toSubmodule := rfl

/-- Pullback commutes with the actual successive quotient. -/
def compGradedEquiv (s : ObjectRepFiltration A n) (f : H →* G) (i : Fin n) :
    ((s.comp f).gradedRepresentation i).ρ.Equiv
      ((s.gradedRepresentation i).ρ.comp f) :=
  Representation.Equiv.mk (LinearEquiv.refl R _) (fun _ => rfl)

end Pullback

section Equivalence

variable {k : Type uR} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uV} k G} {B : Rep.{uW} k G} {n : ℕ}

@[simp]
theorem mem_equivTransport_subrepresentation (s : ObjectRepFiltration A n)
    (e : A.ρ.Equiv B.ρ) (i : Fin (n + 1)) (v : B) :
    v ∈ (LengthTwo.transport e s).subrepresentation i ↔
      e.symm v ∈ s.subrepresentation i := Iff.rfl

/-- The ambient equivalence identifies each original actual graded quotient with
the corresponding quotient of the transported filtration. -/
noncomputable def equivTransportGradedEquiv (s : ObjectRepFiltration A n)
    (e : A.ρ.Equiv B.ρ) (i : Fin n) :
    (s.gradedRepresentation i).ρ.Equiv
      ((LengthTwo.transport e s).gradedRepresentation i).ρ :=
  Classical.choice (by
    apply LengthTwo.nonempty_gradedEquiv e.toIntertwiningMap
    · intro v hv
      change e.symm (e v) ∈ (s.subrepresentation i.succ).toSubmodule
      rw [LengthTwo.equiv_symm_apply_apply]
      exact hv
    · intro w hw
      exact ⟨e.symm w, hw, LengthTwo.equiv_apply_symm_apply e w⟩
    · intro v _
      change e.symm (e v) ∈ (s.subrepresentation i.castSucc).toSubmodule ↔ _
      rw [LengthTwo.equiv_symm_apply_apply]
      rfl)

end Equivalence

end Langlands.ObjectRepFiltration

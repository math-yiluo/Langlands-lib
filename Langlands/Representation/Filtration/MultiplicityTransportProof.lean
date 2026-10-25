import Langlands.Representation.Filtration.MultiplicityTransportStatement
import Langlands.Representation.Filtration.JordanHolderTransportProof

/-! Actual supplied-series and factor-count transport. -/

namespace Langlands

universe uK uG uH uA uB uT uU

namespace MultiplicityTransportProof

section Pullback

variable {k : Type uK} [Field k] {G : Type uG} [Group G]
  {H : Type uH} [Group H] (e : H ≃* G)
  {V : Type uA} [AddCommGroup V] [Module k V] (ρ : Representation k G V)

/-- Group pullback retains the invariant vector subspace. -/
def pullSub (S : Subrepresentation ρ) : Subrepresentation (ρ.comp e.toMonoidHom) where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule h := S.apply_mem_toSubmodule (e h)

/-- A bijective change of acting group reflects invariance as well. -/
def unpullSub (S : Subrepresentation (ρ.comp e.toMonoidHom)) : Subrepresentation ρ where
  toSubmodule := S.toSubmodule
  apply_mem_toSubmodule g := by
    simpa using S.apply_mem_toSubmodule (e.symm g)

/-- Group pullback identifies the actual invariant-subspace lattices. -/
def subrepOrderIso : Subrepresentation ρ ≃o Subrepresentation (ρ.comp e.toMonoidHom) where
  toFun := pullSub e ρ
  invFun := unpullSub e ρ
  left_inv _ := by ext; rfl
  right_inv _ := by ext; rfl
  map_rel_iff' := Iff.rfl

variable {W : Type uT} [AddCommGroup W] [Module k W] {σ : Representation k G W}

/-- The same linear equivalence intertwines both pulled-back actions. -/
def pullEquiv (φ : ρ.Equiv σ) :
    Representation.Equiv (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom) :=
  Representation.Equiv.mk φ.toLinearEquiv (fun h => φ.isIntertwining' (e h))

/-- Surjectivity of the group equivalence reflects the intertwining equations. -/
def unpullEquiv (φ : Representation.Equiv
    (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom)) : ρ.Equiv σ :=
  Representation.Equiv.mk φ.toLinearEquiv (by
    intro g
    simpa using φ.isIntertwining' (e.symm g))

theorem nonempty_equiv_iff :
    Nonempty (Representation.Equiv (ρ.comp e.toMonoidHom) (σ.comp e.toMonoidHom)) ↔
      Nonempty (ρ.Equiv σ) :=
  ⟨fun ⟨φ⟩ => ⟨unpullEquiv e ρ φ⟩, fun ⟨φ⟩ => ⟨pullEquiv e ρ φ⟩⟩

/-- Pulling back by a group equivalence and its inverse restores the action. -/
def doublePullEquiv : Representation.Equiv
    ((ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom) ρ :=
  Representation.Equiv.mk (LinearEquiv.refl k V) (by
    intro g
    change ρ (e (e.symm g)) = ρ g
    rw [e.apply_symm_apply])

end Pullback

end MultiplicityTransportProof

open LengthCriterionProof MultiplicityTransportProof

/-- Pull back a supplied chain with the identical vector subspaces, simple
factors, actual graded identifications and exact counts. -/
theorem groupEquivFiltrationMultiplicityTransport :
    GroupEquivFiltrationMultiplicityTransportStatement.{uK, uG, uH, uA, uT} := by
  intro k _ G _ H _ e A τ n s
  let f := MultiplicityTransportProof.subrepOrderIso e A.ρ
  let t : ObjectRepFiltration (Rep.of (A.ρ.comp e.toMonoidHom)) n :=
    ObjectRepFiltration.ofSubrepresentations (fun i => f (s.subrepresentation i))
      (f.monotone.comp s.monotone_subrepresentation)
      (by
        change f (s.subrepresentation 0) = ⊥
        rw [s.subrepresentation_zero]
        exact f.map_bot)
      (by
        change f (s.subrepresentation (Fin.last n)) = ⊤
        rw [s.subrepresentation_last]
        exact f.map_top)
  refine ⟨t, fun _ => rfl, ?_, ?_, ?_⟩
  · rw [hasSimpleFactors_iff_covBy, hasSimpleFactors_iff_covBy]
    exact forall_congr' fun i => (apply_covBy_apply_iff f).symm
  · intro i
    exact ⟨Representation.Equiv.refl ((s.gradedRepresentation i).ρ.comp e.toMonoidHom)⟩
  · unfold ObjectRepFiltration.factorMultiplicity
    apply Nat.card_congr
    refine (Equiv.refl (Fin n)).subtypeEquiv ?_
    intro i
    exact nonempty_equiv_iff e (s.gradedRepresentation i).ρ

/-- Reuse the existing actual image-series construction and compare its
factor-count predicates at the same indices. -/
theorem equivCompositionSeriesMultiplicityTransport :
    EquivCompositionSeriesMultiplicityTransportStatement.{uK, uG, uA, uB, uT, uU} := by
  intro k _ G _ A B τ υ φ ψ n s hs
  obtain ⟨t, ht, hgraded⟩ := jordanHolderSeriesTransport k G A B φ n s hs
  refine ⟨t, ht, hgraded, ?_⟩
  unfold ObjectRepFiltration.factorMultiplicity
  apply Nat.card_congr
  refine (Equiv.refl (Fin n)).subtypeEquiv ?_
  intro i
  obtain ⟨f⟩ := hgraded i
  exact ⟨fun ⟨q⟩ => ⟨(f.trans q).trans ψ.symm⟩,
    fun ⟨p⟩ => ⟨(f.symm.trans p).trans ψ⟩⟩

/-- Ambient and constituent equivalences transport the actual witnesses in
both directions without changing the multiplicity. -/
theorem equivJordanHolderMultiplicityTransport :
    EquivJordanHolderMultiplicityTransportStatement.{uK, uG, uA, uB, uT, uU} := by
  intro k _ G _ A B τ υ φ ψ m
  constructor
  · rintro ⟨n, s, hs, hcount⟩
    obtain ⟨t, ht, -, htcount⟩ :=
      equivCompositionSeriesMultiplicityTransport k G A B τ υ φ ψ n s hs
    exact ⟨n, t, ht, htcount.trans hcount⟩
  · rintro ⟨n, t, ht, hcount⟩
    obtain ⟨s, hs, -, hscount⟩ :=
      equivCompositionSeriesMultiplicityTransport k G B A υ τ φ.symm ψ.symm n t ht
    exact ⟨n, s, hs, hscount.trans hcount⟩

/-- Group pullback transports actual series witnesses; inverse pullback and
the canonical double-pullback equivalences give the reverse implication. -/
theorem groupEquivJordanHolderMultiplicityTransport :
    GroupEquivJordanHolderMultiplicityTransportStatement.{uK, uG, uH, uA, uT} := by
  intro k _ G _ H _ e A τ m
  constructor
  · rintro ⟨n, s, hs, hcount⟩
    obtain ⟨t, -, hsimple, -, htcount⟩ :=
      groupEquivFiltrationMultiplicityTransport k G H e A τ n s
    exact ⟨n, t, hsimple.mp hs, htcount.trans hcount⟩
  · rintro ⟨n, t, ht, hcount⟩
    obtain ⟨s, -, hsimple, -, hscount⟩ :=
      groupEquivFiltrationMultiplicityTransport k H G e.symm
        (Rep.of (A.ρ.comp e.toMonoidHom)) (Rep.of (τ.ρ.comp e.toMonoidHom)) n t
    exact (equivJordanHolderMultiplicityTransport k G
      (Rep.of ((A.ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom)) A
      (Rep.of ((τ.ρ.comp e.toMonoidHom).comp e.symm.toMonoidHom)) τ
      (doublePullEquiv e A.ρ) (doublePullEquiv e τ.ρ) m).mp
        ⟨n, s, hsimple.mp ht, hscount.trans hcount⟩

/-- The two actual-series transports and their witness-preserving multiplicity
consequences, with all seven universes independent. -/
theorem multiplicityTransport :
    MultiplicityTransportStatement.{uK, uG, uH, uA, uB, uT, uU} :=
  ⟨groupEquivFiltrationMultiplicityTransport,
    equivCompositionSeriesMultiplicityTransport,
    groupEquivJordanHolderMultiplicityTransport,
    equivJordanHolderMultiplicityTransport⟩

end Langlands

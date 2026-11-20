import Langlands.Global.Arithmetic.GeneralPositionStatement
import Langlands.ClassFieldTheory.Local.IntermediateReciprocityTransport

/-! # Towers in the algebraic closure of a prescribed intermediate field -/

noncomputable section

universe uF

namespace Langlands.Global.GeneralPosition

open LocalFactor.CommonClosure Weil.Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (E : Extension F)

local notation "EP" => E.asPadicField (p := p)

/-- View a field containing `E` in the chosen algebraic closure of `E`. -/
def rebase (L : Extension F) (h : E.field ≤ L.field) : Extension EP := by
  let : FiniteDimensional F.Carrier (IntermediateField.extendScalars h) :=
    inferInstanceAs (FiniteDimensional F.Carrier L.field)
  let : FiniteDimensional E.field (IntermediateField.extendScalars h) :=
    FiniteDimensional.right F.Carrier E.field (IntermediateField.extendScalars h)
  let e := (intermediateClosureEquiv F E).symm
  exact ⟨(IntermediateField.extendScalars h).map e.toAlgHom,
    FiniteDimensional.of_injective
      (IntermediateField.intermediateFieldMap e (IntermediateField.extendScalars h)).symm.toLinearMap
      (IntermediateField.intermediateFieldMap e (IntermediateField.extendScalars h)).symm.injective⟩

theorem mem_rebase (L : Extension F) (h : E.field ≤ L.field)
    (x : AlgebraicClosure E.field) :
    x ∈ (rebase F E L h).field ↔ intermediateClosureEquiv F E x ∈ L.field := by
  change x ∈ (IntermediateField.extendScalars h).map
    (intermediateClosureEquiv F E).symm.toAlgHom ↔ _
  have H := IntermediateField.map_mem_map (IntermediateField.extendScalars h)
    (intermediateClosureEquiv F E).symm.toAlgHom (x := intermediateClosureEquiv F E x)
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply,
    IntermediateField.mem_extendScalars] using H

theorem rebase_mono {L M : Extension F} (hL : E.field ≤ L.field)
    (hM : E.field ≤ M.field) (h : L.field ≤ M.field) :
    (rebase F E L hL).field ≤ (rebase F E M hM).field :=
  fun x hx => (mem_rebase F E M hM x).mpr (h ((mem_rebase F E L hL x).mp hx))

theorem rebase_self : (rebase F E E le_rfl).field = ⊥ := by
  change (IntermediateField.extendScalars (le_refl E.field)).map
    (intermediateClosureEquiv F E).symm.toAlgHom = ⊥
  rw [IntermediateField.extendScalars_self, IntermediateField.map_bot]

theorem rebase_galois_mem (L : Extension F) (h : E.field ≤ L.field)
    (g : Field.absoluteGaloisGroup (EP).Carrier) :
    g ∈ (rebase F E L h).field.fixingSubgroup ↔
      intermediateGaloisMap F E g ∈ L.field.fixingSubgroup := by
  refine (IntermediateField.mem_fixingSubgroup_iff (rebase F E L h).field g).trans
    (Iff.trans ?_ (IntermediateField.mem_fixingSubgroup_iff L.field
      (intermediateGaloisMap F E g)).symm)
  constructor
  · intro hg x hx
    obtain ⟨y, rfl⟩ := (intermediateClosureEquiv F E).surjective x
    exact (intermediateClosureEquiv_galoisMap F E g y).trans
      (congrArg (intermediateClosureEquiv F E) (hg y ((mem_rebase F E L h y).mpr hx)))
  · intro hg x hx
    apply (intermediateClosureEquiv F E).injective
    exact (intermediateClosureEquiv_galoisMap F E g x).symm.trans
      (hg _ ((mem_rebase F E L h x).mp hx))

theorem rebase_weil_mem (L : Extension F) (h : E.field ≤ L.field) (g : localWeilGroup EP) :
    g ∈ weilSubgroup EP (rebase F E L h) ↔
      (intermediateWeilEquiv F E g : localWeilGroup F) ∈ weilSubgroup F L := by
  change localProjection EP g ∈ (rebase F E L h).field.fixingSubgroup ↔
    localProjection F (intermediateWeilEquiv F E g : localWeilGroup F) ∈ L.field.fixingSubgroup
  rw [intermediateWeilEquiv_projection]
  exact rebase_galois_mem F E L h _

/-- Transport a prime cyclic step along the closure isomorphism. -/
theorem rebase_primeStep {L M : Extension F} (hL : E.field ≤ L.field)
    (hM : E.field ≤ M.field) (hstep : IsCyclicPrimeStep F L M) :
    IsCyclicPrimeStep EP (rebase F E L hL) (rebase F E M hM) := by
  obtain ⟨h, hGal, _, hp⟩ := hstep
  let h' := rebase_mono F E hL hM h
  let eL : L.field ≃+* (rebase F E L hL).field :=
    (IntermediateField.intermediateFieldMap (intermediateClosureEquiv F E).symm
      (IntermediateField.extendScalars hL)).toRingEquiv
  let eM : IntermediateField.extendScalars h ≃+* IntermediateField.extendScalars h' :=
    (IntermediateField.intermediateFieldMap (intermediateClosureEquiv F E).symm
      (IntermediateField.extendScalars hM)).toRingEquiv
  have hc : (algebraMap (rebase F E L hL).field (IntermediateField.extendScalars h')).comp
      eL.toRingHom = eM.toRingHom.comp (algebraMap L.field (IntermediateField.extendScalars h)) := by
    ext x
    rfl
  let : IsGalois (rebase F E L hL).field (IntermediateField.extendScalars h') :=
    IsGalois.of_equiv_equiv (f := eL) (g := eM) hc
  have hp' : (Module.finrank (rebase F E L hL).field (IntermediateField.extendScalars h')).Prime :=
    (Algebra.finrank_eq_of_equiv_equiv eL eM hc) ▸ hp
  let : FiniteDimensional (rebase F E L hL).field (IntermediateField.extendScalars h') :=
    Module.finite_of_finrank_pos hp'.pos
  let : Fact (Module.finrank (rebase F E L hL).field (IntermediateField.extendScalars h')).Prime :=
    ⟨hp'⟩
  exact ⟨h', inferInstance, isCyclic_of_prime_card (IsGalois.card_aut_eq_finrank _ _), hp'⟩

/-- Delete adjacent repetitions in a finite chain, retaining only its stages. -/
theorem compress_chain {α : Type*} (step : α → α → Prop) {n : ℕ}
    (T : Fin (n + 1) → α)
    (hstep : ∀ i : Fin n, T i.succ = T i.castSucc ∨ step (T i.succ) (T i.castSucc)) :
    ∃ (m : ℕ) (S : Fin (m + 1) → α), S 0 = T 0 ∧ S (Fin.last m) = T (Fin.last n) ∧
      (∀ i : Fin m, step (S i.succ) (S i.castSucc)) ∧
      ∀ i, ∃ j, S i = T j := by
  induction n with
  | zero =>
    exact ⟨0, T, rfl, rfl, fun i => Fin.elim0 i, fun i => ⟨i, rfl⟩⟩
  | succ n ih =>
    let V : Fin (n + 1) → α := fun i => T i.succ
    have hV (i : Fin n) : V i.succ = V i.castSucc ∨ step (V i.succ) (V i.castSucc) :=
      hstep i.succ
    obtain ⟨m, S, h₀, hlast, hS, hmem⟩ := ih V hV
    rcases hstep 0 with h | h
    · exact ⟨m, S, h₀.trans h, hlast, hS, fun i => by
        obtain ⟨j, hj⟩ := hmem i
        exact ⟨j.succ, hj⟩⟩
    · refine ⟨m + 1, Fin.cons (T 0) S, Fin.cons_zero _ _, ?_, ?_, ?_⟩
      · rw [Fin.cons_last, hlast]
        rfl
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · change step (S 0) (T 0)
          rw [h₀]
          exact h
        · change step (S j.succ) (S j.castSucc)
          exact hS j
      · intro i
        refine Fin.cases ⟨0, Fin.cons_zero _ _⟩ (fun j => ?_) i
        obtain ⟨k, hk⟩ := hmem j
        exact ⟨k.succ, (Fin.cons_succ _ _ _).trans hk⟩

end Langlands.Global.GeneralPosition

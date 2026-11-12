import Langlands.GroupScheme.Quaternionic.FormLemmas
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.NoncommRing

/-! # Values, polar forms, and maximal singular subspaces -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

variable {K : Type u} {D : Type v} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n]

theorem sesqForm_add_matrix (H H' : Matrix n n D) (x y : n → D) :
    σ.sesqForm (H + H') x y = σ.sesqForm H x y + σ.sesqForm H' x y := by
  simp [sesqForm, mul_add, add_mul, Finset.sum_add_distrib]

variable [DecidableEq n]

/-- Conjugation `z ↦ a z σ(a)` preserves the alternating subspace. -/
theorem sandwich_mem_alternatingSubspace (a : D) {z : D}
    (hz : z ∈ σ.alternatingSubspace) : a * z * σ a ∈ σ.alternatingSubspace := by
  obtain ⟨b, rfl⟩ := σ.mem_alternatingSubspace.mp hz
  apply σ.mem_alternatingSubspace.mpr
  refine ⟨a * b * σ a, ?_⟩
  simp only [map_mul, apply_apply]
  noncomm_ring

/-- The scalar action on quadratic values induced by multiplication of a row vector by
an element of the division algebra. -/
def valueSandwich (a : D) :
    (D ⧸ σ.alternatingSubspace) →ₗ[K] D ⧸ σ.alternatingSubspace :=
  σ.alternatingSubspace.mapQ σ.alternatingSubspace
    { toFun := fun z => a * z * σ a
      map_add' := fun x y => by noncomm_ring
      map_smul' := fun c z => by simp }
    (fun z hz => σ.sandwich_mem_alternatingSubspace a hz)

@[simp] theorem valueSandwich_mk (a z : D) :
    σ.valueSandwich a (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (a * z * σ a) := rfl

theorem quadraticValue_zero (q : σ.QuadraticForms n) : σ.quadraticValue 0 q = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q => simp [quadraticValue_mk, sesqForm]

theorem quadraticValue_smul (a : D) (x : n → D) (q : σ.QuadraticForms n) :
    σ.quadraticValue (a • x) q = σ.valueSandwich a (σ.quadraticValue x q) := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    simp only [quadraticValue_mk, sesqForm_smul_left, sesqForm_smul_right,
      valueSandwich_mk]

theorem quadraticValue_smul_eq_zero (a : D) (x : n → D) (q : σ.QuadraticForms n)
    (hx : σ.quadraticValue x q = 0) : σ.quadraticValue (a • x) q = 0 := by
  rw [quadraticValue_smul, hx, LinearMap.map_zero]

theorem quotient_mk_map (a : D) :
    (Submodule.Quotient.mk (σ a) : D ⧸ σ.alternatingSubspace) =
      Submodule.Quotient.mk a := by
  apply (Submodule.Quotient.eq _).mpr
  simpa using σ.sub_mem_alternatingSubspace (σ a)

theorem sesqForm_polar_mk (Q : Matrix n n D) (x y : n → D) :
    σ.sesqForm (σ.polar (Submodule.Quotient.mk Q : σ.QuadraticForms n)) x y =
      σ.sesqForm Q x y + σ (σ.sesqForm Q y x) := by
  rw [polar_mk, sesqForm_add_matrix, map_sesqForm]

/-- Polarization in the quotient-valued convention of Tits. -/
theorem quadraticValue_add (x y : n → D) (q : σ.QuadraticForms n) :
    σ.quadraticValue (x + y) q =
      σ.quadraticValue x q + σ.quadraticValue y q +
        Submodule.Quotient.mk (σ.sesqForm (σ.polar q) x y) := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    rw [quadraticValue_mk, quadraticValue_mk, quadraticValue_mk,
      sesqForm_add_left, sesqForm_add_right, sesqForm_add_right, sesqForm_polar_mk]
    simp only [← Submodule.mkQ_apply, LinearMap.map_add]
    simp only [Submodule.mkQ_apply, quotient_mk_map]
    abel

theorem matrix_polar (q : σ.QuadraticForms n) :
    σ.matrix n (σ.polar q) = σ.polar q := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q => simp [polar_mk, add_comm]

theorem sesqForm_polar_swap (q : σ.QuadraticForms n) (x y : n → D) :
    σ (σ.sesqForm (σ.polar q) x y) = σ.sesqForm (σ.polar q) y x := by
  rw [map_sesqForm, matrix_polar]

theorem sesqForm_polar_self_eq_zero (q : σ.QuadraticForms n) (x : n → D)
    (hx : σ.quadraticValue x q = 0) : σ.sesqForm (σ.polar q) x x = 0 := by
  induction q using Submodule.Quotient.induction_on with
  | _ Q =>
    rw [quadraticValue_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨a, ha⟩ := σ.mem_alternatingSubspace.mp hx
    rw [sesqForm_polar_mk, ← ha, map_sub, apply_apply]
    abel

theorem isTotallySingular_bot (q : σ.QuadraticForms n) :
    σ.IsTotallySingular q ⊥ := by
  intro x hx
  rw [Submodule.mem_bot] at hx
  subst x
  exact σ.quadraticValue_zero q

theorem IsTotallySingular.mono {q : σ.QuadraticForms n}
    {W W' : Submodule D (n → D)} (hW : σ.IsTotallySingular q W) (h : W' ≤ W) :
    σ.IsTotallySingular q W' :=
  fun x hx => hW x (h hx)

/-- The set of dimensions of totally singular subspaces is nonempty and bounded. -/
theorem singularFinranks_nonempty_bddAbove (q : σ.QuadraticForms n) :
    {r | ∃ W : Submodule D (n → D),
      σ.IsTotallySingular q W ∧ Module.finrank D W = r}.Nonempty ∧
    BddAbove {r | ∃ W : Submodule D (n → D),
      σ.IsTotallySingular q W ∧ Module.finrank D W = r} := by
  constructor
  · exact ⟨0, ⊥, σ.isTotallySingular_bot q, by simp⟩
  · refine ⟨Fintype.card n, ?_⟩
    rintro r ⟨W, _, rfl⟩
    simpa only [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W

theorem IsTotallySingular.finrank_le_quadraticWittIndex
    {q : σ.QuadraticForms n} {W : Submodule D (n → D)}
    (hW : σ.IsTotallySingular q W) : Module.finrank D W ≤ σ.quadraticWittIndex q :=
  le_csSup (σ.singularFinranks_nonempty_bddAbove q).2 ⟨W, hW, rfl⟩

theorem quadraticWittIndex_le_card (q : σ.QuadraticForms n) :
    σ.quadraticWittIndex q ≤ Fintype.card n := by
  apply csSup_le (σ.singularFinranks_nonempty_bddAbove q).1
  rintro r ⟨W, _, rfl⟩
  simpa only [Module.finrank_fintype_fun_eq_card] using Submodule.finrank_le W

/-- The supremum in the definition of the Witt index is attained. -/
theorem exists_maximal_totallySingular (q : σ.QuadraticForms n) :
    ∃ W : Submodule D (n → D),
      σ.IsTotallySingular q W ∧ Module.finrank D W = σ.quadraticWittIndex q := by
  have h := σ.singularFinranks_nonempty_bddAbove q
  exact h.1.csSup_mem h.2.finite

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

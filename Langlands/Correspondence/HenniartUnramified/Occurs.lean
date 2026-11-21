import Langlands.Correspondence.HenniartUnramified.Classification
import Langlands.Representation.Classification.Cosocle
import Langlands.Weil.Representation.SubquotientContinuity
import Mathlib.GroupTheory.OrderOfElement

/-! # Existence of an inertia type of finite period in a representation -/

noncomputable section

namespace Langlands.FiniteRepresentation.SplitDegree

open Representation

universe uG uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {D : SplitDegree G}

variable {V : Type uW} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

omit [IsTopologicalGroup G] [FiniteDimensional ℂ V] in
/-- If the inertia image is finite, conjugation by some positive power of the lift does not
change the inertia action. -/
theorem exists_pos_conj_eq (σ : Representation ℂ G V)
    (hfin : (Set.range (σ.comp D.inertia.subtype)).Finite) :
    ∃ k : ℕ, 0 < k ∧ ∀ n : D.inertia, σ (D.cj k n) = σ n := by
  classical
  let R := Set.range (σ.comp D.inertia.subtype)
  have : Finite R := hfin.to_subtype
  have hmem : ∀ T ∈ R, σ D.lift * T * σ D.lift⁻¹ ∈ R := by
    rintro _ ⟨n, rfl⟩
    refine ⟨D.cj 1 n, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, coe_cj, pow_one, map_mul]
  let c : R → R := fun T => ⟨σ D.lift * T * σ D.lift⁻¹, hmem T T.2⟩
  have hc : Function.Injective c := by
    intro T T' h
    apply Subtype.ext
    have h' := congrArg (fun S : R => σ D.lift⁻¹ * S * σ D.lift) h
    simp only [c] at h'
    have e1 : ∀ X : Module.End ℂ V, σ D.lift⁻¹ * (σ D.lift * X * σ D.lift⁻¹) * σ D.lift = X := by
      intro X
      rw [← mul_assoc, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul, mul_assoc,
        ← map_mul, inv_mul_cancel, map_one, mul_one]
    rw [e1, e1] at h'
    exact h'
  let e : Equiv.Perm R := Equiv.ofBijective c ⟨hc, Finite.injective_iff_surjective.mp hc⟩
  refine ⟨orderOf e, orderOf_pos e, fun n => ?_⟩
  have hiter : ∀ j : ℕ, ((e ^ j) ⟨σ n, n, rfl⟩ : Module.End ℂ V) = σ (D.cj j n) := by
    intro j
    induction j with
    | zero => simp [cj_zero]
    | succ j ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      change σ D.lift * ((e ^ j) ⟨σ n, n, rfl⟩ : Module.End ℂ V) * σ D.lift⁻¹ = _
      rw [ih, ← map_mul, ← map_mul, show j + 1 = 1 + j from add_comm j 1, ← cj_add,
        coe_cj D 1, pow_one]
  have h := hiter (orderOf e)
  rw [pow_orderOf_eq_one, Equiv.Perm.one_apply] at h
  exact h.symm

/-- Every nonzero continuous representation with finite inertia image has an inertia type of
finite period as a quotient of its inertia restriction. -/
theorem exists_occurring_type [Nontrivial V] (σ : Representation ℂ G V)
    (hc : (FiniteRepresentation.of σ).IsContinuous)
    (hfin : (Set.range (σ.comp D.inertia.subtype)).Finite) :
    ∃ B : {B : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType B},
      (∃ P : Representation.IntertwiningMap (σ.comp D.inertia.subtype) B.1.representation,
        P ≠ 0) ∧
      0 < Function.minimalPeriod (D.conjType 1) (D.toClass B) := by
  classical
  let ρ := σ.comp D.inertia.subtype
  let emb : Subrepresentation ρ ↪o Submodule ℂ V :=
    ⟨⟨Subrepresentation.toSubmodule, Subrepresentation.toSubmodule_injective⟩, Iff.rfl⟩
  have : WellFoundedGT (Subrepresentation ρ) := emb.wellFoundedGT
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ :=
    fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)
  obtain ⟨W, hW, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation ρ)).resolve_left hbt
  let π := Representation.quotient ρ W.toSubmodule fun g _ hw => W.apply_mem_toSubmodule g hw
  let q : Representation.IntertwiningMap ρ π :=
    { toLinearMap := W.toSubmodule.mkQ
      isIntertwining' := fun _ => rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hker : q.ker = W :=
    Subrepresentation.toSubmodule_injective (Submodule.ker_mkQ W.toSubmodule)
  have hπ : π.IsIrreducible :=
    (Langlands.Classification.isIrreducible_iff_isCoatom_ker q hq).mpr (by rw [hker]; exact hW)
  have hρc : (FiniteRepresentation.of ρ).IsContinuous :=
    isContinuous_restrict D.inertia.subtype continuous_subtype_val hc
  have hπc : (FiniteRepresentation.of π).IsContinuous :=
    isContinuous_quotient (A := FiniteRepresentation.of ρ) hρc W
  let B : {B : FiniteRepresentation.{0, uG, uW} ℂ D.inertia // D.IsType B} :=
    ⟨FiniteRepresentation.of π, hπc, hπ⟩
  refine ⟨B, ⟨q, fun h0 => ?_⟩, ?_⟩
  · apply hW.1
    apply Subrepresentation.toSubmodule_injective
    apply eq_top_iff.mpr
    intro v _
    have h1 : q v = 0 := by rw [h0]; rfl
    exact (Submodule.Quotient.mk_eq_zero _).mp h1
  · obtain ⟨k, hk, hconj⟩ := exists_pos_conj_eq σ hfin
    apply Function.minimalPeriod_pos_of_mem_periodicPts
    refine ⟨k, hk, ?_⟩
    change (D.conjType 1)^[k] (D.toClass B) = D.toClass B
    rw [iterate_conjType, conjType_mk]
    apply Quotient.sound
    refine ⟨Representation.Equiv.mk (LinearEquiv.refl ℂ _) fun n => ?_⟩
    apply LinearMap.ext
    intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (σ (D.cj k n) v) = Submodule.Quotient.mk (σ n v)
      rw [hconj]

end Langlands.FiniteRepresentation.SplitDegree

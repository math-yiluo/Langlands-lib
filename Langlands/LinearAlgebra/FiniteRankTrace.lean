import Mathlib.Algebra.Module.LinearMap.FiniteRange
import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.Complex.Basic

/-! # Trace on finite-rank complex endomorphisms -/

noncomputable section

namespace Langlands

universe uV uW

variable (V : Type uV) [AddCommGroup V] [Module ℂ V]

/-- The existing submodule of endomorphisms with Noetherian, hence
finite-dimensional, range over the complex field. -/
abbrev finiteRankEnd : Submodule ℂ (Module.End ℂ V) :=
  LinearMap.finiteRange ℂ V V

variable {V}

theorem mem_finiteRankEnd_iff (T : Module.End ℂ V) :
    T ∈ finiteRankEnd V ↔ FiniteDimensional ℂ T.range := by
  constructor
  · intro h
    let : IsNoetherian ℂ T.range := h
    infer_instance
  · intro h
    let := h
    change IsNoetherian ℂ T.range
    infer_instance

namespace FiniteRankEnd

instance finiteDimensional_range (T : finiteRankEnd V) :
    FiniteDimensional ℂ T.val.range :=
  (mem_finiteRankEnd_iff T.val).mp T.property

/-- Restrict an endomorphism to any subspace containing its image. -/
def onSubspace (T : Module.End ℂ V) (S : Submodule ℂ V) (h : T.range ≤ S) :
    Module.End ℂ S :=
  (T.codRestrict S (fun v => h (LinearMap.mem_range_self T v))).comp S.subtype

@[simp]
theorem onSubspace_apply (T : Module.End ℂ V) (S : Submodule ℂ V)
    (h : T.range ≤ S) (v : S) :
    (onSubspace T S h v : V) = T v := rfl

/-- Genuine trace, taken on the finite-dimensional image. -/
def traceValue (T : finiteRankEnd V) : ℂ :=
  LinearMap.trace ℂ T.val.range (onSubspace T.val T.val.range le_rfl)

/-- Any finite-dimensional stage containing the image computes the same trace. -/
theorem traceValue_eq_subspace (T : finiteRankEnd V) (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (h : T.val.range ≤ S) :
    traceValue T = LinearMap.trace ℂ S (onSubspace T.val S h) := by
  let i : T.val.range →ₗ[ℂ] S := Submodule.inclusion h
  let f : S →ₗ[ℂ] T.val.range := T.val.rangeRestrict.comp S.subtype
  have h₁ : f.comp i = onSubspace T.val T.val.range le_rfl := by
    ext v
    rfl
  have h₂ : i.comp f = onSubspace T.val S h := by
    ext v
    rfl
  unfold traceValue
  rw [← h₁, ← h₂]
  exact LinearMap.trace_comp_comm' i f

theorem traceValue_add (T U : finiteRankEnd V) :
    traceValue (T + U) = traceValue T + traceValue U := by
  let S : Submodule ℂ V := T.val.range ⊔ U.val.range
  have hT : T.val.range ≤ S := le_sup_left
  have hU : U.val.range ≤ S := le_sup_right
  have hTU : (T + U).val.range ≤ S := LinearMap.range_add_le T.val U.val
  rw [traceValue_eq_subspace (T + U) S hTU,
    traceValue_eq_subspace T S hT, traceValue_eq_subspace U S hU]
  have h : onSubspace (T + U).val S hTU =
      onSubspace T.val S hT + onSubspace U.val S hU := by
    ext v
    rfl
  rw [h, map_add]

theorem traceValue_smul (c : ℂ) (T : finiteRankEnd V) :
    traceValue (c • T) = c • traceValue T := by
  have h : (c • T).val.range ≤ T.val.range :=
    LinearMap.range_smul_le_range T.val c
  rw [traceValue_eq_subspace (c • T) T.val.range h]
  have he : onSubspace (c • T).val T.val.range h =
      c • onSubspace T.val T.val.range le_rfl := by
    ext v
    rfl
  rw [he, map_smul]
  rfl

/-- The complex linear trace functional on actual finite-rank endomorphisms. -/
def trace : finiteRankEnd V →ₗ[ℂ] ℂ where
  toFun := traceValue
  map_add' := traceValue_add
  map_smul' := traceValue_smul

theorem trace_eq_subspace (T : finiteRankEnd V) (S : Submodule ℂ V)
    [FiniteDimensional ℂ S] (h : T.val.range ≤ S) :
    trace T = LinearMap.trace ℂ S (onSubspace T.val S h) :=
  traceValue_eq_subspace T S h

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A factorization through a finite-dimensional carrier gives a finite-rank map. -/
def ofFactorization [FiniteDimensional ℂ W] (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] V) :
    finiteRankEnd V :=
  ⟨g.comp f, (LinearMap.HasNoetherianRange.of_isNoetherian_dom (f := g)).comp_right f⟩

/-- Cyclic trace through any finite-dimensional factorization. -/
theorem trace_eq_of_factorization [FiniteDimensional ℂ W] (T : finiteRankEnd V)
    (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] V) (hT : T.val = g.comp f) :
    trace T = LinearMap.trace ℂ W (f.comp g) := by
  have h : T.val.range ≤ g.range := by
    rw [hT]
    exact LinearMap.range_comp_le_range f g
  rw [trace_eq_subspace T g.range h]
  have he : onSubspace T.val g.range h =
      g.rangeRestrict.comp (f.comp g.range.subtype) := by
    ext v
    change T.val v = g (f v)
    rw [hT]
    rfl
  rw [he, LinearMap.trace_comp_comm']
  rfl

@[simp]
theorem trace_ofFactorization [FiniteDimensional ℂ W]
    (f : V →ₗ[ℂ] W) (g : W →ₗ[ℂ] V) :
    trace (ofFactorization f g) = LinearMap.trace ℂ W (f.comp g) :=
  trace_eq_of_factorization _ f g rfl

/-- On a finite-dimensional ambient carrier this agrees with Mathlib's trace. -/
theorem trace_eq_ambient [FiniteDimensional ℂ V] (T : finiteRankEnd V) :
    trace T = LinearMap.trace ℂ V T.val := by
  simpa using trace_eq_of_factorization T LinearMap.id T.val (by simp)

/-- The rank-one endomorphism `v ↦ ell(v) • w`. -/
def rankOne (ell : Module.Dual ℂ V) (w : V) : finiteRankEnd V :=
  ofFactorization ell ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight w)

@[simp]
theorem rankOne_apply (ell : Module.Dual ℂ V) (w v : V) :
    (rankOne ell w).val v = ell v • w := rfl

@[simp]
theorem trace_rankOne (ell : Module.Dual ℂ V) (w : V) :
    trace (rankOne ell w) = ell w := by
  rw [rankOne, trace_ofFactorization]
  have he : ell.comp ((LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight w) =
      (LinearMap.id : ℂ →ₗ[ℂ] ℂ).smulRight (ell w) := by
    ext
    simp
  rw [he, LinearMap.trace_smulRight, LinearMap.id_apply]

/-- Actual conjugation of a finite-rank map by a linear equivalence. -/
def conjugate (e : V ≃ₗ[ℂ] W) (T : finiteRankEnd V) : finiteRankEnd W :=
  ⟨e.conj T.val, (T.property.comp_right e.symm.toLinearMap).comp_left e.toLinearMap⟩

@[simp]
theorem conjugate_apply (e : V ≃ₗ[ℂ] W) (T : finiteRankEnd V) (w : W) :
    (conjugate e T).val w = e (T.val (e.symm w)) := rfl

/-- Genuine trace is invariant under equivalences of arbitrary carrier universes. -/
@[simp]
theorem trace_conjugate (e : V ≃ₗ[ℂ] W) (T : finiteRankEnd V) :
    trace (conjugate e T) = trace T := by
  let f : W →ₗ[ℂ] T.val.range := T.val.rangeRestrict.comp e.symm.toLinearMap
  let g : T.val.range →ₗ[ℂ] W := e.toLinearMap.comp T.val.range.subtype
  have h : (conjugate e T).val = g.comp f := by
    ext w
    rfl
  rw [trace_eq_of_factorization (conjugate e T) f g h]
  change LinearMap.trace ℂ T.val.range (f.comp g) =
    LinearMap.trace ℂ T.val.range (onSubspace T.val T.val.range le_rfl)
  congr 1
  ext v
  change T.val (e.symm (e v.val)) = T.val v.val
  rw [e.symm_apply_apply]

end FiniteRankEnd
end Langlands

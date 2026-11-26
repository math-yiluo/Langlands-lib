import Langlands.Algebra.RegularTrace
import Langlands.BaseChange.TwistedCharacter.SemisimpleSlice
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.SimpleModule.WedderburnArtin

/-! # Fixed algebras of semisimple adjoint operators -/

noncomputable section

namespace Langlands.BaseChange

open Module

variable {F B : Type*} [Field F] [CharZero F] [Ring B] [Algebra F B] [FiniteDimensional F B]

/-- Trace of left multiplication on a finite-dimensional associative algebra. -/
def leftRegularTrace : B →ₗ[F] F :=
  Langlands.Algebra.regularTrace F B

omit [CharZero F] [FiniteDimensional F B] in
private theorem leftRegularTrace_mul_comm (x y : B) :
    leftRegularTrace (F := F) (x * y) = leftRegularTrace (y * x) :=
  Langlands.Algebra.regularTrace_mul_comm F B x y

omit [CharZero F] [FiniteDimensional F B] in
private theorem leftRegularTrace_automorphism (α : B ≃ₐ[F] B) (x : B) :
    leftRegularTrace (F := F) (α x) = leftRegularTrace x := by
  change LinearMap.trace F B (Algebra.lmul F B (α x)) =
    LinearMap.trace F B (Algebra.lmul F B x)
  have he : Algebra.lmul F B (α x) = α.toLinearEquiv.conj (Algebra.lmul F B x) := by
    ext z
    change α x * z = α (x * α.symm z)
    rw [map_mul, α.apply_symm_apply]
  rw [he, LinearMap.trace_conj']

private theorem eq_zero_of_leftRegularTrace_mul_eq_zero [IsSemisimpleRing B] (x : B)
    (hx : ∀ y : B, leftRegularTrace (F := F) (x * y) = 0) : x = 0 := by
  let I : Submodule B B := Submodule.span B {x}
  obtain ⟨J, hJ⟩ := exists_isCompl I
  let P := I.projection J hJ
  let e := P 1
  have he (y : B) : P y = y * e := by
    simpa only [smul_eq_mul, mul_one, e] using P.map_smul y (1 : B)
  have hIe : e ∈ I := Submodule.projection_apply_mem hJ 1
  have he2 : IsIdempotentElem e :=
    (he e).symm.trans (Submodule.projection_apply_of_mem_left hJ hIe)
  obtain ⟨y, hy⟩ := Submodule.mem_span_singleton.mp hIe
  have hy' : y * x = e := hy
  have htr : leftRegularTrace (F := F) e = 0 := by
    rw [← hy', leftRegularTrace_mul_comm]
    exact hx y
  have hlm : Algebra.lmul F B e = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff (he2.map (Algebra.lmul F B))).mp htr
  have he0 : e = 0 := Algebra.lmul_injective (hlm.trans (map_zero (Algebra.lmul F B)).symm)
  have hp : P x = x := Submodule.projection_apply_of_mem_left hJ (Submodule.mem_span_singleton_self x)
  rw [he, he0, mul_zero] at hp
  exact hp.symm

private theorem fixed_eq_zero_of_leftRegularTrace_mul_eq_zero [IsSemisimpleRing B]
    (α : B ≃ₐ[F] B) (hα : Module.End.IsSemisimple α.toLinearMap)
    (x : adjointFixedAlgebra α)
    (hx : ∀ y : adjointFixedAlgebra α, leftRegularTrace (F := F) (x.val * y.val) = 0) : x = 0 := by
  let S := (adjointFixedAlgebra α).toSubmodule
  have hS : S ∈ Module.End.invtSubmodule α.toLinearMap := by
    intro z hz
    change α z = z at hz
    change α z ∈ S
    rwa [hz]
  obtain ⟨Q, hQ, hSQ⟩ := Module.End.isSemisimple_iff.mp hα S hS
  have hmap : ∀ z ∈ Q, α.toLinearMap z ∈ Q :=
    (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem α.toLinearMap).mp hQ
  let a : End F Q := LinearMap.id - α.toLinearMap.restrict hmap
  have ha : Function.Injective a := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hza : z.val - α z.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    have hzS : z.val ∈ S := (sub_eq_zero.mp hza).symm
    exact Subtype.ext (Submodule.disjoint_def.mp hSQ.disjoint z.val hzS z.prop)
  have haSurj := (a.linearEquivOfInjective ha rfl).surjective
  have hαx : α x.val = x.val := x.prop
  have hQtrace : ∀ q : Q, leftRegularTrace (F := F) (x.val * q.val) = 0 := by
    intro q
    obtain ⟨z, hz⟩ := haSurj q
    have hq : q.val = z.val - α z.val := (congrArg Subtype.val hz).symm
    have htr : leftRegularTrace (F := F) (x.val * α z.val) = leftRegularTrace (x.val * z.val) := by
      have he := leftRegularTrace_automorphism α (x.val * z.val)
      rwa [map_mul, hαx] at he
    rw [hq, mul_sub, map_sub, htr, sub_self]
  apply Subtype.ext
  apply eq_zero_of_leftRegularTrace_mul_eq_zero (F := F)
  intro y
  obtain ⟨⟨s, q⟩, hy⟩ := (S.prodEquivOfIsCompl Q hSQ).surjective y
  change s.val + q.val = y at hy
  rw [← hy, mul_add, map_add, hx s, hQtrace, add_zero]

/-- The fixed algebra of a semisimple automorphism of a finite-dimensional semisimple algebra
is semisimple in characteristic zero. -/
theorem isSemisimpleRing_adjointFixedAlgebra [IsSemisimpleRing B]
    (α : B ≃ₐ[F] B) (hα : Module.End.IsSemisimple α.toLinearMap) :
    IsSemisimpleRing (adjointFixedAlgebra α) := by
  let S := adjointFixedAlgebra α
  have : IsArtinianRing S := IsArtinianRing.of_finite F S
  apply IsArtinianRing.isSemisimpleRing_iff_jacobson.mpr
  apply le_antisymm _ bot_le
  intro x hx
  have hzero : x = 0 := by
    apply fixed_eq_zero_of_leftRegularTrace_mul_eq_zero α hα x
    intro y
    rw [leftRegularTrace_mul_comm]
    have hmem : y * x ∈ Ring.jacobson S := Ideal.mul_mem_left _ _ hx
    obtain ⟨n, hn⟩ := IsSemiprimaryRing.isNilpotent (R := S)
    have hnil : IsNilpotent (y * x : S) := by
      refine ⟨n, ?_⟩
      have hh := Ideal.pow_mem_pow hmem n
      rw [hn] at hh
      change (y * x) ^ n ∈ (⊥ : Ideal S) at hh
      simpa only [Submodule.mem_bot] using hh
    exact (LinearMap.isNilpotent_trace_of_isNilpotent
      ((hnil.map S.val).map (Algebra.lmul F B))).eq_zero
  rwa [Submodule.mem_bot]

/-- The ambient regular trace pair on the subalgebra fixed by the adjoint. -/
def adjointFixedTracePairing (α : B ≃ₐ[F] B) : LinearMap.BilinForm F (adjointFixedAlgebra α) :=
  LinearMap.compr₂ (LinearMap.mul F _) (leftRegularTrace.comp (adjointFixedAlgebra α).val.toLinearMap)

omit [CharZero F] [FiniteDimensional F B] in
@[simp]
theorem adjointFixedTracePairing_apply (α : B ≃ₐ[F] B) (x y : adjointFixedAlgebra α) :
    adjointFixedTracePairing α x y = leftRegularTrace (x.val * y.val) := rfl

omit [CharZero F] [FiniteDimensional F B] in
/-- The trace pair is symmetric. -/
theorem adjointFixedTracePairing_isSymm (α : B ≃ₐ[F] B) :
    (adjointFixedTracePairing α).IsSymm := by
  refine ⟨fun x y => ?_⟩
  simp only [adjointFixedTracePairing_apply, leftRegularTrace_mul_comm x.val y.val]

/-- At a semisimple adjoint operator the trace pair separates points in both variables. -/
theorem adjointFixedTracePairing_nondegenerate [IsSemisimpleRing B]
    (α : B ≃ₐ[F] B) (hα : Module.End.IsSemisimple α.toLinearMap) :
    (adjointFixedTracePairing α).Nondegenerate := by
  refine ⟨fixed_eq_zero_of_leftRegularTrace_mul_eq_zero α hα, fun x hx => ?_⟩
  exact fixed_eq_zero_of_leftRegularTrace_mul_eq_zero α hα x
    (fun y => ((adjointFixedTracePairing_isSymm α).eq x y).trans (hx y))

omit [CharZero F] [FiniteDimensional F B] in
/-- Conjugation by a unit in the fixed algebra preserves the trace pair. -/
theorem adjointFixedTracePairing_conjugation (α : B ≃ₐ[F] B) (u : (adjointFixedAlgebra α)ˣ)
    (x y : adjointFixedAlgebra α) :
    adjointFixedTracePairing α (u.val * x * (u⁻¹ : (adjointFixedAlgebra α)ˣ).val)
      (u.val * y * (u⁻¹ : (adjointFixedAlgebra α)ˣ).val) = adjointFixedTracePairing α x y := by
  let S := adjointFixedAlgebra α
  let v := (u⁻¹ : Sˣ).val
  change leftRegularTrace (F := F) (S.val ((u.val * x * v) * (u.val * y * v))) =
    leftRegularTrace (S.val (x * y))
  have hh : (u.val * x * v) * (u.val * y * v) = (u.val * (x * y)) * v := by
    simp only [mul_assoc, v, Units.inv_mul_cancel_left]
  rw [hh, map_mul, leftRegularTrace_mul_comm, ← map_mul, ← mul_assoc, show v * u.val = 1 from u.inv_mul,
    one_mul]

section Matrix

universe u v

/-- The fixed algebra for a semisimple twisted adjoint is a semisimple ring in the
finite reduced coefficient-algebra model. -/
theorem isSemisimpleRing_twistedAdjointFixedAlgebra
    {k : Type u} [Field k] [CharZero k] {E : Type v} [CommRing E] [Algebra k E]
    [Module.Finite k E] [IsReduced E] {n : ℕ} (σ : E ≃ₐ[k] E) (δ : GeneralLinear n E)
    (h : Module.End.IsSemisimple (twistedMatrixConj σ δ).toLinearMap) :
    IsSemisimpleRing (adjointFixedAlgebra (twistedAdjointAlgEquiv σ δ)) := by
  have : IsArtinianRing E := IsArtinianRing.of_finite k E
  have : IsSemisimpleRing E := IsArtinianRing.isSemisimpleRing_of_isReduced E
  exact isSemisimpleRing_adjointFixedAlgebra _ h

end Matrix

end Langlands.BaseChange

import Langlands.BaseChange.TwistedCharacter.SemisimpleFixedAlgebra
import Langlands.HarmonicAnalysis.UnitConjugation.PairingFourier

/-! # Trace pairings and projections to the fixed algebra -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis.UnitConjugation

variable {F R : Type*} [Field F] [Ring R] [Algebra F R]

private theorem leftRegularTrace_map (α : R ≃ₐ[F] R) (x : R) :
    leftRegularTrace (F := F) (α x) = leftRegularTrace x := by
  change LinearMap.trace F R (Algebra.lmul F R (α x)) =
    LinearMap.trace F R (Algebra.lmul F R x)
  have he : Algebra.lmul F R (α x) = α.toLinearEquiv.conj (Algebra.lmul F R x) := by
    ext z
    change α x * z = α (x * α.symm z)
    rw [map_mul, α.apply_symm_apply]
  rw [he, LinearMap.trace_conj']

/-- Every algebra automorphism preserves the regular trace pairing. -/
theorem regularTraceForm_automorphism (α : R ≃ₐ[F] R) (x y : R) :
    Langlands.Algebra.regularTraceForm F R (α x) (α y) =
      Langlands.Algebra.regularTraceForm F R x y := by
  change leftRegularTrace (F := F) (α x * α y) = leftRegularTrace (x * y)
  rw [← map_mul, leftRegularTrace_map α]

/-- A projection onto the fixed algebra that is constant along `α` is adjoint
to the inclusion for the ambient and restricted regular trace forms. -/
def FixedTraceProjectionStatement [FiniteDimensional F R]
    (α : R ≃ₐ[F] R) (p : R →ₗ[F] adjointFixedAlgebra α) : Prop :=
  (∀ y : adjointFixedAlgebra α, p y.val = y) →
  (∀ x, p (α x) = p x) →
  ∀ (x : R) (y : adjointFixedAlgebra α),
    adjointFixedTracePairing α (p x) y = Langlands.Algebra.regularTraceForm F R x y.val

variable [FiniteDimensional F R]

theorem fixedTraceProjection (α : R ≃ₐ[F] R) (p : R →ₗ[F] adjointFixedAlgebra α) :
    FixedTraceProjectionStatement α p := by
  intro hp hα x y
  let Q := LinearMap.ker p
  have hQ (z : R) (hz : z ∈ Q) : α.toLinearMap z ∈ Q := by
    change p (α z) = 0
    rw [hα]
    exact hz
  let d : Q →ₗ[F] Q := α.toLinearMap.restrict hQ - LinearMap.id
  have hd : Function.Injective d := by
    apply LinearMap.ker_eq_bot.mp
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hval : α z.val - z.val = 0 := congrArg Subtype.val (LinearMap.mem_ker.mp hz)
    let w : adjointFixedAlgebra α := ⟨z.val, sub_eq_zero.mp hval⟩
    have hz0 : p w.val = 0 := z.property
    apply Subtype.ext
    exact congrArg (fun a : adjointFixedAlgebra α => a.val) ((hp w).symm.trans hz0)
  have hxQ : x - (p x).val ∈ Q := by
    change p (x - (p x).val) = 0
    rw [map_sub, hp, sub_self]
  obtain ⟨z, hz⟩ := (d.linearEquivOfInjective hd rfl).surjective ⟨_, hxQ⟩
  have hdiff : x - (p x).val = α z.val - z.val := (congrArg Subtype.val hz).symm
  have hfixed : α y.val = y.val := y.property
  have htrace : leftRegularTrace (F := F) (α z.val * y.val) = leftRegularTrace (z.val * y.val) := by
    simpa only [map_mul, hfixed] using leftRegularTrace_map α (z.val * y.val)
  change leftRegularTrace ((p x).val * y.val) = leftRegularTrace (x * y.val)
  have hzero := congrArg (fun a : R => leftRegularTrace (F := F) (a * y.val)) hdiff
  simp only [sub_mul, map_sub, htrace, sub_self] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- The ambient regular trace form is an invariant pairing on a finite-dimensional
semisimple algebra in characteristic zero. -/
theorem isInvariantPairing_regularTraceForm [CharZero F] [IsSemisimpleRing R] :
    IsInvariantPairing (Langlands.Algebra.regularTraceForm F R) := by
  let α : R ≃ₐ[F] R := AlgEquiv.refl
  let i (x : R) : adjointFixedAlgebra α := ⟨x, rfl⟩
  have h := adjointFixedTracePairing_nondegenerate α Module.End.isSemisimple_id
  refine ⟨Langlands.Algebra.regularTraceForm_isSymm F R, ⟨?_, ?_⟩, ?_⟩
  · intro x hx
    exact congrArg Subtype.val (h.1 (i x) fun y => hx y.val)
  · intro x hx
    exact congrArg Subtype.val (h.2 (i x) fun y => hx y.val)
  intro u x y
  change leftRegularTrace (F := F)
      (((u : R) * x * ↑u⁻¹) * ((u : R) * y * ↑u⁻¹)) = leftRegularTrace (x * y)
  have hm : ((u : R) * x * ↑u⁻¹) * ((u : R) * y * ↑u⁻¹) =
      (u : R) * (x * y) * ↑u⁻¹ := by
    simp only [mul_assoc, Units.inv_mul_cancel_left]
  rw [hm]
  change Langlands.Algebra.regularTrace F R ((u : R) * (x * y) * ↑u⁻¹) = _
  rw [Langlands.Algebra.regularTrace_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]
  rfl

end Langlands.BaseChange

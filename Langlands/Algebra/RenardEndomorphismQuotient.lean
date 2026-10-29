import Langlands.Algebra.RenardEndomorphismLocalization
import Mathlib.LinearAlgebra.Quotient.Basic

/-! # The actual power-kernel quotient of an endomorphism -/

set_option autoImplicit false

universe u v

namespace Langlands.Renard.EndomorphismLocalization

variable {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]

/-- The increasing union of the kernels of powers of `a`, as an actual submodule. -/
def powerKernel (a : Module.End R V) : Submodule R V :=
  ⨆ n : ℕ, LinearMap.ker (a ^ n)

theorem powerKernel_def (a : Module.End R V) :
    powerKernel a = ⨆ n : ℕ, LinearMap.ker (a ^ n) :=
  rfl

/-- Directedness makes this supremum the literal union, rather than just its span. -/
theorem mem_powerKernel_iff (a : Module.End R V) (z : V) :
    z ∈ powerKernel a ↔ ∃ n : ℕ, (a ^ n) z = 0 := by
  have hd : Directed (· ≤ ·) (fun n : ℕ => LinearMap.ker (a ^ n)) :=
    a.iterateKer.monotone.directed_le
  simp only [powerKernel, Submodule.mem_iSup_of_directed _ hd, LinearMap.mem_ker]

/-- Stability needed to descend `a` to the actual quotient. -/
theorem powerKernel_stable (a : Module.End R V) {z : V}
    (hz : z ∈ powerKernel a) : a z ∈ powerKernel a := by
  obtain ⟨n, hn⟩ := (mem_powerKernel_iff a z).mp hz
  apply (mem_powerKernel_iff a (a z)).mpr
  refine ⟨n, ?_⟩
  rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply, hn, map_zero]

theorem powerKernel_le_comap (a : Module.End R V) :
    powerKernel a ≤ (powerKernel a).comap a :=
  fun _ hz => powerKernel_stable a hz

/-- Renard's `L' = L / K`, using Mathlib's actual module quotient. -/
abbrev PowerKernelQuotient (a : Module.End R V) : Type v :=
  V ⧸ powerKernel a

/-- The canonical quotient projection, independent of the localization map `iota`. -/
def quotientProjection (a : Module.End R V) : V →ₗ[R] PowerKernelQuotient a :=
  (powerKernel a).mkQ

/-- The actual quotient endomorphism, sending the class of `z` to the class of `a z`. -/
def quotientEnd (a : Module.End R V) : Module.End R (PowerKernelQuotient a) :=
  (powerKernel a).mapQ (powerKernel a) a (powerKernel_le_comap a)

theorem quotientProjection_apply (a : Module.End R V) (z : V) :
    quotientProjection a z = (Submodule.Quotient.mk z : PowerKernelQuotient a) :=
  rfl

theorem quotientEnd_projection (a : Module.End R V) (z : V) :
    quotientEnd a (quotientProjection a z) = quotientProjection a (a z) :=
  rfl

theorem quotientEnd_comp_projection (a : Module.End R V) :
    (quotientEnd a).comp (quotientProjection a) = (quotientProjection a).comp a := by
  ext z
  exact quotientEnd_projection a z

theorem quotientProjection_surjective (a : Module.End R V) :
    Function.Surjective (quotientProjection a) :=
  (powerKernel a).mkQ_surjective

theorem ker_quotientProjection (a : Module.End R V) :
    LinearMap.ker (quotientProjection a) = powerKernel a :=
  (powerKernel a).ker_mkQ

end Langlands.Renard.EndomorphismLocalization

import Langlands.Algebra.ArtinReesTensorKernelBoundStatement
import Langlands.Algebra.IdealTensorIntersectionKernelProof
import Mathlib.RingTheory.Filtration

/-! # Proof of the Artin–Rees bound for ideal tensor kernels -/

universe u v

namespace Langlands.Algebra

open TensorProduct LinearMap

/-- If `b ≤ a` and `b ≤ K * a`, then the tensored inclusion `M ⊗[R] b → M ⊗[R] a`
has range inside `K • ⊤`. -/
theorem range_lTensor_inclusion_le_smul_top {R : Type u} {M : Type v} [CommRing R]
    [AddCommGroup M] [Module R M] {a b K : Ideal R} (hba : b ≤ a) (hb : b ≤ K * a) :
    range (lTensor M (Submodule.inclusion hba)) ≤ (K • ⊤ : Submodule R (M ⊗[R] a)) := by
  rintro _ ⟨z, rfl⟩
  induction z with
  | tmul m c =>
    rw [lTensor_tmul]
    have hc : Submodule.inclusion hba c ∈ (K • ⊤ : Submodule R a) := by
      rw [Submodule.mem_smul_top_iff, Ideal.smul_eq_mul]
      exact hb c.2
    exact Submodule.smul_top_le_comap_smul_top K (TensorProduct.mk R M a m) hc
  | add x y hx hy =>
    rw [map_add]
    exact add_mem hx hy

/-- Proof of `ArtinReesTensorKernelBoundStatement`: Artin–Rees for the ideal `a` of the
finite `R`-module `R` gives `c` with `a ⊓ I ^ (n + c) ≤ I ^ n * a`; the published
intersection tensor-kernel transport for `J = I ^ (n + c)` places the kernel in the range
of the tensored inclusion of `a ⊓ I ^ (n + c)`, which factors through `I ^ n * a`. -/
theorem artinReesTensorKernelBound : ArtinReesTensorKernelBoundStatement.{u, v} := by
  intro R M _ _ _ _ I hinj a n x hx
  obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul I (a : Submodule R R)
  have hAR : a ⊓ I ^ (n + c) ≤ I ^ n * a := by
    have h := hc (n + c) (Nat.le_add_left c n)
    rw [Nat.add_sub_cancel] at h
    calc a ⊓ I ^ (n + c) = I ^ (n + c) • ⊤ ⊓ a := by
          rw [inf_comm, Ideal.smul_eq_mul, Ideal.mul_top]
      _ = I ^ n • (I ^ c • ⊤ ⊓ a) := h
      _ ≤ I ^ n • a := smul_mono_right _ inf_le_right
      _ = I ^ n * a := Ideal.smul_eq_mul _ _
  have hsup : Function.Injective (lTensor M (a ⊔ I ^ (n + c)).subtype) :=
    hinj _ (n + c) le_sup_right
  obtain ⟨z, rfl⟩ := idealTensorIntersectionKernel R M a (I ^ (n + c)) hsup hx
  have hfac : Submodule.inclusion (inf_le_left : a ⊓ I ^ (n + c) ≤ a) =
      Submodule.inclusion (Ideal.mul_le_right : I ^ n * a ≤ a) ∘ₗ Submodule.inclusion hAR :=
    rfl
  rw [hfac, lTensor_comp, comp_apply]
  exact range_lTensor_inclusion_le_smul_top _ le_rfl (mem_range_self _ _)

end Langlands.Algebra

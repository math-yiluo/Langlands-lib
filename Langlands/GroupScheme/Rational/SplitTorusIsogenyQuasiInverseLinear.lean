import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.GroupTheory.OrderOfElement

noncomputable section

universe v w

namespace Langlands.GroupScheme.SplitTorusIsogeny

variable {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]

/-- The order of the cokernel sends every element into the range. -/
theorem cokernelCard_smul_mem_range (f : M →ₗ[ℤ] N) (y : N) :
    (Nat.card (N ⧸ f.range) : ℤ) • y ∈ f.range := by
  apply (Submodule.Quotient.mk_eq_zero f.range).mp
  change f.range.mkQ ((Nat.card (N ⧸ f.range) : ℤ) • y) = 0
  rw [map_smul]
  simpa only [natCast_zsmul] using
    (card_nsmul_eq_zero' (x := f.range.mkQ y))

/-- Lift multiplication by the finite cokernel's order through an injective linear map. -/
def quasiInverseOfFiniteCokernel (f : M →ₗ[ℤ] N) (hf : Function.Injective f)
    [Finite (N ⧸ f.range)] : N →ₗ[ℤ] M :=
  (LinearEquiv.ofInjective f hf).symm.toLinearMap ∘ₗ
    (((Nat.card (N ⧸ f.range) : ℤ) • LinearMap.id).codRestrict f.range
      (cokernelCard_smul_mem_range f))

/-- The composite on the target is multiplication by the cokernel's order. -/
theorem comp_quasiInverseOfFiniteCokernel (f : M →ₗ[ℤ] N) (hf : Function.Injective f)
    [Finite (N ⧸ f.range)] :
    f ∘ₗ quasiInverseOfFiniteCokernel f hf =
      (Nat.card (N ⧸ f.range) : ℤ) • LinearMap.id := by
  ext y
  change f ((LinearEquiv.ofInjective f hf).symm
    ⟨(Nat.card (N ⧸ f.range) : ℤ) • y, cokernelCard_smul_mem_range f y⟩) =
      (Nat.card (N ⧸ f.range) : ℤ) • y
  exact LinearEquiv.ofInjective_symm_apply f _

/-- Injectivity forces the same scalar composite on the source. -/
theorem quasiInverseOfFiniteCokernel_comp (f : M →ₗ[ℤ] N) (hf : Function.Injective f)
    [Finite (N ⧸ f.range)] :
    quasiInverseOfFiniteCokernel f hf ∘ₗ f =
      (Nat.card (N ⧸ f.range) : ℤ) • LinearMap.id := by
  ext x
  apply hf
  change f (quasiInverseOfFiniteCokernel f hf (f x)) =
    f ((Nat.card (N ⧸ f.range) : ℤ) • x)
  rw [map_smul]
  exact LinearMap.congr_fun (comp_quasiInverseOfFiniteCokernel f hf) (f x)

/-- An injective integral linear map with finite cokernel has a two-sided integer quasiinverse. -/
theorem exists_quasiInverse_of_injective_finiteCokernel (f : M →ₗ[ℤ] N)
    (hf : Function.Injective f) (hfinite : Finite (N ⧸ f.range)) :
    ∃ n : ℤ, n ≠ 0 ∧ ∃ g : N →ₗ[ℤ] M,
      g ∘ₗ f = n • LinearMap.id ∧ f ∘ₗ g = n • LinearMap.id := by
  let := hfinite
  refine ⟨Nat.card (N ⧸ f.range), ?_, quasiInverseOfFiniteCokernel f hf,
    quasiInverseOfFiniteCokernel_comp f hf, comp_quasiInverseOfFiniteCokernel f hf⟩
  exact Int.natCast_ne_zero.mpr (Nat.card_pos (α := N ⧸ f.range)).ne'

end Langlands.GroupScheme.SplitTorusIsogeny

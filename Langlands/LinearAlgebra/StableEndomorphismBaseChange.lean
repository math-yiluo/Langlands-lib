import Langlands.LinearAlgebra.StableEndomorphismStatements
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! Stability with a fixed exponent under arbitrary extension of scalars. -/

noncomputable section

open scoped TensorProduct

namespace Langlands.LinearAlgebra.StableEndomorphism

universe uR uS uV

section Ring

variable {R : Type uR} [CommRing R] {V : Type uV} [AddCommGroup V] [Module R V]

/-- A stable endomorphism restricts to an automorphism of its actual range. -/
def stableRangeEquiv (f : Module.End R V)
    (hk : LinearMap.ker f = LinearMap.ker (f ^ 2))
    (hr : LinearMap.range f = LinearMap.range (f ^ 2)) :
    LinearMap.range f ≃ₗ[R] LinearMap.range f := by
  let a : Module.End R (LinearMap.range f) := f.rangeRestrict.domRestrict _
  apply LinearEquiv.ofBijective a
  constructor
  · intro x y hxy
    apply Subtype.ext
    obtain ⟨z, hz⟩ := (LinearMap.range f).sub_mem x.property y.property
    have hz2 : z ∈ LinearMap.ker (f ^ 2) := by
      rw [LinearMap.mem_ker, pow_two, Module.End.mul_apply, hz, map_sub]
      exact sub_eq_zero.mpr (congrArg Subtype.val hxy)
    rw [← hk, LinearMap.mem_ker] at hz2
    exact sub_eq_zero.mp (hz.symm.trans hz2)
  · intro y
    have hy : y.val ∈ LinearMap.range (f ^ 2) := hr ▸ y.property
    obtain ⟨z, hz⟩ := hy
    exact ⟨⟨f z, LinearMap.mem_range_self f z⟩, Subtype.ext hz⟩

@[simp] theorem stableRangeEquiv_apply (f : Module.End R V)
    (hk : LinearMap.ker f = LinearMap.ker (f ^ 2))
    (hr : LinearMap.range f = LinearMap.range (f ^ 2)) (x : LinearMap.range f) :
    (stableRangeEquiv f hk hr x).val = f x.val := rfl

/-- A stable endomorphism admits a linear inverse on its range, extended by zero
on its kernel; the two identities suffice for every scalar extension. -/
theorem exists_sqFactorization (f : Module.End R V)
    (hk : LinearMap.ker f = LinearMap.ker (f ^ 2))
    (hr : LinearMap.range f = LinearMap.range (f ^ 2)) :
    ∃ g : Module.End R V, f ^ 2 * g = f ∧ g * f ^ 2 = f := by
  let e := stableRangeEquiv f hk hr
  let g : Module.End R V := (LinearMap.range f).subtype.comp
    (e.symm.toLinearMap.comp (e.symm.toLinearMap.comp f.rangeRestrict))
  have he (x : LinearMap.range f) : f x.val = (e x).val := rfl
  have hi (x : LinearMap.range f) : f (e.symm x).val = x.val :=
    congrArg Subtype.val (e.apply_symm_apply x)
  refine ⟨g, ?_, ?_⟩
  · apply LinearMap.ext
    intro x
    change f (f (e.symm (e.symm (f.rangeRestrict x))).val) = f x
    rw [hi, hi]
    rfl
  · apply LinearMap.ext
    intro x
    change (e.symm (e.symm (e (e (f.rangeRestrict x))))).val = f x
    rw [e.symm_apply_apply, e.symm_apply_apply]
    rfl

/-- These two linear identities imply both stability equalities over any ring. -/
theorem ker_range_sq_of_sqFactorization (f g : Module.End R V)
    (hfg : f ^ 2 * g = f) (hgf : g * f ^ 2 = f) :
    LinearMap.ker f = LinearMap.ker (f ^ 2) ∧
      LinearMap.range f = LinearMap.range (f ^ 2) := by
  constructor
  · apply le_antisymm
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [pow_two, Module.End.mul_apply, hx, map_zero]
    · intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      rw [← hgf, Module.End.mul_apply, hx, map_zero]
  · apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨g x, (LinearMap.congr_fun hfg x)⟩
    · rintro _ ⟨x, rfl⟩
      exact ⟨f x, by rw [pow_two, Module.End.mul_apply]⟩

/-- Both stability equalities survive arbitrary scalar extension. No flatness
or finite-generation hypothesis is needed. -/
theorem ker_range_sq_baseChange (S : Type uS) [CommRing S] [Algebra R S]
    (f : Module.End R V)
    (hk : LinearMap.ker f = LinearMap.ker (f ^ 2))
    (hr : LinearMap.range f = LinearMap.range (f ^ 2)) :
    LinearMap.ker (f.baseChange S) = LinearMap.ker (f.baseChange S ^ 2) ∧
      LinearMap.range (f.baseChange S) = LinearMap.range (f.baseChange S ^ 2) := by
  obtain ⟨g, hfg, hgf⟩ := exists_sqFactorization f hk hr
  apply ker_range_sq_of_sqFactorization (f.baseChange S) (g.baseChange S)
  · simpa only [LinearMap.baseChange_mul, LinearMap.baseChange_pow] using
      congrArg (LinearMap.baseChange S) hfg
  · simpa only [LinearMap.baseChange_mul, LinearMap.baseChange_pow] using
      congrArg (LinearMap.baseChange S) hgf

/-- A fixed stable power survives complex specialization with the same exponent. -/
theorem stablePower_baseChange [Algebra R ℂ] (f : Module.End R V) (b : ℕ)
    (hk : LinearMap.ker (f ^ b) = LinearMap.ker ((f ^ b) ^ 2))
    (hr : LinearMap.range (f ^ b) = LinearMap.range ((f ^ b) ^ 2)) :
    Stable (f.baseChange ℂ ^ b) := by
  have h := ker_range_sq_baseChange ℂ (f ^ b) hk hr
  simpa only [Stable, LinearMap.baseChange_pow] using h

end Ring

end Langlands.LinearAlgebra.StableEndomorphism

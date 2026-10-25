import Mathlib.RepresentationTheory.Irreducible
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Cancelling trivial multiplicity spaces of irreducible representations -/

noncomputable section
open scoped TensorProduct

universe uK uG uV uW uA uB uJ

namespace Langlands.TensorMultiplicity

variable {K : Type uK} [Field K] {G : Type uG} [Monoid G]
variable {V : Type uV} {W : Type uW} {A : Type uA} {B : Type uB}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B]

/-- A vector in a trivial multiplicity space defines an equivariant tensor slice. -/
def slice (ρ : Representation K G V) (a : A) :
    ρ.IntertwiningMap (ρ.tprod (Representation.trivial K G A)) where
  toLinearMap := (TensorProduct.mk K V A).flip a
  isIntertwining' g := by
    ext x
    rfl

@[simp]
theorem slice_apply (ρ : Representation K G V) (a : A) (x : V) :
    slice ρ a x = x ⊗ₜ[K] a := rfl

/-- Taking one basis coefficient in a trivial multiplicity space is equivariant. -/
def coefficient (σ : Representation K G W) {J : Type uJ} [DecidableEq J]
    (b : Module.Basis J K B) (j : J) :
    (σ.tprod (Representation.trivial K G B)).IntertwiningMap σ where
  toLinearMap := (Finsupp.lapply j).comp (TensorProduct.equivFinsuppOfBasisRight b).toLinearMap
  isIntertwining' g := by
    apply TensorProduct.ext'
    intro x y
    change TensorProduct.equivFinsuppOfBasisRight b (σ g x ⊗ₜ[K] y) j =
      σ g (TensorProduct.equivFinsuppOfBasisRight b (x ⊗ₜ[K] y) j)
    simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_smul]

@[simp]
theorem coefficient_apply (σ : Representation K G W) {J : Type uJ} [DecidableEq J]
    (b : Module.Basis J K B) (j : J) (t : W ⊗[K] B) :
    coefficient σ b j t = TensorProduct.equivFinsuppOfBasisRight b t j := rfl

/-- Some equivariant coefficient detects each nonzero tensor. -/
theorem exists_coefficient_ne_zero (σ : Representation K G W)
    {t : W ⊗[K] B} (ht : t ≠ 0) :
    ∃ j, coefficient σ (Module.Free.chooseBasis K B) j t ≠ 0 := by
  classical
  by_contra h
  apply ht
  apply (TensorProduct.equivFinsuppOfBasisRight (Module.Free.chooseBasis K B)).injective
  apply Finsupp.ext
  intro j
  simpa using not_not.mp (not_exists.mp h j)

/-- A tensor of two nonzero vectors over a field is nonzero. -/
theorem tmul_ne_zero {x : V} {a : A} (hx : x ≠ 0) (ha : a ≠ 0) :
    x ⊗ₜ[K] a ≠ 0 := by
  classical
  let b := Module.Free.chooseBasis K A
  have hrepr : b.repr a ≠ 0 := by
    intro h
    exact ha (b.repr.injective (h.trans (map_zero b.repr).symm))
  obtain ⟨j, hj⟩ : ∃ j, b.repr a j ≠ 0 := by
    by_contra h
    exact hrepr (Finsupp.ext fun j => not_not.mp (not_exists.mp h j))
  intro h
  have hh := congrArg (fun t : V ⊗[K] A => TensorProduct.equivFinsuppOfBasisRight b t j) h
  simp only [TensorProduct.equivFinsuppOfBasisRight_apply_tmul_apply, map_zero,
    Finsupp.zero_apply] at hh
  exact (smul_ne_zero hj hx) hh

/-- Equivalent tensors with trivial multiplicity actions have equivalent irreducible
factors, provided the source multiplicity space is nonzero. -/
theorem nonempty_equiv_of_tensor_trivial (ρ : Representation K G V)
    (σ : Representation K G W) [ρ.IsIrreducible] [σ.IsIrreducible] [Nontrivial A]
    (q : (ρ.tprod (Representation.trivial K G A)).Equiv
      (σ.tprod (Representation.trivial K G B))) : Nonempty (ρ.Equiv σ) := by
  classical
  have : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra K G) ρ.asModule
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  obtain ⟨a, ha⟩ := exists_ne (0 : A)
  have ht : q (x ⊗ₜ[K] a) ≠ 0 := by
    intro h
    exact tmul_ne_zero hx ha (q.injective (h.trans q.toLinearEquiv.map_zero.symm))
  obtain ⟨j, hj⟩ := exists_coefficient_ne_zero σ ht
  let f : ρ.IntertwiningMap σ :=
    (coefficient σ (Module.Free.chooseBasis K B) j).comp
      (q.toIntertwiningMap.comp (slice ρ a))
  have hf : f ≠ 0 := by
    intro h
    exact hj (congrArg (fun f : ρ.IntertwiningMap σ => f x) h)
  exact ⟨f.ofBijective ((Representation.IsIrreducible.bijective_or_eq_zero f).resolve_right hf)⟩

end Langlands.TensorMultiplicity

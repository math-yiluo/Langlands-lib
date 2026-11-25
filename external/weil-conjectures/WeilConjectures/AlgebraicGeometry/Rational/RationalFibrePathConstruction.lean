/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import WeilConjectures.AlgebraicGeometry.Galois.GaloisLisseCorrespondenceData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicSheaves
public import Mathlib.CategoryTheory.Conj
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
import WeilConjectures.AlgebraicGeometry.Lisse.LisseRationalScalarFiberMaps

set_option linter.privateModule false
/-! # Rationalization of integral fibre paths

## References

* Deligne, Weil II (1.1.1) c), p.147
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (Y : Scheme.{u}) [IsNoetherian Y] [Y.IsSeparated]
  [∀ x : Y, Invertible (l : Y.residueField x)]
private lemma fractionTensorPure {R B : Type*} [CommRing R] [IsDomain R] [Field B]
    [Algebra R B] [IsFractionRing R B]
    (M : Type*) [AddCommGroup M] [Module R M] (z : B ⊗[R] M) :
    ∃ a : B, ∃ m : M, z = a ⊗ₜ[R] m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors R)
    (TensorProduct.mk R B M 1) z
  have hs0 : algebraMap R B s ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.property
  refine ⟨(algebraMap R B s)⁻¹, m, ?_⟩
  rw [Submonoid.smul_def, ← algebraMap_smul B] at hs
  have h : (algebraMap R B s) • z = (1 : B) ⊗ₜ[R] m := hs
  have hv := congrArg (fun x : B ⊗[R] M ↦ (algebraMap R B s)⁻¹ • x) h
  simpa only [smul_smul, inv_mul_cancel₀ hs0, one_smul, TensorProduct.smul_tmul',
    smul_eq_mul, mul_one] using hv

end AlgebraicGeometry.Scheme

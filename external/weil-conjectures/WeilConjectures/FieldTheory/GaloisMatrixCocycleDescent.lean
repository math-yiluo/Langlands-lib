/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Topology.LocallyConstant.Basic
import WeilConjectures.FieldTheory.GaloisMatrixHilbert90
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Descending a splitting with a genuine Galois matrix cocycle

Source: Stacks Project, Tag 03R7, injectivity via general-linear descent.
(blueprint: lem-sc-galois-matrix-cocycle-descent)
-/

@[expose] public section
universe u
namespace Field
open scoped TensorProduct
/-- A splitting whose base-algebra images have fixed entries descends to the base field.
The entries have unique base-field preimages. Injectivity follows from faithful scalar
extension, and surjectivity follows from equality of finite dimensions. -/
private theorem fixed_matrix_descent (K : Type u) [Field K]
    (D : Type u) [Ring D] [Algebra K D] (n : ℕ)
    (e : (SeparableClosure K ⊗[K] D) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (he : ∀ (g : Gal(SeparableClosure K/K)) (a : D),
      (e (1 ⊗ₜ[K] a)).map g = e (1 ⊗ₜ[K] a)) :
    ∃ f : D →ₐ[K] Matrix (Fin n) (Fin n) K, Function.Bijective f := by
  classical
  let S := SeparableClosure K
  let F : D →ₐ[K] Matrix (Fin n) (Fin n) S :=
    (e.restrictScalars K).toAlgHom.comp Algebra.TensorProduct.includeRight
  have hentry (a : D) (i j : Fin n) : ∃ k : K, algebraMap K S k = F a i j := by
    apply (InfiniteGalois.mem_range_algebraMap_iff_fixed _).mpr
    intro g
    exact congrArg (fun m ↦ m i j) (he g a)
  let f₀ : D → Matrix (Fin n) (Fin n) K := fun a i j ↦ (hentry a i j).choose
  have hf₀ (a : D) : (f₀ a).map (algebraMap K S) = F a := by
    funext i j
    exact (hentry a i j).choose_spec
  let ι : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) S :=
    (Algebra.ofId K S).mapMatrix
  have hι : Function.Injective ι :=
    Matrix.map_injective (FaithfulSMul.algebraMap_injective K S)
  have hfι (a : D) : ι (f₀ a) = F a := hf₀ a
  let f : D →ₐ[K] Matrix (Fin n) (Fin n) K :=
    { toFun := f₀
      map_zero' := hι (by rw [hfι, map_zero, map_zero])
      map_one' := hι (by rw [hfι, map_one, map_one])
      map_add' := fun a c ↦ hι (by rw [hfι, map_add, map_add, hfι, hfι])
      map_mul' := fun a c ↦ hι (by rw [hfι, map_mul, map_mul, hfι, hfι])
      commutes' := fun k ↦ hι (by rw [hfι, F.commutes, ι.commutes]) }
  have hinj : Function.Injective f := by
    intro a c hac
    have ht : (1 : S) ⊗ₜ[K] (a - c) = 0 := by
      apply e.injective
      change F (a - c) = e 0
      rw [map_sub, map_zero, ← hfι a, ← hfι c]
      change ι (f a) - ι (f c) = 0
      rw [hac, sub_self]
    exact sub_eq_zero.mp ((Module.FaithfullyFlat.one_tmul_eq_zero_iff K D (a - c)).mp ht)
  have : Module.Finite S (S ⊗[K] D) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  have : Module.Finite K D := Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  have hdim : Module.finrank K D = Module.finrank K (Matrix (Fin n) (Fin n) K) := by
    rw [← Module.finrank_baseChange (R := S)]
    rw [e.toLinearEquiv.finrank_eq]
    simp only [Matrix, Module.finrank_pi_fintype, Module.finrank_self]
  exact ⟨f, hinj,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := f.toLinearMap) hdim).mp hinj⟩

/-- Conjugation by the inverse of a unit matrix, with its explicit inverse. -/
private def matrixConjugation (K : Type u) [Field K] (n : ℕ)
    (t : Matrix.GeneralLinearGroup (Fin n) K) :
    Matrix (Fin n) (Fin n) K ≃ₐ[K] Matrix (Fin n) (Fin n) K where
  toFun x := t⁻¹.val * x * t.val
  invFun x := t.val * x * t⁻¹.val
  left_inv x := by simp [mul_assoc]
  right_inv x := by simp [mul_assoc]
  map_add' x y := by simp [mul_add, add_mul]
  map_mul' x y := by simp [mul_assoc]
  commutes' r := by
    rw [mul_assoc, Algebra.commutes r t.val, ← mul_assoc, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, one_mul]

/-- The descent construction produces a bijective algebra homomorphism over the base.
The proof is the matrix Hilbert 90 and finite Galois descent argument from Stacks Tag 03R7.
(blueprint: lem-sc-galois-matrix-cocycle-descent) -/
theorem exists_algHom_matrix_of_galois_cocycle (K : Type u) [Field K]
    (D : Type u) [Ring D] [Algebra K D] (n : ℕ)
    (e : (SeparableClosure K ⊗[K] D) ≃ₐ[SeparableClosure K]
      Matrix (Fin n) (Fin n) (SeparableClosure K))
    (b : Gal(SeparableClosure K/K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    (hb : IsLocallyConstant b)
    (hdesc : ∀ (g : Gal(SeparableClosure K/K)) (a : D),
      (e (1 ⊗ₜ[K] a)).map g =
        ((b g)⁻¹).val * e (1 ⊗ₜ[K] a) * (b g).val)
    (hcoc : ∀ g h, b g * Matrix.GeneralLinearGroup.map g.toRingHom (b h) = b (g * h)) :
    ∃ f : D →ₐ[K] Matrix (Fin n) (Fin n) K, Function.Bijective f := by
  obtain ⟨t, ht⟩ := exists_galois_matrix_invariant_basis K n b hb hcoc
  let e' := e.trans (matrixConjugation (SeparableClosure K) n t)
  apply fixed_matrix_descent K D n e'
  intro g a
  change (t⁻¹.val * e (1 ⊗ₜ[K] a) * t.val).map g =
    t⁻¹.val * e (1 ⊗ₜ[K] a) * t.val
  rw [Matrix.map_mul, Matrix.map_mul, hdesc]
  have hright : (b g).val * t.val.map g = t.val := by
    exact congrArg Units.val (ht g)
  have hleft : t⁻¹.val.map g * (b g)⁻¹.val = t⁻¹.val := by
    have hunit : Matrix.GeneralLinearGroup.map g.toRingHom t⁻¹ * (b g)⁻¹ = t⁻¹ := by
      simpa only [mul_inv_rev, map_inv] using congrArg Inv.inv (ht g)
    exact congrArg Units.val hunit
  calc
    _ = (t⁻¹.val.map g * (b g)⁻¹.val) * e (1 ⊗ₜ[K] a) *
        ((b g).val * t.val.map g) := by simp only [mul_assoc]
    _ = _ := by rw [hleft, hright]
end Field

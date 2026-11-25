/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Central.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Central.Matrix
import Mathlib.Algebra.Central.TensorProduct
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Finiteness.Descent
import Mathlib.RingTheory.SimpleRing.Congr
import Mathlib.RingTheory.SimpleRing.Matrix

/-!
# An algebra with a matrix form is central simple

Source: Stacks Project, Tag 03R2, implication (4) to (1), generalized to a field extension.
(blueprint: lem-sc-matrix-form-central-simple).
-/

@[expose] public section

universe u v w

open scoped TensorProduct

namespace Field

/-- An algebra split by a field extension into a nonempty matrix algebra is a CSA.

Proof: finite generation descends along the faithfully flat field extension.
For a proper two-sided ideal I of A, A/I and L tensor_K (A/I) are nontrivial.
The scalar-extended quotient map has simple source (the matrix algebra), hence
is injective. Faithful flatness reflects its injectivity, so I is zero.
For x in the center of A, 1 tensor x is central after scalar extension, hence
is l tensor 1 for some l in L. Choose a K-linear functional f on L with f(1)=1.
Applying f tensor id yields x=f(l) times 1, so x is in the image of K.

Source: Stacks Project, Tag 03R2, implication (4) to (1), generalized to an arbitrary
field extension; the contraction and faithful-flatness arguments are expanded here.
(blueprint: lem-sc-matrix-form-central-simple). -/
theorem centralSimple_of_matrix_form (K : Type u) [Field K]
    (L : Type v) [Field L] [Algebra K L]
    (A : Type w) [Ring A] [Algebra K A]
    (n : ℕ) (hn : n ≠ 0)
    (e : (L ⊗[K] A) ≃ₐ[L] Matrix (Fin n) (Fin n) L) :
    Algebra.IsCentral K A ∧ IsSimpleRing A ∧ FiniteDimensional K A := by
  classical
  have : NeZero n := ⟨hn⟩
  have : Nontrivial (L ⊗[K] A) := e.toEquiv.nontrivial
  have : Nontrivial A :=
    (Algebra.TensorProduct.includeRight : A →ₐ[K] L ⊗[K] A).toRingHom.domain_nontrivial
  have : IsSimpleRing (L ⊗[K] A) :=
    IsSimpleRing.of_ringEquiv e.symm.toRingEquiv inferInstance
  have : FiniteDimensional L (L ⊗[K] A) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  have hfin : FiniteDimensional K A :=
    Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L
  refine ⟨?_, ?_, hfin⟩
  · refine ⟨fun x hx ↦ ?_⟩
    have ht : (1 ⊗ₜ[K] x : L ⊗[K] A) ∈ Subalgebra.center K (L ⊗[K] A) :=
      Algebra.TensorProduct.includeRight_map_center_le K L A ⟨x, hx, rfl⟩
    have hm : e (1 ⊗ₜ[K] x) ∈ Subalgebra.center L (Matrix (Fin n) (Fin n) L) :=
      (MulEquivClass.apply_mem_center_iff e).mpr ht
    obtain ⟨l, hl⟩ := (Algebra.IsCentral.mem_center_iff L).mp hm
    have heq : (1 ⊗ₜ[K] x : L ⊗[K] A) = l ⊗ₜ[K] (1 : A) := by
      apply e.injective
      simpa using hl.trans (e.commutes l).symm
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
    have hc := congrArg
      (fun t ↦ TensorProduct.lid K A (TensorProduct.map f (LinearMap.id) t)) heq
    refine ⟨f l, ?_⟩
    simpa [hf, Algebra.algebraMap_eq_smul_one] using hc.symm
  · apply isSimpleRing_iff_isTwoSided_imp.mpr
    refine ⟨inferInstance, fun I hI ↦ ?_⟩
    have : I.IsTwoSided := hI
    by_cases htop : I = ⊤
    · exact Or.inr htop
    · have : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr htop
      let q := Ideal.Quotient.mkₐ K I
      let tq := Algebra.TensorProduct.map (AlgHom.id L L) q
      have hi : Function.Injective tq := tq.toRingHom.injective
      have hq : Function.Injective q := by
        apply (Module.FaithfullyFlat.lTensor_injective_iff_injective K L q.toLinearMap).mp
        exact hi
      left
      rw [← Ideal.Quotient.mkₐ_ker K I]
      exact (RingHom.injective_iff_ker_eq_bot _).mp hq

end Field

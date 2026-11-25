/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Artinian.Module
import WeilConjectures.FieldTheory.FiniteGaloisReceivingSeparableExtensions

/-!
# Separable splitting with purely inseparable residue fields

Source: Stacks Project, More on Morphisms, proof of Lemma 02LM; Fields, Lemmas 030K,
09DT and 0EXM (blueprint: lem-weil-pbc-separable-split-purely-inseparable-residue-fields).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace Algebra

/-- A finite family of finite field extensions admits a finite separable extension over which
all prime quotients of the tensor products are finite purely inseparable fields. The extension
may be chosen Galois and receiving the relative separable closures of the original fields.
Source: Stacks Project, proof of Lemma 02LM; Fields, Lemmas 030K, 09DT and 0EXM.
(blueprint: lem-weil-pbc-separable-split-purely-inseparable-residue-fields)

Proof:
1. For each i take the relative separable closure S_i of k in K_i. By
   `lem-weil-pbc-separable-first-purely-inseparable` (030K), K_i/S_i is purely inseparable.
   S_i/k is finite, since S_i is a subspace of the finite-dimensional k-vector space K_i.
2. By `lem-weil-pbc-finite-galois-receiving-separable-extensions` (09DT, 0EXM), choose a
   finite Galois extension L/k receiving k-embeddings of every S_i.
3. A k-basis of K_i gives L-module generators 1 tensor e_j of A_i = L tensor_k K_i.
   Thus A_i is finite over L. By `lem-weil-pbc-finite-over-zero-dim-local-discrete-spectrum`,
   A_i has finitely many primes, all maximal; each quotient E is a field finite over L.
4. For b in S_i its minimal polynomial over k splits in L, because its image under the
   chosen embedding is in L and L/k is normal. Its image in E is a root of this split
   polynomial, hence lies in the image of L in E.
5. Every element of E is a finite sum of products of images of elements of L and K_i.
   In characteristic zero K_i = S_i, so step 4 makes L -> E surjective. In characteristic
   p > 0, choose a common p-power exponent sending the finitely many K_i-coefficients
   into S_i. Frobenius additivity and step 4 put that power of the element in L.
   Therefore E/L is purely inseparable, and it is finite by step 3.
For n = 0, the extension k/k (transported to the witness universe) suffices.
-/
theorem exists_separable_split_purelyInseparable_prime_quotients
    (k : Type u) [Field k] (n : ℕ) (K : Fin n → Type v)
    [∀ i : Fin n, Field (K i)] [∀ i : Fin n, Algebra k (K i)] [∀ i : Fin n, Module.Finite k (K i)] :
    ∃ (L : Type (max u v)) (_ : Field L) (_ : Algebra k L),
      Module.Finite k L ∧ Algebra.IsSeparable k L ∧ IsGalois k L ∧
        (∀ i : Fin n, Nonempty (separableClosure k (K i) →ₐ[k] L)) ∧
        ∀ i : Fin n, Finite (PrimeSpectrum (L ⊗[k] K i)) ∧
          ∀ (p : Ideal (L ⊗[k] K i)), p.IsPrime →
            IsField ((L ⊗[k] K i) ⧸ p) ∧
              Module.Finite L ((L ⊗[k] K i) ⧸ p) ∧
              IsPurelyInseparable L ((L ⊗[k] K i) ⧸ p) := by
  obtain ⟨L, hField, hAlg, hFin, hSep, hSplit, hEmb⟩ :=
    finite_galois_receiving_separable_extensions k n
      (fun i ↦ separableClosure k (K i)) (fun i ↦ inferInstance) (fun i ↦ inferInstance)
  let : Field L := hField
  let : Algebra k L := hAlg
  have : Module.Finite k L := hFin
  have : Algebra.IsSeparable k L := hSep
  have : Normal k L := { splits' := hSplit }
  have hGal : IsGalois k L := ⟨⟩
  refine ⟨L, hField, hAlg, hFin, hSep, hGal, hEmb, ?_⟩
  intro i
  have : Module.Finite L (L ⊗[k] K i) := inferInstance
  have : IsArtinianRing (L ⊗[k] K i) :=
    isArtinian_of_tower L (inferInstance : IsArtinian L (L ⊗[k] K i))
  refine ⟨inferInstance, ?_⟩
  intro p hp
  have : p.IsPrime := hp
  have : p.IsMaximal := inferInstance
  refine ⟨(Ideal.Quotient.maximal_ideal_iff_isField_quotient p).mp inferInstance, inferInstance, ?_⟩
  let : Field ((L ⊗[k] K i) ⧸ p) := Ideal.Quotient.field p
  let E := (L ⊗[k] K i) ⧸ p
  let f : K i →ₐ[k] E :=
    (Ideal.Quotient.mkₐ k p).comp Algebra.TensorProduct.includeRight
  obtain ⟨e⟩ := hEmb i
  have hs (b : separableClosure k (K i)) : f b.val ∈ (algebraMap L E).range := by
    have hsplit := Normal.splits (inferInstance : Normal k L) (e b)
    rw [minpoly.algHom_eq e e.injective] at hsplit
    apply hsplit.mem_range_of_isRoot
    · exact Polynomial.map_ne_zero (minpoly.ne_zero (Algebra.IsIntegral.isIntegral b))
    · change Polynomial.eval (f b.val)
        (((minpoly k b).map (algebraMap k L)).map (algebraMap L E)) = 0
      rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq k L E]
      rw [Polynomial.eval_map_algebraMap]
      exact minpoly.aeval_algHom k (f.comp (separableClosure k (K i)).val) b
  let q := ringExpChar k
  have : ExpChar E q := expChar_of_injective_ringHom (algebraMap k E).injective q
  have : ExpChar L q := expChar_of_injective_ringHom (algebraMap k L).injective q
  apply (isPurelyInseparable_iff_pow_mem L q).mpr
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmem : Ideal.Quotient.mk p a ∈ Subalgebra.perfectClosure L E q := by
    induction a using TensorProduct.inductionOn with
    | add a b ha hb =>
      rw [map_add]
      exact (Subalgebra.perfectClosure L E q).add_mem ha hb
    | tmul l a =>
      have hka : f a ∈ Subalgebra.perfectClosure L E q := by
        obtain ⟨m, b, hb⟩ := IsPurelyInseparable.pow_mem (separableClosure k (K i)) q a
        obtain ⟨c, hc⟩ := hs b
        refine ⟨m, c, ?_⟩
        rw [← map_pow, ← hb]
        exact hc
      have hl := (Subalgebra.perfectClosure L E q).algebraMap_mem l
      have heq : Ideal.Quotient.mk p (l ⊗ₜ[k] a) = algebraMap L E l * f a := by
        change Ideal.Quotient.mk p (l ⊗ₜ[k] a) =
          Ideal.Quotient.mk p (l ⊗ₜ[k] (1 : K i)) *
            Ideal.Quotient.mk p ((1 : L) ⊗ₜ[k] a)
        rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [heq]
      exact (Subalgebra.perfectClosure L E q).mul_mem hl hka
  exact hmem

end Algebra

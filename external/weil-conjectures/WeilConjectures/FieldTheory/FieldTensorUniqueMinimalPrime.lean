/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import WeilConjectures.AlgebraicGeometry.FlatFibresIrreducible
import WeilConjectures.RingTheory.TensorFiniteTypeLimit
import WeilConjectures.Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import WeilConjectures.FieldTheory.AlgClosedFiniteTypeTensorDomain
import WeilConjectures.FieldTheory.SepClosedTensorReduction
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Tensor products of fields over a separably closed field

Source: Stacks Project, Algebra, Lemma 00I7 (lemma-separably-closed-irreducible),
specialized to field extensions (blueprint: lem-weil-pbc-field-tensor-irreducible).
-/

@[expose] public section

universe u v w

open scoped TensorProduct
open AlgebraicGeometry

private theorem tensor_domain_of_algClosed
    (k : Type u) [Field k] [IsAlgClosed k]
    (R : Type v) [CommRing R] [IsDomain R] [Algebra k R]
    (S : Type w) [CommRing S] [IsDomain S] [Algebra k S] :
    IsDomain (R ⊗[k] S) := by
  classical
  have : NoZeroDivisors (R ⊗[k] S) := ⟨by
    intro x y hxy
    obtain ⟨sx, hx⟩ := TensorProduct.exists_finset x
    obtain ⟨sy, hy⟩ := TensorProduct.exists_finset y
    let D := Algebra.adjoin k ((sx ∪ sy).image Prod.snd : Set S)
    have : Algebra.FiniteType k D :=
      (Subalgebra.fg_iff_finiteType D).mp (Subalgebra.fg_adjoin_finset _)
    have : IsDomain (R ⊗[k] D) :=
      IsAlgClosed.isDomain_tensorProduct_of_finiteType k R D
    let ι := Algebra.TensorProduct.map (AlgHom.id k R) D.val
    have hinj : Function.Injective ι :=
      Module.Flat.lTensor_preserves_injective_linearMap (M := R) D.val.toLinearMap
        Subtype.val_injective
    have hmem (z : R × S) (hz : z ∈ sx ∪ sy) : z.2 ∈ D :=
      Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hz))
    let x' : R ⊗[k] D :=
      ∑ z ∈ sx.attach, z.1.1 ⊗ₜ ⟨z.1.2, hmem _ (Finset.mem_union_left sy z.2)⟩
    let y' : R ⊗[k] D :=
      ∑ z ∈ sy.attach, z.1.1 ⊗ₜ ⟨z.1.2, hmem _ (Finset.mem_union_right sx z.2)⟩
    have hx' : ι x' = x := by
      rw [hx]
      simp only [x', map_sum, ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Subalgebra.coe_val]
      exact Finset.sum_attach sx fun z ↦ z.1 ⊗ₜ z.2
    have hy' : ι y' = y := by
      rw [hy]
      simp only [y', map_sum, ι, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
        Subalgebra.coe_val]
      exact Finset.sum_attach sy fun z ↦ z.1 ⊗ₜ z.2
    have hxy' : x' * y' = 0 := hinj (by rw [map_mul, hx', hy', hxy, map_zero])
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hxy' with h | h
    · left
      rw [← hx', h, map_zero]
    · right
      rw [← hy', h, map_zero]⟩
  have : Nontrivial (R ⊗[k] S) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain k R S
      (algebraMap k R).injective (algebraMap k S).injective
  exact (isDomain_iff_noZeroDivisors_and_nontrivial _).mpr ⟨inferInstance, inferInstance⟩

namespace IsSepClosed

/-- Over a separably closed field, the tensor product of two field extensions has a unique
minimal prime, and its affine spectrum is irreducible and connected.
Source: Stacks Project, Algebra, Lemma 00I7 (lemma-separably-closed-irreducible)
(blueprint: lem-weil-pbc-field-tensor-irreducible).

Proof:
1. Base change to the algebraic closure of `k`, which is purely inseparable over the
separably closed base. Purely inseparable base change and quotienting by nil ideals
preserve spectra. The reductions `R`, `S` of the base-changed fields are domains, and
`Spec (K ⊗[k] L)` is homeomorphic to `Spec (R ⊗[AlgebraicClosure k] S)`.
2. Over an algebraically closed field, a domain tensored with a finite type domain is a
domain: specialize basis coordinates at each maximal ideal of the finite type factor.
Its residue field is the base field by the Nullstellensatz, so a zero product forces one
specialized factor to vanish. Products of coordinates lie in every maximal ideal and
hence vanish by Jacobsonness. Nonzero coordinates contradict the domain property.
3. For arbitrary domains, each pair of tensor elements comes from a finite type
subalgebra of the second factor. Tensoring that inclusion with the first factor is
injective, since vector spaces are flat. Step 2 therefore rules out zero divisors;
nontriviality makes the tensor product a domain.
4. Transport irreducibility of this domain's spectrum through the homeomorphism of
Step 1. The original tensor product's nilradical is then prime and is its unique minimal
prime. An irreducible space is connected. -/
theorem field_tensor_unique_minimalPrime
    (k : Type u) [Field k] [IsSepClosed k]
    (K : Type v) [Field K] [Algebra k K]
    (L : Type w) [Field L] [Algebra k L] :
    (∃! p : Ideal (K ⊗[k] L), p ∈ minimalPrimes (K ⊗[k] L)) ∧
      IrreducibleSpace (Spec (CommRingCat.of (K ⊗[k] L))) ∧
      ConnectedSpace (Spec (CommRingCat.of (K ⊗[k] L))) := by
  let Ω := AlgebraicClosure k
  let R := (Ω ⊗[k] K) ⧸ nilradical (Ω ⊗[k] K)
  let S := (Ω ⊗[k] L) ⧸ nilradical (Ω ⊗[k] L)
  obtain ⟨hR, hS, ⟨e⟩⟩ := tensor_reduction_domains_homeomorph k K L
  let : IsDomain R := hR
  let : IsDomain S := hS
  let : IsDomain (R ⊗[Ω] S) := tensor_domain_of_algClosed Ω R S
  have : IrreducibleSpace (PrimeSpectrum (K ⊗[k] L)) :=
    e.irreducibleSpace_iff.mpr inferInstance
  have hprime : (nilradical (K ⊗[k] L)).IsPrime :=
    PrimeSpectrum.irreducibleSpace_iff_isPrime_nilradical.mp inferInstance
  let := hprime
  have hmin : minimalPrimes (K ⊗[k] L) = {nilradical (K ⊗[k] L)} := by
    change (⊥ : Ideal (K ⊗[k] L)).minimalPrimes = _
    rw [← Ideal.radical_minimalPrimes]
    have : (⊥ : Ideal (K ⊗[k] L)).radical.IsPrime := hprime
    exact Ideal.minimalPrimes_eq_subsingleton_self
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨nilradical (K ⊗[k] L), ?_, ?_⟩
    · rw [hmin]
      exact Set.mem_singleton _
    · intro p hp
      simpa only [hmin, Set.mem_singleton_iff] using hp
  · change IrreducibleSpace (PrimeSpectrum (K ⊗[k] L))
    infer_instance
  · change ConnectedSpace (PrimeSpectrum (K ⊗[k] L))
    infer_instance

end IsSepClosed

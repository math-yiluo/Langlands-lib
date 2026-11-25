/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.Algebra.Field.ULift

/-!
# Finitely many finite separable extensions embed into one finite Galois extension

Source: literature/stacks-project/fields.tex, Lemmas 09DT and 0EXM and Definition 09I0
(blueprint: lem-weil-pbc-finite-galois-receiving-separable-extensions)
-/

@[expose] public section

open scoped Polynomial

universe u v

/-- Finitely many finite separable extensions of a field embed into one finite Galois
extension. Source: Stacks Project, Fields, Lemmas 09GU, 09DT, 0EXM and Definition 09I0;
More on Morphisms, proof of Lemma 02LM.
(blueprint: lem-weil-pbc-finite-galois-receiving-separable-extensions)

Proof:
1. By `lem-weil-pbc-separable-closure-exists-galois`, choose a separable algebraic,
   separably closed extension Ω/k. Its normality makes it Galois (Definition 09I0).
2. By `lem-weil-pbc-separable-extension-embeds-separably-closed`, embed each Lᵢ into Ω
   as a k-algebra, using its separability and the separable closedness of Ω (09GU).
3. Choose finite k-bases of the Lᵢ. Their images form a finite set S in Ω. By
   `lem-weil-pbc-finite-set-in-finite-galois-subextension`, choose a finite separable
   normal intermediate field K containing S (09DT and 0EXM).
4. Each image lies in K: expand any element in its basis and use k-linearity and
   closure of K under k-linear combinations. Restrict the embeddings' codomains to K
   to obtain the required k-algebra homomorphisms. When n = 0, S is empty and K = k
   suffices, transported to the indicated universe if necessary.
-/
theorem finite_galois_receiving_separable_extensions
    (k : Type u) [Field k] (n : ℕ)
    (L : Fin n → Type v) [hfield : ∀ i, Field (L i)]
    [halgebra : ∀ i, Algebra k (L i)]
    (hfinite : ∀ i, letI := hfield i; letI := halgebra i;
      FiniteDimensional k (L i))
    (hseparable : ∀ i, letI := hfield i; letI := halgebra i;
      Algebra.IsSeparable k (L i)) :
    ∃ (K : Type (max u v)) (hK : Field K) (aK : Algebra k K),
      letI := hK
      letI := aK
      FiniteDimensional k K ∧ Algebra.IsSeparable k K ∧
        (∀ β : K, ((minpoly k β).map (algebraMap k K)).Splits) ∧
        (∀ i : Fin n, letI := hfield i; letI := halgebra i;
          Nonempty ((L i) →ₐ[k] K)) := by
  classical
  let : ∀ i, FiniteDimensional k (L i) := hfinite
  let : ∀ i, Algebra.IsSeparable k (L i) := hseparable
  let Ω := SeparableClosure k
  let σ : ∀ i, L i →ₐ[k] Ω := fun i ↦ IsSepClosed.lift
  let b := fun i ↦ Module.finBasis k (L i)
  let S : Set Ω := Set.range fun p : Σ i, Fin (Module.finrank k (L i)) ↦
    σ p.1 (b p.1 p.2)
  let J := FiniteGaloisIntermediateField.adjoin k S
  have hmem (i : Fin n) (x : L i) : σ i x ∈ J.toIntermediateField := by
    rw [← (b i).sum_repr x, map_sum]
    apply J.toIntermediateField.sum_mem
    intro j hj
    rw [map_smul]
    apply J.toIntermediateField.smul_mem
    exact FiniteGaloisIntermediateField.subset_adjoin k S ⟨⟨i, j⟩, rfl⟩
  let τ : ∀ i, L i →ₐ[k] J := fun i ↦
    (σ i).codRestrict J.toIntermediateField.toSubalgebra (hmem i)
  let K := ULift.{v} J
  let e : J ≃ₐ[k] K := ULift.algEquiv.symm
  let : FiniteDimensional k K :=
    FiniteDimensional.of_injective e.symm.toLinearMap e.symm.injective
  let : IsGalois k K := IsGalois.of_algEquiv e
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact fun β ↦ Normal.splits (inferInstance : Normal k K) β
  · exact fun i ↦ ⟨e.toAlgHom.comp (τ i)⟩

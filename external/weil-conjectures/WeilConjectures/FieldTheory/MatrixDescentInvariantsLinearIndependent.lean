/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FieldTheory.MatrixDescentInvariants
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Linear independence of invariant matrices survives scalar extension

Source: Stacks Project, Tag 03R6, coefficient uniqueness in finite Galois descent.
(blueprint: lem-sc-matrix-descent-invariants-linear-independent).
-/

@[expose] public section

universe u v

namespace Field

/-- A base-field independent family of twisted invariant matrices remains independent
in the ambient matrix space over the separable closure.

Proof: it suffices to treat finite subfamilies. Induct on their size. If the last
vector is in the separable-closure span of the previous ones, its coefficients
are unique by the inductive independence hypothesis. Apply each twisted Galois
map to this expansion. Every vector is fixed, and semilinearity applies the
Galois automorphism to each coefficient, so uniqueness says the coefficients
are fixed by every automorphism. The fixed field of the separable closure is K.
The expansion therefore has coefficients in K, contradicting the original
K-linear independence. The empty family is independent; the argument also
applies to the zero matrix space when n=0. No local constancy or action law for
b is needed: only invertibility of each b(g) and invariance of these vectors.

Source: Stacks Project, Tag 03R6, coefficient uniqueness argument of step 4 of
lem-sc-matrix-descent-scalar-map-bijective.
(blueprint: lem-sc-matrix-descent-invariants-linear-independent). -/
theorem matrixDescentInvariants_linearIndependent (K : Type u) [Field K] (n : ℕ)
    (b : (SeparableClosure K ≃ₐ[K] SeparableClosure K) →
      Matrix.GeneralLinearGroup (Fin n) (SeparableClosure K))
    {ι : Type v} (v : ι → matrixDescentInvariants K n b)
    (hv : LinearIndependent K v) :
    LinearIndependent (SeparableClosure K)
      (fun i ↦ (v i : Matrix (Fin n) (Fin n) (SeparableClosure K))) := by
  classical
  let w : ι → Matrix (Fin n) (Fin n) (SeparableClosure K) := fun i ↦ v i
  have hk : LinearIndependent K w :=
    hv.map' (matrixDescentInvariants K n b).val.toLinearMap
      (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have ht (g : SeparableClosure K ≃ₐ[K] SeparableClosure K)
      (a : SeparableClosure K) (i : ι) :
      (b g).val * (a • w i).map g * ((b g)⁻¹).val = g a • w i := by
    rw [Matrix.map_smul' g a (w i) g.map_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [(v i).property g]
  have hfin (s : Finset ι) : LinearIndepOn (SeparableClosure K) w (s : Set ι) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      rw [Finset.coe_insert]
      apply ih.insert
      intro hmem
      obtain ⟨c, hc⟩ :=
        (Submodule.mem_span_image_finset_iff_exists_fun (SeparableClosure K)).mp hmem
      have hfixed (j : s) (g : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
          g (c j) = c j := by
        apply ih.eq_coords_of_eq (f := fun j : s ↦ g (c j)) (g := c) _ j
        calc
          (∑ j : s, g (c j) • w j) =
              (b g).val * (∑ j : s, c j • w j).map g * ((b g)⁻¹).val := by
            change _ = (b g).val *
              (g.toAlgHom.mapMatrix (∑ j : s, c j • w j)) * ((b g)⁻¹).val
            rw [map_sum, Matrix.mul_sum, Matrix.sum_mul]
            exact Finset.sum_congr rfl fun j _ ↦ (ht g (c j) j).symm
          _ = w i := by rw [hc]; exact (v i).property g
          _ = ∑ j : s, c j • w j := hc.symm
      have hcoeff (j : s) : ∃ a : K, algebraMap K (SeparableClosure K) a = c j :=
        (InfiniteGalois.mem_range_algebraMap_iff_fixed (c j)).mpr (hfixed j)
      choose d hd using hcoeff
      have hmemK : w i ∈ Submodule.span K (w '' (s : Set ι)) := by
        apply (Submodule.mem_span_image_finset_iff_exists_fun K).mpr
        refine ⟨d, ?_⟩
        calc
          (∑ j : s, d j • w j) = ∑ j : s, c j • w j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [← hd j, IsScalarTower.algebraMap_smul]
          _ = w i := hc
      have hk' : LinearIndepOn K w (insert i (s : Set ι)) :=
        hk.comp _ Subtype.val_injective
      exact ((linearIndepOn_insert hi).mp hk').2 hmemK
  apply linearIndependent_iff_finset_linearIndependent.mpr
  exact hfin

end Field

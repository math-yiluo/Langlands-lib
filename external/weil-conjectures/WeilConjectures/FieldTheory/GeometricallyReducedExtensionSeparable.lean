/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import WeilConjectures.FieldTheory.SeparableExtension
import Mathlib.FieldTheory.SeparablyGenerated
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.Field.ULift

/-!
# Geometrically reduced field extensions are separable in positive characteristic

Source: Stacks Project, Algebra, Lemma Tag 030W, implication (4) => (1),
with Definition Tag 030S
(blueprint: lem-weil-pbc-geometrically-reduced-extension-separable).
-/

@[expose] public section

universe u v

open scoped TensorProduct

namespace Algebra

/-- In prime characteristic, reducedness of the tensor product with every field extension
implies separability in the sense that every finitely generated intermediate field is
separably generated. Source: Stacks Project, Algebra, Lemma Tag 030W, (4) => (1),
with Definition Tag 030S
(blueprint: lem-weil-pbc-geometrically-reduced-extension-separable).

Proof:
1. In an algebraic closure of `k`, form the subfield of elements whose `p`-th powers lie
   in `k`. Frobenius is injective and a ring homomorphism, so this subfield contains `k`
   and has a unique `p`-th root of every element of `k`
   (`def-weil-algebraic-closure`, `def-weil-ring-frobenius`, `def-pc-field-extension`).
2. Apply the hypothesis to this extension `L = k^{1/p}`. The ring `K ⊗[k] L` is reduced
   and has characteristic `p` (`def-weil-vector-space-scalar-extension`).
3. For a finite relation with coefficients `cᵢ` in `k`, put `x = ∑ bᵢ ⊗ cᵢ^{1/p}`.
   Frobenius and tensor balancing give `x^p = (∑ cᵢ bᵢ^p) ⊗ 1`
   (`def-weil-ring-frobenius`, `def-weil-vector-space-scalar-extension`).
4. If the `bᵢ` are linearly independent and the latter sum vanishes, reducedness gives
   `x = 0`. Extend the `bᵢ` to a basis and extend scalars; their tensors remain independent.
   Thus every `cᵢ^{1/p}`, and hence every `cᵢ`, is zero
   (`lem-weil-pbc-vector-space-basis-through-vector`, `def-weil-vector-space-scalar-extension`).
5. This independence of `p`-th powers passes to every finitely generated intermediate
   field. Apply `lem-weil-pbc-p-power-independence-separably-generated` to obtain a
   separating transcendence basis there. This is exactly clause (2) of
   `def-weil-pbc-separable-field-extension`.
-/
theorem isSeparableExtension_of_forall_isReduced_tensorProduct
    (k : Type u) (K : Type v) [Field k] [Field K] [Algebra k K]
    (p : ℕ) [Fact p.Prime] [CharP k p]
    (hred : ∀ (L : Type (max u v)) [Field L] [Algebra k L],
      IsReduced (K ⊗[k] L)) :
    Algebra.IsSeparableExtension k K := by
  classical
  -- Frobenius independence, using roots in a universe-lifted algebraic closure.
  have hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (· ^ p) (s : Set K) := by
    let L := ULift.{v} (AlgebraicClosure k)
    let : IsReduced (K ⊗[k] L) := hred L
    let : IsReduced (L ⊗[k] K) :=
      isReduced_of_injective (Algebra.TensorProduct.comm k L K)
        (Algebra.TensorProduct.comm k L K).injective
    let : Nontrivial (L ⊗[k] K) :=
      Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left
        k L K (algebraMap k K).injective
    let : CharP (L ⊗[k] K) p :=
      charP_of_injective_algebraMap (algebraMap k (L ⊗[k] K)).injective p
    intro s hs
    rw [linearIndepOn_finset_iff]
    intro c hc i hi
    have hroot (x : K) : ∃ r : L, r ^ p = algebraMap k L (c x) := by
      obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq
        (algebraMap k (AlgebraicClosure k) (c x)) (Fact.out : p.Prime).pos
      exact ⟨ULift.up r, congrArg ULift.up hr⟩
    choose r hr using hroot
    have hz : (∑ x ∈ s, r x ⊗ₜ[k] x : L ⊗[k] K) ^ p = 0 := by
      rw [sum_pow_char]
      have heq : (∑ x ∈ s, (r x ⊗ₜ[k] x : L ⊗[k] K) ^ p) =
          ∑ x ∈ s, (r x ^ p) ⊗ₜ[k] (x ^ p) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Algebra.TensorProduct.tmul_pow (R := k) (r x) x p
      rw [heq]
      simp_rw [hr]
      have hterm (x : K) :
          (algebraMap k L (c x)) ⊗ₜ[k] (x ^ p) = (1 : L) ⊗ₜ[k] (c x • x ^ p) := by
        rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
      simp_rw [hterm]
      rw [← TensorProduct.tmul_sum, hc, TensorProduct.tmul_zero]
    have hz' : (∑ x ∈ s, r x ⊗ₜ[k] x : L ⊗[k] K) = 0 :=
      IsReduced.eq_zero _ ⟨p, hz⟩
    have hli : LinearIndependent L (fun x : s ↦ (1 : L) ⊗ₜ[k] (x : K)) :=
      Module.Flat.linearIndependent_one_tmul hs
    rw [← s.sum_attach (fun x ↦ r x ⊗ₜ[k] x)] at hz'
    have hsum : (∑ x : s, r x • ((1 : L) ⊗ₜ[k] (x : K))) = 0 := by
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one, Finset.attach_eq_univ] using hz'
    have hri : r i = 0 := (Fintype.linearIndependent_iff.mp hli) (fun x : s ↦ r x) hsum ⟨i, hi⟩
    apply (algebraMap k L).injective
    simpa [hri, zero_pow (Fact.out : p.Prime).ne_zero] using (hr i).symm
  -- Transfer the criterion to each finitely generated intermediate field.
  intro F hF
  let : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have hFpow : ∀ s : Finset F,
      LinearIndepOn k _root_.id (s : Set F) →
        LinearIndepOn k (· ^ p) (s : Set F) := by
    intro s hs
    have hi : Function.Injective F.val := Subtype.val_injective
    have hs' : LinearIndepOn k (fun x : F ↦ (x : K)) (s : Set F) :=
      hs.map_injOn F.val.toLinearMap hi.injOn
    have h := hpow (s.image fun x : F ↦ (x : K)) (by
      simpa only [Finset.coe_image] using hs'.id_image)
    rw [Finset.coe_image] at h
    have h' := h.comp_of_image hi.injOn
    apply (F.val.toLinearMap.linearIndepOn_iff_of_injOn hi.injOn).mp
    change LinearIndepOn k (fun x : F ↦ ((x ^ p : F) : K)) (s : Set F)
    simpa only [Function.comp_def, IntermediateField.coe_pow] using h'
  obtain ⟨s, hs, hsep⟩ :=
    exists_isTranscendenceBasis_and_isSeparable_of_linearIndepOn_pow_of_essFiniteType
      p (Fact.out : p.Prime) hFpow
  exact ⟨(s : Set F), hs, hsep⟩

end Algebra

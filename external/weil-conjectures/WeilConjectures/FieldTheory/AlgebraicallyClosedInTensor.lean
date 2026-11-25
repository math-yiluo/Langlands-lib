/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.RingTheory.Flat.Basic

/-!
# Irreducible polynomials over a field algebraically closed in an extension

Let `k ⊆ K` be fields such that every element of `K` integral over `k` lies in `k`. Then a monic
irreducible polynomial over `k` stays irreducible over `K`: the coefficients of a monic factor
over `K` are integral over `k` (`Polynomial.isIntegral_coeff_of_dvd`), hence lie in `k`.

## Main results

- `Polynomial.Monic.irreducible_map_of_forall_isIntegral`.
-/

@[expose] public section

open Polynomial

namespace Polynomial

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- A monic polynomial over `K` whose coefficients are integral over `k`, for `k` integrally
closed in `K`, comes from `k`. -/
lemma exists_map_eq_of_forall_isIntegral
    (h : ∀ x : K, IsIntegral k x → x ∈ (algebraMap k K).range) {q : K[X]}
    (hq : ∀ i, IsIntegral k (q.coeff i)) : ∃ q₀ : k[X], q₀.map (algebraMap k K) = q := by
  choose c hc using fun i ↦ h _ (hq i)
  refine ⟨∑ i ∈ Finset.range (q.natDegree + 1), C (c i) * X ^ i, ?_⟩
  conv_rhs => rw [q.as_sum_range_C_mul_X_pow]
  simp [Polynomial.map_sum, hc]

/-- **Irreducibility is preserved by extension to a field in which `k` is algebraically
closed.** If every element of `K` integral over `k` lies in `k`, a monic irreducible polynomial
over `k` is irreducible over `K`. -/
theorem Monic.irreducible_map_of_forall_isIntegral
    (h : ∀ x : K, IsIntegral k x → x ∈ (algebraMap k K).range) {f : k[X]} (hf : f.Monic)
    (hirr : Irreducible f) : Irreducible (f.map (algebraMap k K)) := by
  have hfm : (f.map (algebraMap k K)).Monic := hf.map _
  refine ⟨fun hu ↦ hirr.not_isUnit ?_, fun a b hab ↦ ?_⟩
  · rw [Polynomial.isUnit_iff_degree_eq_zero, Polynomial.degree_map] at hu
    exact Polynomial.isUnit_iff_degree_eq_zero.2 hu
  have ha0 : a ≠ 0 := fun h0 ↦ hfm.ne_zero (by rw [hab, h0, zero_mul])
  have hb0 : b ≠ 0 := fun h0 ↦ hfm.ne_zero (by rw [hab, h0, mul_zero])
  -- normalize both factors
  set a' := a * C a.leadingCoeff⁻¹
  set b' := b * C b.leadingCoeff⁻¹
  have ha' : a'.Monic := Polynomial.monic_mul_leadingCoeff_inv ha0
  have hb' : b'.Monic := Polynomial.monic_mul_leadingCoeff_inv hb0
  have hab' : f.map (algebraMap k K) = a' * b' := by
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      have := congrArg Polynomial.leadingCoeff hab
      rwa [hfm.leadingCoeff, Polynomial.leadingCoeff_mul, eq_comm] at this
    have hinv : a.leadingCoeff⁻¹ * b.leadingCoeff⁻¹ = 1 := by
      rw [← mul_inv, hlc, inv_one]
    calc f.map (algebraMap k K) = a * b * C (a.leadingCoeff⁻¹ * b.leadingCoeff⁻¹) := by
          rw [hinv, C_1, mul_one, hab]
      _ = a' * b' := by rw [C_mul]; ring
  obtain ⟨a₀, ha₀⟩ := exists_map_eq_of_forall_isIntegral h
    (isIntegral_coeff_of_dvd f a' hf ha' (Dvd.intro _ hab'.symm))
  obtain ⟨b₀, hb₀⟩ := exists_map_eq_of_forall_isIntegral h
    (isIntegral_coeff_of_dvd f b' hf hb' (Dvd.intro_left _ hab'.symm))
  have hf₀ : f = a₀ * b₀ := Polynomial.map_injective _ (algebraMap k K).injective (by
    rw [Polynomial.map_mul, ha₀, hb₀, hab'])
  rcases hirr.isUnit_or_isUnit hf₀ with hu | hu
  · left
    have hd : a'.degree = 0 := by
      rw [← ha₀, Polynomial.degree_map]; exact Polynomial.degree_eq_zero_of_isUnit hu
    rw [Polynomial.degree_mul, Polynomial.degree_C (inv_ne_zero
      (Polynomial.leadingCoeff_ne_zero.2 ha0)), add_zero] at hd
    exact Polynomial.isUnit_iff_degree_eq_zero.2 hd
  · right
    have hd : b'.degree = 0 := by
      rw [← hb₀, Polynomial.degree_map]; exact Polynomial.degree_eq_zero_of_isUnit hu
    rw [Polynomial.degree_mul, Polynomial.degree_C (inv_ne_zero
      (Polynomial.leadingCoeff_ne_zero.2 hb0)), add_zero] at hd
    exact Polynomial.isUnit_iff_degree_eq_zero.2 hd

end Polynomial

namespace Algebra.TensorProduct

open scoped _root_.TensorProduct

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

/-- For a monic irreducible `f` over `k` and `k` integrally closed in `K`, the ring
`K ⊗[k] k[X]/(f) ≅ K[X]/(f)` is a field. -/
theorem isField_tensorProduct_adjoinRoot
    (h : ∀ x : K, IsIntegral k x → x ∈ (algebraMap k K).range) {f : k[X]} (hf : f.Monic)
    (hirr : Irreducible f) : IsField (K ⊗[k] AdjoinRoot f) := by
  have hirr' := hf.irreducible_map_of_forall_isIntegral h hirr
  have : Fact (Irreducible (f.map (algebraMap k K))) := ⟨hirr'⟩
  let e₁ := AdjoinRoot.tensorAlgEquiv (R := k) (T := K) f
    (f.map (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom) rfl
  let e₂ : AdjoinRoot (f.map
      (Algebra.TensorProduct.includeRight (R := k) (A := K)).toRingHom) ≃+*
      AdjoinRoot (f.map (algebraMap k K)) :=
    AdjoinRoot.mapRingEquiv (Algebra.TensorProduct.rid k k K).toRingEquiv _ _ (by
      rw [Polynomial.map_map]
      refine Associated.of_eq (congrArg (Polynomial.map · f) (RingHom.ext fun x ↦ ?_))
      simp [Algebra.algebraMap_eq_smul_one])
  exact (e₁.toRingEquiv.trans e₂).toMulEquiv.isField (Field.toIsField _)

variable (L : Type*) [Field L] [Algebra k L]

/-- For a finite separable extension `L/k` and `k` integrally closed in `K`, `K ⊗[k] L` is a
field: `L ≅ k[X]/(f)` for the minimal polynomial `f` of a primitive element. -/
theorem isField_of_finiteDimensional [FiniteDimensional k L] [Algebra.IsSeparable k L]
    (h : ∀ x : K, IsIntegral k x → x ∈ (algebraMap k K).range) : IsField (K ⊗[k] L) := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element k L
  have hi : IsIntegral k α := .of_finite k α
  let e : AdjoinRoot (minpoly k α) ≃ₐ[k] L :=
    (IntermediateField.adjoinRootEquivAdjoin k hi).trans
      ((IntermediateField.equivOfEq hα).trans IntermediateField.topEquiv)
  let e' : K ⊗[k] AdjoinRoot (minpoly k α) ≃ₐ[k] K ⊗[k] L :=
    Algebra.TensorProduct.congr AlgEquiv.refl e
  exact e'.symm.toMulEquiv.isField
    (isField_tensorProduct_adjoinRoot h (minpoly.monic hi) (minpoly.irreducible hi))

/-- For a separable algebraic extension `L/k` and `k` integrally closed in `K`, `K ⊗[k] L` is a
domain: it is the directed union of the fields `K ⊗[k] E` over the finite subextensions `E`
(`Algebra.TensorProduct.isField_of_finiteDimensional`), `K` being flat over `k`. -/
theorem isDomain_of_isSeparable [Algebra.IsSeparable k L]
    (h : ∀ x : K, IsIntegral k x → x ∈ (algebraMap k K).range) : IsDomain (K ⊗[k] L) := by
  -- every element comes from a finite subextension
  have hmem (x : K ⊗[k] L) : ∃ E : IntermediateField k L, FiniteDimensional k E ∧
      x ∈ Set.range (Algebra.TensorProduct.map (AlgHom.id k K) E.val) := by
    induction x using TensorProduct.inductionOn with
    | tmul a b =>
      have : FiniteDimensional k (IntermediateField.adjoin k {b}) :=
        IntermediateField.adjoin.finiteDimensional (Algebra.IsSeparable.isIntegral k b)
      exact ⟨IntermediateField.adjoin k {b}, this,
        a ⊗ₜ ⟨b, IntermediateField.mem_adjoin_simple_self k b⟩, rfl⟩
    | add x y hx hy =>
      obtain ⟨E₁, h₁, x', rfl⟩ := hx
      obtain ⟨E₂, h₂, y', rfl⟩ := hy
      refine ⟨E₁ ⊔ E₂, inferInstance, Algebra.TensorProduct.map (AlgHom.id k K)
        (IntermediateField.inclusion le_sup_left) x' + Algebra.TensorProduct.map (AlgHom.id k K)
        (IntermediateField.inclusion le_sup_right) y', ?_⟩
      simp only [map_add, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp,
        AlgHom.comp_id]
      rfl
  have hinj (E : IntermediateField k L) :
      Function.Injective (Algebra.TensorProduct.map (AlgHom.id k K) E.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap (M := K) E.val.toLinearMap
      E.val.injective
  have hfield (E : IntermediateField k L) [FiniteDimensional k E] : IsDomain (K ⊗[k] E) :=
    have := isField_of_finiteDimensional (K := K) E h
    let _ := this.toField
    inferInstance
  have : Nontrivial (K ⊗[k] L) :=
    have := hfield ⊥
    (hinj ⊥).nontrivial
  suffices NoZeroDivisors (K ⊗[k] L) from NoZeroDivisors.to_isDomain _
  refine ⟨fun {a b} hab ↦ ?_⟩
  obtain ⟨E₁, h₁, a', rfl⟩ := hmem a
  obtain ⟨E₂, h₂, b', rfl⟩ := hmem b
  set i₁ := Algebra.TensorProduct.map (AlgHom.id k K) (IntermediateField.inclusion
    (le_sup_left : E₁ ≤ E₁ ⊔ E₂))
  set i₂ := Algebra.TensorProduct.map (AlgHom.id k K) (IntermediateField.inclusion
    (le_sup_right : E₂ ≤ E₁ ⊔ E₂))
  have e₁ : Algebra.TensorProduct.map (AlgHom.id k K) E₁.val a' =
      Algebra.TensorProduct.map (AlgHom.id k K) (E₁ ⊔ E₂).val (i₁ a') := by
    rw [← AlgHom.comp_apply]
    simp only [i₁, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  have e₂ : Algebra.TensorProduct.map (AlgHom.id k K) E₂.val b' =
      Algebra.TensorProduct.map (AlgHom.id k K) (E₁ ⊔ E₂).val (i₂ b') := by
    rw [← AlgHom.comp_apply]
    simp only [i₂, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
    rfl
  rw [e₁, e₂, ← map_mul, ← map_zero (Algebra.TensorProduct.map (AlgHom.id k K) (E₁ ⊔ E₂).val)]
    at hab
  have := hfield (E₁ ⊔ E₂)
  rcases mul_eq_zero.1 (hinj _ hab) with h0 | h0
  · left; rw [e₁, h0, map_zero]
  · right; rw [e₂, h0, map_zero]

end Algebra.TensorProduct

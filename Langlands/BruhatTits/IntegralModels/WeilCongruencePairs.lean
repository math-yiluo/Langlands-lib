import Langlands.GroupScheme.Torus.WeilRestrictionIntegralModel
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.TensorProduct.Pi

/-! # The coefficient algebra of congruence pairs -/

noncomputable section

universe u

open scoped TensorProduct

namespace Langlands.BruhatTits.IntegralModels.WeilCongruence

variable (A : Type u) [CommRing A] {C : Type u} [CommRing C] [Algebra A C]
  (J : Ideal C)

/-- Pairs `(a,c)` with `c` congruent to the image of `a` modulo `J`. -/
def pairs : Subalgebra A (A × C) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ A J).comp (AlgHom.snd A A C))
    ((Ideal.Quotient.mkₐ A J).comp
      ((IsScalarTower.toAlgHom A A C).comp (AlgHom.fst A A C)))

theorem mem_pairs (x : A × C) :
    x ∈ pairs A J ↔ x.2 - algebraMap A C x.1 ∈ J := by
  rw [pairs, AlgHom.mem_equalizer]
  exact Ideal.Quotient.eq

/-- The two literal coefficient projections. -/
abbrev first : pairs A J →ₐ[A] A := (AlgHom.fst A A C).comp (pairs A J).val

abbrev second : pairs A J →ₐ[A] C := (AlgHom.snd A A C).comp (pairs A J).val

@[simp] theorem first_apply (x : pairs A J) : first A J x = (x : A × C).1 := rfl

@[simp] theorem second_apply (x : pairs A J) : second A J x = (x : A × C).2 := rfl

instance [IsNoetherianRing A] [Module.Finite A C] : Module.Finite A (pairs A J) := by
  change Module.Finite A (pairs A J).toSubmodule
  infer_instance

instance [IsDomain A] [IsPrincipalIdealRing A] [Module.Finite A C] [Module.Free A C] :
    Module.Projective A (pairs A J) := by
  have : Module.IsTorsionFree A (pairs A J) :=
    inferInstanceAs (Module.IsTorsionFree A (pairs A J).toSubmodule)
  exact Module.Projective.of_free

/-- A unit of the coefficient algebra with first component one supplies a
congruent unit in the second component. -/
theorem unit_difference_mem (w : (pairs A J)ˣ) (h : first A J w = 1) :
    second A J w - 1 ∈ J := by
  have h' := (mem_pairs A J (w.val : A × C)).mp w.val.property
  change (w.val : A × C).1 = 1 at h
  simpa only [second_apply, h, map_one] using h'

/-- A unit congruent to one determines a unit of the pair algebra over one. -/
def unitPair (w : Cˣ) (h : (w : C) - 1 ∈ J) : (pairs A J)ˣ := by
  have h' : (↑w⁻¹ : C) - 1 ∈ J := by
    have hn := J.neg_mem (J.mul_mem_left (↑w⁻¹ : C) h)
    simpa [mul_sub] using hn
  refine
    { val := ⟨(1, (w : C)), (mem_pairs A J _).2 (by simpa using h)⟩
      inv := ⟨(1, (↑w⁻¹ : C)), (mem_pairs A J _).2 (by simpa using h')⟩
      val_inv := ?_
      inv_val := ?_ }
  · apply Subtype.ext
    change (1 * 1, (w : C) * (↑w⁻¹ : C)) = (1, 1)
    simp
  · apply Subtype.ext
    change (1 * 1, (↑w⁻¹ : C) * (w : C)) = (1, 1)
    simp

@[simp] theorem first_unitPair (w : Cˣ) (h : (w : C) - 1 ∈ J) :
    first A J (unitPair A J w h) = 1 := rfl

@[simp] theorem second_unitPair (w : Cˣ) (h : (w : C) - 1 ∈ J) :
    second A J (unitPair A J w h) = w := rfl

section Generic

variable (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
  (B : Type u) [CommRing B] [Algebra K B] (e : K ⊗[A] C ≃ₐ[K] B)

private def tensorInclusion : K ⊗[A] pairs A J →ₐ[K] K ⊗[A] (A × C) where
  __ := (Algebra.TensorProduct.map (AlgHom.id A K) (pairs A J).val).toRingHom
  commutes' k := by simp [Algebra.TensorProduct.algebraMap_apply]

omit [IsFractionRing A K] in
private theorem tensorInclusion_tmul (k : K) (x : pairs A J) :
    tensorInclusion A J K (k ⊗ₜ x) = k ⊗ₜ (x : A × C) := rfl

private theorem tensorInclusion_bijective (a : A) (ha : a ≠ 0)
    (hJ : algebraMap A C a ∈ J) : Function.Bijective (tensorInclusion A J K) := by
  refine ⟨?_, ?_⟩
  · let : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := K) (pairs A J).val.toLinearMap
      Subtype.val_injective
  · intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      exact ⟨x' + y', map_add _ _ _⟩
    | tmul k x =>
      have hax : a • x ∈ pairs A J := by
        rw [mem_pairs]
        rw [Prod.smul_fst, Prod.smul_snd, Algebra.smul_def, smul_eq_mul, map_mul, ← mul_sub]
        exact J.mul_mem_right _ hJ
      refine ⟨(k / algebraMap A K a) ⊗ₜ ⟨a • x, hax⟩, ?_⟩
      rw [tensorInclusion_tmul, ← TensorProduct.smul_tmul, Algebra.smul_def, mul_div_cancel₀]
      exact (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha

/-- Inverting a nonzero scalar in the congruence ideal separates both
coefficient projections. -/
def genericPairsEquiv (a : A) (ha : a ≠ 0) (hJ : algebraMap A C a ∈ J) :
    K ⊗[A] pairs A J ≃ₐ[K] K × B :=
  ((AlgEquiv.ofBijective (tensorInclusion A J K)
    (tensorInclusion_bijective A J K a ha hJ)).trans
    (Algebra.TensorProduct.prodRight A K K A C)).trans
    ((Algebra.TensorProduct.rid A K K).prodCongr e)

@[simp] theorem genericPairsEquiv_tmul (a : A) (ha : a ≠ 0)
    (hJ : algebraMap A C a ∈ J) (k : K) (x : pairs A J) :
    genericPairsEquiv A J K B e a ha hJ (k ⊗ₜ x) =
      (k * algebraMap A K (first A J x), e (k ⊗ₜ second A J x)) := by
  simp only [genericPairsEquiv, AlgEquiv.trans_apply, AlgEquiv.ofBijective_apply,
    tensorInclusion_tmul, Algebra.TensorProduct.prodRight_tmul, AlgEquiv.prodCongr_apply]
  apply Prod.ext
  · change Algebra.TensorProduct.rid A K K (k ⊗ₜ first A J x) = _
    rw [Algebra.TensorProduct.rid_tmul, Algebra.smul_def, mul_comm]
  · rfl

end Generic
end Langlands.BruhatTits.IntegralModels.WeilCongruence

import Langlands.CommutativeAlgebra.IntegralFibre.Taylor
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-! # Injectivity of the truncated Taylor map along a smooth section -/

open TensorProduct MvPolynomial

namespace Langlands.CommutativeAlgebra.IntegralFibre

section TaylorSmooth

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
variable (σ : S →ₐ[A] A) {d : ℕ} (t : Fin d → S)

/-- The truncated polynomial ring `A[T]/(T)^k`. -/
abbrev TPoly (A : Type*) [CommRing A] (d k : ℕ) := MvPolynomial (Fin d) A ⧸ idealOfVars (Fin d) A ^ k

variable (δ : S →ₗ[A] (Fin d → A)) (hδ : ∀ x y, δ (x * y) = σ x • δ y + σ y • δ x)

/-- The first-order Taylor polynomial `σ(s) + ∑ δ_i(s) T_i`. -/
noncomputable def firstOrderPoly : S →ₗ[A] MvPolynomial (Fin d) A :=
  (Algebra.linearMap A (MvPolynomial (Fin d) A)) ∘ₗ σ.toLinearMap +
    ∑ i, (LinearMap.mulRight A (X i)) ∘ₗ (Algebra.linearMap A (MvPolynomial (Fin d) A)) ∘ₗ
      (LinearMap.proj i) ∘ₗ δ

lemma firstOrderPoly_apply (s : S) :
    firstOrderPoly σ δ s = C (σ s) + ∑ i, C (δ s i) * X i := by
  simp [firstOrderPoly, algebraMap_eq]

include hδ in
lemma delta_one : δ 1 = 0 := by
  have := hδ 1 1
  simp only [mul_one, map_one, one_smul] at this
  have h2 : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact this.symm
  exact add_left_cancel h2

include hδ in
lemma firstOrderPoly_mul_sub_mem (x y : S) :
    firstOrderPoly σ δ (x * y) - firstOrderPoly σ δ x * firstOrderPoly σ δ y ∈
      idealOfVars (Fin d) A ^ 2 := by
  set Dx : MvPolynomial (Fin d) A := ∑ i, C (δ x i) * X i
  set Dy : MvPolynomial (Fin d) A := ∑ i, C (δ y i) * X i
  have hD : ∑ i, C (δ (x * y) i) * X i = C (σ x) * Dy + C (σ y) * Dx := by
    simp only [Dx, Dy, hδ, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, add_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]
  rw [firstOrderPoly_apply, firstOrderPoly_apply, firstOrderPoly_apply, hD, map_mul, map_mul]
  change C (σ x) * C (σ y) + (C (σ x) * Dy + C (σ y) * Dx) - (C (σ x) + Dx) * (C (σ y) + Dy) ∈ _
  have : C (σ x) * C (σ y) + (C (σ x) * Dy + C (σ y) * Dx) - (C (σ x) + Dx) * (C (σ y) + Dy) =
      -(Dx * Dy) := by ring
  rw [this, Ideal.neg_mem_iff, pow_two]
  exact Ideal.mul_mem_mul
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

/-- The first-order Taylor expansion `S → A[T]/(T)^2`. -/
noncomputable def firstOrder : S →ₐ[A] TPoly A d 2 :=
  AlgHom.ofLinearMap
    ((Ideal.Quotient.mkₐ A (idealOfVars (Fin d) A ^ 2)).toLinearMap ∘ₗ firstOrderPoly σ δ)
    (by simp [firstOrderPoly_apply, delta_one σ δ hδ])
    (by
      intro x y
      simp only [LinearMap.coe_comp, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk, ← map_mul]
      exact Ideal.Quotient.eq.mpr (firstOrderPoly_mul_sub_mem σ δ hδ x y))

lemma firstOrder_apply (s : S) :
    firstOrder σ δ hδ s = Ideal.Quotient.mk _ (C (σ s) + ∑ i, C (δ s i) * X i) := by
  simp [firstOrder, firstOrderPoly_apply]

omit [Algebra A S] in
lemma mk_idealOfVars_pow_eq_bot (k : ℕ) :
    (idealOfVars (Fin d) A ^ k).map (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ k)) = ⊥ := by
  rw [Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]

omit [Algebra A S] in
lemma factor_ker_isNilpotent {K : ℕ} (hK : 2 ≤ K) :
    IsNilpotent (RingHom.ker (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right hK : idealOfVars (Fin d) A ^ K ≤ idealOfVars (Fin d) A ^ 2))) := by
  refine ⟨K, ?_⟩
  have : RingHom.ker (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right hK : idealOfVars (Fin d) A ^ K ≤ idealOfVars (Fin d) A ^ 2)) =
      (idealOfVars (Fin d) A ^ 2).map (Ideal.Quotient.mk _) :=
    Ideal.Quotient.factor_ker (Ideal.pow_le_pow_right hK)
  rw [this, ← Ideal.map_pow, ← pow_mul, Ideal.zero_eq_bot, eq_bot_iff]
  calc _ ≤ (idealOfVars (Fin d) A ^ K).map (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ K)) :=
        Ideal.map_mono (Ideal.pow_le_pow_right (by omega))
    _ = ⊥ := mk_idealOfVars_pow_eq_bot K

section Lift

variable (h : S) (hh : IsUnit (σ h))
include hh hδ

lemma firstOrder_isUnit_powers (y : Submonoid.powers h) : IsUnit (firstOrder σ δ hδ y) := by
  obtain ⟨n, hn⟩ := y.2
  rw [← hn, map_pow]
  apply IsUnit.pow
  have : firstOrder σ δ hδ h = Ideal.Quotient.mk _ (C (σ h)) +
      Ideal.Quotient.mk _ (∑ i, C (δ h i) * X i) := by
    rw [firstOrder_apply, map_add]
  rw [this]
  refine IsNilpotent.isUnit_add_left_of_commute ?_ ?_ (Commute.all _ _)
  swap
  · exact (hh.map C).map _
  refine ⟨2, ?_⟩
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem, pow_two, pow_two]
  exact Ideal.mul_mem_mul
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
    (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))

variable [Algebra.FormallySmooth A (Localization.Away h)]

/-- A lift of the first-order Taylor expansion to `A[T]/(T)^K`, using formal smoothness of
`S_h`. -/
noncomputable def taylorLift (K : ℕ) (hK : 2 ≤ K) : S →ₐ[A] TPoly A d K :=
  (Algebra.FormallySmooth.liftOfSurjective
    (IsLocalization.liftAlgHom (M := Submonoid.powers h) (S := Localization.Away h)
      (f := firstOrder σ δ hδ) (firstOrder_isUnit_powers σ δ hδ h hh))
    (Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right hK : idealOfVars (Fin d) A ^ K ≤ idealOfVars (Fin d) A ^ 2))
    (fun x ↦ Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right hK) x)
    (factor_ker_isNilpotent hK)).comp
    (IsScalarTower.toAlgHom A S (Localization.Away h))

lemma factor_taylorLift (K : ℕ) (hK : 2 ≤ K) (s : S) :
    Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right hK : idealOfVars (Fin d) A ^ K ≤ idealOfVars (Fin d) A ^ 2)
      (taylorLift σ δ hδ h hh K hK s) = firstOrder σ δ hδ s := by
  rw [taylorLift, AlgHom.comp_apply]
  refine (Algebra.FormallySmooth.liftOfSurjective_apply _ _ _ _ _).trans ?_
  exact IsLocalization.lift_eq (M := Submonoid.powers h) (S := Localization.Away h) _ s

/-- **Injectivity of the truncated Taylor map** along a section `σ` lying in the formally
smooth locus, for coordinates `t` dual to a derivation `δ` at `σ`. -/
theorem theta_injective_of_formallySmooth (ht : ∀ i, σ (t i) = 0)
    (hδt : ∀ i, δ (t i) = Pi.single i 1) (k : ℕ) : Function.Injective (theta σ t k) := by
  have hK : 2 ≤ k + 2 := by omega
  have hkK : k ≤ k + 2 := by omega
  let Ψ := taylorLift σ δ hδ h hh (k + 2) hK
  let fac := Ideal.Quotient.factorₐ A
    (Ideal.pow_le_pow_right hkK : idealOfVars (Fin d) A ^ (k + 2) ≤ idealOfVars (Fin d) A ^ k)
  let ψ := fac.comp Ψ
  have hJ : ∀ j ∈ RingHom.ker σ, ∃ p ∈ idealOfVars (Fin d) A,
      Ψ j = Ideal.Quotient.mk _ p := by
    intro j hj
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (Ψ j)
    refine ⟨p, ?_, hp.symm⟩
    have h2 := factor_taylorLift σ δ hδ h hh (k + 2) hK j
    rw [firstOrder_apply, RingHom.mem_ker.mp hj, map_zero, zero_add] at h2
    have h3 : Ideal.Quotient.mk (idealOfVars (Fin d) A ^ 2) p =
        Ideal.Quotient.mk _ (∑ i, C (δ j i) * X i) := by
      rw [← h2]
      change _ = Ideal.Quotient.factorₐ A _ (Ψ j)
      rw [← hp]
      rfl
    have h4 := Ideal.Quotient.eq.mp h3
    have : p = (p - ∑ i, C (δ j i) * X i) + ∑ i, C (δ j i) * X i := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero h4)
      (Ideal.sum_mem _ fun i _ ↦ Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩))
  have hker : RingHom.ker σ ^ k ≤ RingHom.ker ψ := by
    have h1 : RingHom.ker σ ≤
        ((idealOfVars (Fin d) A).map (Ideal.Quotient.mk (idealOfVars (Fin d) A ^ (k + 2)))).comap
          Ψ := by
      intro j hj
      obtain ⟨p, hp, e⟩ := hJ j hj
      rw [Ideal.mem_comap, e]
      exact Ideal.mem_map_of_mem _ hp
    refine (Ideal.pow_right_mono h1 k).trans ((Ideal.le_comap_pow _ k).trans ?_)
    intro x hx
    rw [Ideal.mem_comap, ← Ideal.map_pow,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hx
    obtain ⟨p, hp, e⟩ := hx
    rw [RingHom.mem_ker]
    change fac (Ψ x) = 0
    rw [← e]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  let ψbar : (S ⧸ RingHom.ker σ ^ k) →ₐ[A] TPoly A d k :=
    Ideal.Quotient.liftₐ (RingHom.ker σ ^ k) ψ (fun a ha ↦ hker ha)
  choose q hq using fun i ↦ Ideal.Quotient.mk_surjective (Ψ (t i))
  refine theta_injective_of_lift σ t k ψbar q ?_ ?_
  · intro i
    change fac (Ψ (t i)) = _
    rw [← hq i]
    rfl
  · intro i
    have h2 := factor_taylorLift σ δ hδ h hh (k + 2) hK (t i)
    rw [firstOrder_apply, ht i, hδt i, map_zero, zero_add] at h2
    have h3 : Ideal.Quotient.mk (idealOfVars (Fin d) A ^ 2) (q i) =
        Ideal.Quotient.mk _ (X i) := by
      have e : ∑ j, C ((Pi.single i (1 : A) : Fin d → A) j) * X j = (X i : MvPolynomial (Fin d) A) := by
        rw [Finset.sum_eq_single i]
        · simp
        · intro j _ hj; simp [hj]
        · simp
      rw [← e, ← h2]
      change _ = Ideal.Quotient.factorₐ A _ (Ψ (t i))
      rw [← hq i]
      rfl
    exact Ideal.Quotient.eq.mp h3

end Lift

end TaylorSmooth

end Langlands.CommutativeAlgebra.IntegralFibre

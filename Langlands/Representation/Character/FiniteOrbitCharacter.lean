import Langlands.Representation.Character.CentralIdempotent
import Mathlib.Algebra.Group.AddChar

/-! # Finite character sums under an exponential change of variables -/

noncomputable section

namespace Langlands.Representation.Character

open scoped MonoidAlgebra

universe u

variable {A K : Type*} [AddCommGroup A] [Fintype A] [Group K] [Fintype K]

private theorem additiveCharacterSum_convolution (S : Finset (AddChar A ℂ)) (z : A) :
    (∑ x : A, (∑ ψ ∈ S, ψ x) * (∑ η ∈ S, η (z - x))) =
      (Fintype.card A : ℂ) * ∑ ψ ∈ S, ψ z := by
  classical
  have h (ψ η : AddChar A ℂ) :
      (∑ x : A, ψ x * η (z - x)) =
        if ψ = η then (Fintype.card A : ℂ) * ψ z else 0 := by
    have hsum : (∑ x : A, ψ x * η (z - x)) = (∑ x : A, (ψ - η) x) * η z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro x _
      rw [sub_eq_add_neg, AddChar.map_add_eq_mul, AddChar.sub_apply]
      rw [mul_comm (η z) (η (-x)), mul_assoc]
    rw [hsum, AddChar.sum_eq_ite]
    by_cases h' : ψ = η
    · simp [h']
    · simp only [ite_eq_right (sub_ne_zero.mpr h'), ite_eq_right h', zero_mul]
  calc
    _ = ∑ ψ ∈ S, ∑ η ∈ S, ∑ x : A, ψ x * η (z - x) := by
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ψ hψ
      simp_rw [h]
      rw [Finset.sum_eq_single_of_mem ψ hψ, ite_eq_left rfl]
      intro η _ hη
      exact ite_eq_right (Ne.symm hη)

private theorem finiteConvolution_change (E : A ≃ K) (Φ : A × A ≃ A × A)
    (hΦ : ∀ x : A × A, E ((Φ x).1 + (Φ x).2) = E x.1 * E x.2)
    (f : A → ℂ)
    (hf : ∀ x : A × A, f (Φ x).1 = f x.1 ∧ f (Φ x).2 = f x.2) (z : A) :
    (∑ g : K, f (E.symm g) * f (E.symm (g⁻¹ * E z))) =
      ∑ x : A, f x * f (z - x) := by
  classical
  let p (x : A × A) := if E x.1 * E x.2 = E z then f x.1 * f x.2 else 0
  let q (x : A × A) := if x.1 + x.2 = z then f x.1 * f x.2 else 0
  calc
    _ = ∑ x : A × A, p x := by
      rw [Fintype.sum_prod_type]
      apply Fintype.sum_equiv E.symm
      intro g
      simp only [p, Equiv.apply_symm_apply]
      have h (y : A) : g * E y = E z ↔ y = E.symm (g⁻¹ * E z) := by
        rw [eq_inv_mul_iff_mul_eq.symm, ← Equiv.apply_eq_iff_eq E, E.apply_symm_apply]
      simp_rw [h]
      simp
    _ = ∑ x : A × A, q x := by
      apply Fintype.sum_equiv Φ
      intro x
      simp only [p, q, ← hΦ x, Equiv.apply_eq_iff_eq, (hf x).1, (hf x).2]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      have h (y : A) : x + y = z ↔ y = z - x := by
        rw [add_comm x y, eq_sub_iff_add_eq]
      simp [q, h]

/-- A finite additive character sum invariant under conjugation gives a group
character when a change of variables straightens products while preserving both
values of the sum. -/
def FiniteOrbitCharacterStatement {A : Type*} {K : Type u}
    [AddCommGroup A] [Fintype A] [Group K] [Fintype K]
    (E : A ≃ K) (Φ : A × A ≃ A × A) (S : Finset (AddChar A ℂ)) : Prop :=
  let f (x : A) := ∑ ψ ∈ S, ψ x
  (∀ g k : K, f (E.symm (g * k * g⁻¹)) = f (E.symm k)) →
  (∀ x : A × A, E ((Φ x).1 + (Φ x).2) = E x.1 * E x.2) →
  (∀ x : A × A, f (Φ x).1 = f x.1 ∧ f (Φ x).2 = f x.2) →
  ∃ (W : Type u) (_ : AddCommGroup W) (_ : Module ℂ W) (_ : FiniteDimensional ℂ W)
    (ρ : Representation ℂ K W),
    ∀ x, ρ.character (E x) = f x

theorem finiteOrbitCharacter (E : A ≃ K) (Φ : A × A ≃ A × A) (S : Finset (AddChar A ℂ)) :
    FiniteOrbitCharacterStatement E Φ S := by
  classical
  intro hconj hΦ hf
  let f (x : A) := ∑ ψ ∈ S, ψ x
  let d : ℂ := Fintype.card K
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hcard : (Fintype.card A : ℂ) = d := congrArg (Nat.cast : ℕ → ℂ) (Fintype.card_congr E)
  let e : ℂ[K] := MonoidAlgebra.ofCoeff
    (Finsupp.equivFunOnFinite.symm (fun g => d⁻¹ * f (E.symm g)))
  have he (g : K) : e.coeff g = d⁻¹ * f (E.symm g) := by simp [e]
  have heC : e ∈ Subring.center ℂ[K] := by
    rw [Subring.mem_center_iff]
    intro a
    induction a using MonoidAlgebra.induction_on with
    | of g =>
      apply MonoidAlgebra.ext
      apply Finsupp.ext
      intro k
      rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply,
        MonoidAlgebra.coeff_mul_single_apply, one_mul, mul_one, he, he]
      have h := hconj g (g⁻¹ * k)
      simpa only [mul_inv_cancel_left] using congrArg (d⁻¹ * ·) h.symm
    | add a b ha hb => rw [add_mul, mul_add, ha, hb]
    | smul c a ha => rw [smul_mul_assoc, ha, mul_smul_comm]
  have heI : IsIdempotentElem e := by
    change e * e = e
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    obtain ⟨z, rfl⟩ := E.surjective g
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (fun _ => zero_mul _)]
    simp only [he, Equiv.symm_apply_apply]
    simp_rw [mul_mul_mul_comm, ← Finset.mul_sum]
    rw [finiteConvolution_change E Φ hΦ f hf, additiveCharacterSum_convolution S, hcard]
    field_simp
    rfl
  obtain ⟨W, _, _, _, ρ, hρ⟩ := centralIdempotentCharacter K e heC heI
  refine ⟨Module.Dual ℂ W, inferInstance, inferInstance, inferInstance, ρ.dual, fun x => ?_⟩
  rw [Representation.char_dual, hρ, inv_inv, he, Equiv.symm_apply_apply,
    ← mul_assoc, mul_inv_cancel₀ hd, one_mul]

end Langlands.Representation.Character

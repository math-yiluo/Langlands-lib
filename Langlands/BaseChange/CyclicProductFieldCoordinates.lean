import Langlands.BaseChange.CyclicAlgebraStructure
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-! # Cyclic coordinates on a given product of fields -/

noncomputable section

namespace Langlands.BaseChange

open scoped BigOperators

universe u v w t

variable {F : Type u} [Field F] {I : Type v} [Fintype I]
  {A : I → Type w} [∀ i, Field (A i)] [∀ i, Algebra F (A i)]

private theorem exists_algEquiv_factor_of_surjective {B : Type t} [Field B] [Algebra F B]
    (f : (∀ i, A i) →ₐ[F] B) (hf : Function.Surjective f) :
    ∃ (i : I) (e : A i ≃ₐ[F] B), ∀ x, f x = e (x i) := by
  classical
  have hsum : (∑ i : I, Pi.single i (1 : A i)) = (1 : ∀ i, A i) := by
    funext j
    rw [Finset.sum_apply, Finset.sum_pi_single]
    simp
  obtain ⟨i, hi⟩ : ∃ i : I, f (Pi.single i (1 : A i)) ≠ 0 := by
    by_contra! h
    have h' := congrArg f hsum
    rw [map_sum, map_one, Finset.sum_eq_zero (fun j _ ↦ h j)] at h'
    exact zero_ne_one h'
  have hselect (x : ∀ j, A j) : Pi.single i (1 : A i) * x = Pi.single i (x i) := by
    funext j
    by_cases hij : j = i
    · subst j
      simp
    · simp [Pi.single_eq_of_ne hij]
  have hone : f (Pi.single i (1 : A i)) = 1 := by
    have h := congrArg f (hselect (Pi.single i (1 : A i)))
    rw [map_mul, Pi.single_eq_same] at h
    exact mul_right_cancel₀ hi (h.trans (one_mul _).symm)
  have happ (x : ∀ j, A j) : f (Pi.single i (x i)) = f x := by
    rw [← hselect x, map_mul, hone, one_mul]
  let g : A i →ₐ[F] B :=
    { toFun := fun a ↦ f (Pi.single i a)
      map_zero' := by simp
      map_one' := hone
      map_add' := by
        intro a b
        rw [show Pi.single i (a + b) = Pi.single i a + Pi.single i b by
          funext j
          by_cases hij : j = i
          · subst j
            simp
          · simp [Pi.single_eq_of_ne hij], map_add]
      map_mul' := by
        intro a b
        rw [show Pi.single i (a * b) = Pi.single i a * Pi.single i b by
          funext j
          by_cases hij : j = i
          · subst j
            simp
          · simp [Pi.single_eq_of_ne hij], map_mul]
      commutes' := fun a ↦ (happ (algebraMap F (∀ j, A j) a)).trans (f.commutes a) }
  refine ⟨i, AlgEquiv.ofBijective g ⟨g.injective, ?_⟩, fun x ↦ (happ x).symm⟩
  intro b
  obtain ⟨x, rfl⟩ := hf b
  exact ⟨x i, happ x⟩

variable {E : Type t} [CommRing E] [Algebra F E] {σ : E ≃ₐ[F] E} {l : ℕ}

/-- If a cyclic algebra is already identified with a finite product of fields,
one of those fields can be chosen for all its cyclic coordinates. -/
theorem exists_cyclicProductFieldCoordinates (hσ : IsCyclicAlgebra σ l)
    (c : E ≃ₐ[F] ∀ i, A i) :
    ∃ (i : I) (m d : ℕ) (τ : A i ≃ₐ[F] A i) (e : E ≃ₐ[F] (Fin (m + 1) → A i)),
      l = (m + 1) * d ∧ IsCyclicAlgebra τ d ∧ (∀ x, e x 0 = c x i) ∧
        (∀ (x : E) (j : Fin m), e (σ x) j.castSucc = e x j.succ) ∧
        ∀ x : E, e (σ x) (Fin.last m) = τ (e x 0) := by
  obtain ⟨data⟩ := CyclicAlgebraStructure.exists_coordinates hσ
  let : data.m.asIdeal.IsMaximal := data.m.isMaximal
  let Q := E ⧸ data.m.asIdeal
  let q : E →ₐ[F] Q := Ideal.Quotient.mkₐ F data.m.asIdeal
  let : Field Q := Ideal.Quotient.field _
  obtain ⟨i, a, ha⟩ := exists_algEquiv_factor_of_surjective (q.comp c.symm.toAlgHom)
    ((Ideal.Quotient.mkₐ_surjective F _).comp c.symm.surjective)
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero data.r_pos.ne'
  let reindex : Fin (m + 1) ≃ Fin data.r := finCongr hm.symm
  let e : E ≃ₐ[F] (Fin (m + 1) → A i) :=
    data.coords.trans ((AlgEquiv.piCongrLeft F (fun _ : Fin data.r ↦ Q) reindex).symm.trans
      (AlgEquiv.piCongrRight fun _ : Fin (m + 1) ↦ a.symm))
  let τ := a.symm.autCongr data.τ
  have hcomp (x : E) (j : Fin (m + 1)) :
      a (e x j) = q ((σ ^ j.val) x) := by
    change a (a.symm (data.coords x (reindex j))) = _
    rw [a.apply_symm_apply, data.coords_apply]
    rfl
  have hcyclic : IsCyclicAlgebra τ data.d := by
    let : Module.Finite F Q := data.cyclic.1
    refine ⟨Module.Finite.of_surjective a.symm.toLinearMap a.symm.surjective,
      a.toLinearEquiv.finrank_eq.trans data.cyclic.2.1, inferInstance, ?_, ?_⟩
    · exact (a.symm.autCongr.orderOf_eq data.τ).trans data.cyclic.2.2.2.1
    · intro x hx
      have h := congrArg a hx
      change a (a.symm (data.τ (a x))) = a x at h
      rw [a.apply_symm_apply] at h
      obtain ⟨b, hb⟩ := data.cyclic.2.2.2.2 _ h
      exact ⟨b, a.injective ((a.commutes b).trans hb)⟩
  refine ⟨i, m, data.d, τ, e, data.degree_eq.trans (congrArg (· * data.d) hm),
    hcyclic, ?_, ?_, ?_⟩
  · intro x
    apply a.injective
    have h := ha (c x)
    change q (c.symm (c x)) = a (c x i) at h
    rw [c.symm_apply_apply] at h
    simpa only [hcomp, Fin.val_zero, pow_zero, AlgEquiv.one_apply] using h
  · intro x j
    apply a.injective
    rw [hcomp, hcomp, Fin.val_castSucc, Fin.val_succ, pow_succ, AlgEquiv.mul_apply]
  · intro x
    apply a.injective
    change a (e (σ x) (Fin.last m)) = a (a.symm (data.τ (a (e x 0))))
    rw [a.apply_symm_apply, hcomp, hcomp, Fin.val_last, Fin.val_zero, pow_zero, AlgEquiv.one_apply]
    have h := data.wrap x
    change q ((σ ^ data.r) x) = data.τ (q x) at h
    rw [hm, pow_succ, AlgEquiv.mul_apply] at h
    exact h

end Langlands.BaseChange

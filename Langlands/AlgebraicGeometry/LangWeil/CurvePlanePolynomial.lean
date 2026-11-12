import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Variables
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.Algebra.Polynomial.Eval.Irreducible

/-!
# Plane polynomials of monic polynomials over a one-variable polynomial ring

A polynomial `F` in `W` over `R[Z]` gives the plane polynomial `planePoly F` in the variables
`X 0 = W` and `X 1 = Z`. Over a field `κ`, algebra maps from `AdjoinRoot F` to `κ` are the
zeros of the plane polynomial, and the zeros over the zeros of a nonzero polynomial in `Z`
are bounded by the product of the degrees.
-/

universe u v

namespace Langlands.AlgebraicGeometry.LangWeil.CurvePlane

open MvPolynomial

section General

variable {R : Type u} [CommRing R]

/-- The plane polynomial of `F`, in the variables `X 0 = W` and `X 1 = Z`. -/
noncomputable def planePoly (F : Polynomial (MvPolynomial (Fin 1) R)) : MvPolynomial (Fin 2) R :=
  (finSuccEquiv R 1).symm F

theorem finSuccEquiv_planePoly (F : Polynomial (MvPolynomial (Fin 1) R)) :
    finSuccEquiv R 1 (planePoly F) = F :=
  (finSuccEquiv R 1).apply_symm_apply F

theorem eval_planePoly (F : Polynomial (MvPolynomial (Fin 1) R)) (v : Fin 2 → R) :
    eval v (planePoly F) = (F.map (eval (Fin.tail v))).eval (v 0) := by
  conv_lhs => rw [← Fin.cons_self_tail v]
  rw [eval_eq_eval_mv_eval', finSuccEquiv_planePoly]

theorem degreeOf_zero_planePoly (F : Polynomial (MvPolynomial (Fin 1) R)) :
    (planePoly F).degreeOf 0 = F.natDegree := by
  rw [← natDegree_finSuccEquiv, finSuccEquiv_planePoly]

theorem finSuccEquiv_map {S : Type v} [CommRing S] (f : R →+* S)
    (P : MvPolynomial (Fin 2) R) :
    finSuccEquiv S 1 (map f P) = (finSuccEquiv R 1 P).map (map f) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq, Polynomial.map_add]
  | mul_X p i hp =>
    rw [map_mul, map_X, map_mul, map_mul, hp, Polynomial.map_mul]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_X_zero]
    · simp [finSuccEquiv_X_succ]

theorem map_planePoly {S : Type v} [CommRing S] (f : R →+* S)
    (F : Polynomial (MvPolynomial (Fin 1) R)) :
    map f (planePoly F) = planePoly (F.map (map f)) := by
  apply (finSuccEquiv S 1).injective
  rw [finSuccEquiv_map, finSuccEquiv_planePoly, finSuccEquiv_planePoly]

theorem irreducible_planePoly_iff (F : Polynomial (MvPolynomial (Fin 1) R)) :
    Irreducible (planePoly F) ↔ Irreducible F :=
  MulEquiv.irreducible_iff (finSuccEquiv R 1).symm.toMulEquiv

theorem degreeOf_map_le {σ : Type*} {S : Type v} [CommRing S] (f : R →+* S)
    (P : MvPolynomial σ R) (i : σ) : (map f P).degreeOf i ≤ P.degreeOf i := by
  rw [degreeOf_le_iff]
  intro m hm
  exact le_degreeOf_of_mem_support i (support_map_subset f P hm)

/-- The coefficients of `F` have `Z`-degree at most the `Z`-degree of `planePoly F`. -/
theorem degreeOf_coeff_le (F : Polynomial (MvPolynomial (Fin 1) R)) (i : ℕ) :
    (F.coeff i).degreeOf 0 ≤ (planePoly F).degreeOf 1 := by
  have h := degreeOf_coeff_finSuccEquiv (planePoly F) 0 i
  rwa [finSuccEquiv_planePoly] at h

end General

section Field

variable {κ : Type u} [Field κ]

omit [Field κ] in
theorem tail_eq_const (v : Fin 2 → κ) : Fin.tail v = fun _ => v 1 := by
  funext i
  rw [Fin.fin_one_eq_zero i]
  rfl

/-- An algebra map out of `AdjoinRoot F` restricts to evaluation on the coefficients. -/
theorem algHom_of_eq_eval (F : Polynomial (MvPolynomial (Fin 1) κ))
    (χ : AdjoinRoot F →ₐ[κ] κ) (p : MvPolynomial (Fin 1) κ) :
    χ (AdjoinRoot.of F p) = eval (fun _ => χ (AdjoinRoot.of F (X 0))) p := by
  have h : χ.comp (AdjoinRoot.ofAlgHom κ F) =
      aeval (fun _ => χ (AdjoinRoot.of F (X 0))) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [Fin.fin_one_eq_zero i, aeval_X]
    rfl
  have h' := congrArg (fun ψ : MvPolynomial (Fin 1) κ →ₐ[κ] κ => ψ p) h
  simpa [coe_aeval_eq_eval] using h'

theorem eval_planePoly_algHom (F : Polynomial (MvPolynomial (Fin 1) κ))
    (χ : AdjoinRoot F →ₐ[κ] κ) :
    eval ![χ (AdjoinRoot.root F), χ (AdjoinRoot.of F (X 0))] (planePoly F) = 0 := by
  rw [eval_planePoly, Polynomial.eval_map, tail_eq_const]
  change Polynomial.eval₂ (eval (fun _ => χ (AdjoinRoot.of F (X 0)))) (χ (AdjoinRoot.root F)) F = 0
  have hring : (χ : AdjoinRoot F →+* κ).comp (AdjoinRoot.of F) =
      eval (fun _ => χ (AdjoinRoot.of F (X 0))) :=
    RingHom.ext fun p => algHom_of_eq_eval F χ p
  have h := congrArg χ (AdjoinRoot.eval₂_root F)
  rw [map_zero] at h
  have h2 := Polynomial.hom_eval₂ (p := F) (f := AdjoinRoot.of F)
    (g := (χ : AdjoinRoot F →+* κ)) (x := AdjoinRoot.root F)
  rw [← hring]
  exact h2.symm.trans h

/-- Algebra maps from `AdjoinRoot F` to `κ` are the zeros of the plane polynomial. -/
noncomputable def algHomEquivZeros (F : Polynomial (MvPolynomial (Fin 1) κ)) :
    (AdjoinRoot F →ₐ[κ] κ) ≃ {v : Fin 2 → κ // eval v (planePoly F) = 0} where
  toFun χ := ⟨![χ (AdjoinRoot.root F), χ (AdjoinRoot.of F (X 0))], eval_planePoly_algHom F χ⟩
  invFun v := AdjoinRoot.liftAlgHom F (aeval (Fin.tail v.1)) (v.1 0) (by
    rw [coe_aeval_eq_eval]
    have h := v.2
    rw [eval_planePoly, Polynomial.eval_map] at h
    exact h)
  left_inv χ := by
    apply AdjoinRoot.algHom_ext'
    · apply MvPolynomial.algHom_ext
      intro i
      rw [Fin.fin_one_eq_zero i]
      simp [AdjoinRoot.liftAlgHom_of]
    · simp [AdjoinRoot.liftAlgHom_root]
  right_inv v := by
    apply Subtype.ext
    funext i
    fin_cases i
    · exact AdjoinRoot.liftAlgHom_root ..
    · change AdjoinRoot.liftAlgHom F (aeval (Fin.tail v.1)) (v.1 0) _ (AdjoinRoot.of F (X 0)) =
        v.1 1
      rw [AdjoinRoot.liftAlgHom_of, aeval_X]
      rfl

theorem algHomEquivZeros_apply_coe (F : Polynomial (MvPolynomial (Fin 1) κ))
    (χ : AdjoinRoot F →ₐ[κ] κ) (i : Fin 2) :
    ((algHomEquivZeros F χ : {v : Fin 2 → κ // eval v (planePoly F) = 0}) : Fin 2 → κ) i =
      ![χ (AdjoinRoot.root F), χ (AdjoinRoot.of F (X 0))] i := rfl

theorem algHom_of_eq_eval_algHomEquivZeros (F : Polynomial (MvPolynomial (Fin 1) κ))
    (χ : AdjoinRoot F →ₐ[κ] κ) (p : MvPolynomial (Fin 1) κ) :
    χ (AdjoinRoot.of F p) =
      eval (fun _ => ((algHomEquivZeros F χ : {v : Fin 2 → κ // eval v (planePoly F) = 0}) :
        Fin 2 → κ) 1) p :=
  algHom_of_eq_eval F χ p

/-- The zeros of a plane polynomial of a monic `F` over the roots of a nonzero polynomial in
`Z` number at most the product of the degrees. -/
theorem card_zeros_planePoly_root_le [Finite κ] (F : Polynomial (MvPolynomial (Fin 1) κ))
    (hF : F.Monic) (h : Polynomial κ) (hh : h ≠ 0) :
    Nat.card {v : Fin 2 → κ // eval v (planePoly F) = 0 ∧ h.eval (v 1) = 0} ≤
      h.natDegree * F.natDegree := by
  classical
  let β : h.rootSet κ → Type u := fun t => (F.map (eval (fun _ => (t : κ)))).rootSet κ
  have hmon (t : κ) : (F.map (eval (fun _ => t))).Monic := hF.map _
  let ι : {v : Fin 2 → κ // eval v (planePoly F) = 0 ∧ h.eval (v 1) = 0} → Σ t, β t :=
    fun v => ⟨⟨v.1 1, by
      rw [Polynomial.mem_rootSet_of_ne hh, Polynomial.coe_aeval_eq_eval]
      exact v.2.2⟩, ⟨v.1 0, by
      rw [Polynomial.mem_rootSet_of_ne (hmon _).ne_zero, Polynomial.coe_aeval_eq_eval]
      have h0 := v.2.1
      rwa [eval_planePoly, tail_eq_const] at h0⟩⟩
  have hι : Function.Injective ι := by
    intro v w hvw
    have h1 : v.1 1 = w.1 1 := congrArg (fun s : Σ t, β t => ((s.1 : κ))) hvw
    have h0 : v.1 0 = w.1 0 := congrArg (fun s : Σ t, β t => ((s.2 : κ))) hvw
    apply Subtype.ext
    funext i
    fin_cases i
    · exact h0
    · exact h1
  calc Nat.card {v : Fin 2 → κ // eval v (planePoly F) = 0 ∧ h.eval (v 1) = 0}
      ≤ Nat.card (Σ t, β t) := Nat.card_le_card_of_injective ι hι
    _ = ∑ t, Nat.card (β t) := Nat.card_sigma
    _ ≤ ∑ _t : h.rootSet κ, F.natDegree := by
      apply Finset.sum_le_sum
      intro t _
      rw [Nat.card_coe_set_eq]
      exact (Polynomial.ncard_rootSet_le _ κ).trans (hF.natDegree_map _).le
    _ = Nat.card (h.rootSet κ) * F.natDegree := by
      rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]
    _ ≤ h.natDegree * F.natDegree := by
      apply Nat.mul_le_mul_right
      rw [Nat.card_coe_set_eq]
      exact Polynomial.ncard_rootSet_le h κ

/-- The diagonal line `X 0 = X 1`. -/
noncomputable def diagonal : MvPolynomial (Fin 2) κ := X 0 - X 1

theorem map_diagonal {L : Type v} [Field L] (f : κ →+* L) :
    map f (diagonal (κ := κ)) = diagonal := by
  simp [diagonal]

theorem irreducible_diagonal : Irreducible (diagonal (κ := κ)) := by
  rw [← MulEquiv.irreducible_iff (finSuccEquiv κ 1).toMulEquiv]
  have h : finSuccEquiv κ 1 (diagonal (κ := κ)) = Polynomial.X - Polynomial.C (X 0) := by
    rw [diagonal, map_sub, finSuccEquiv_X_zero]
    exact congrArg _ (finSuccEquiv_X_succ (j := 0))
  change Irreducible (finSuccEquiv κ 1 (diagonal (κ := κ)))
  rw [h]
  exact Polynomial.irreducible_X_sub_C _

theorem degreeOf_zero_diagonal : (diagonal (κ := κ)).degreeOf 0 = 1 := by
  rw [diagonal, sub_eq_add_neg, degreeOf_add_eq_of_degreeOf_lt] <;>
    simp [degreeOf_neg, degreeOf_X]

theorem degreeOf_one_diagonal : (diagonal (κ := κ)).degreeOf 1 = 1 := by
  rw [diagonal, sub_eq_neg_add, degreeOf_add_eq_of_degreeOf_lt] <;>
    simp [degreeOf_neg, degreeOf_X]

theorem card_zeros_diagonal :
    Nat.card {v : Fin 2 → κ // eval v (diagonal (κ := κ)) = 0} = Nat.card κ := by
  apply Nat.card_congr
  refine
    { toFun := fun v => v.1 0
      invFun := fun t => ⟨![t, t], by simp [diagonal]⟩
      left_inv := fun v => ?_
      right_inv := fun t => rfl }
  apply Subtype.ext
  have hv : v.1 0 = v.1 1 := by
    have := v.2
    simp only [diagonal, map_sub, eval_X] at this
    exact sub_eq_zero.mp this
  funext i
  fin_cases i
  · rfl
  · exact hv

/-- If the plane polynomial of a monic `F` is absolutely irreducible and does not involve `Z`,
its zeros are a line: there are exactly as many as elements of `κ`. -/
theorem card_zeros_planePoly_of_degreeOf_one_eq_zero
    (F : Polynomial (MvPolynomial (Fin 1) κ)) (hF : F.Monic)
    (hirr : Irreducible (map (algebraMap κ (AlgebraicClosure κ)) (planePoly F)))
    (hdeg : (planePoly F).degreeOf 1 = 0) :
    Nat.card {v : Fin 2 → κ // eval v (planePoly F) = 0} = Nat.card κ := by
  classical
  have hconst (i : ℕ) : F.coeff i = C ((F.coeff i).coeff 0) := by
    rw [← totalDegree_eq_zero_iff_eq_C, totalDegree_eq_zero_iff]
    intro m hm x
    rw [Fin.fin_one_eq_zero x]
    have := (le_degreeOf_of_mem_support 0 hm).trans ((degreeOf_coeff_le F i).trans hdeg.le)
    omega
  have hevalF (x : Fin 1 → κ) : F.map (eval x) = F.map (eval (fun _ => 0)) := by
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_map, hconst i, eval_C, eval_C]
  let f₀ : Polynomial κ := F.map (eval (fun _ => 0))
  have hf₀ : f₀.Monic := hF.map _
  let Ω := AlgebraicClosure κ
  have hFΩ : Irreducible (F.map (map (algebraMap κ Ω))) := by
    rw [map_planePoly, irreducible_planePoly_iff] at hirr
    exact hirr
  have hFΩeq : F.map (map (algebraMap κ Ω)) = (f₀.map (algebraMap κ Ω)).map C := by
    ext i : 1
    rw [Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map, Polynomial.coeff_map,
      hconst i, map_C, eval_C]
  rw [hFΩeq] at hFΩ
  have hf₀Ω : Irreducible (f₀.map (algebraMap κ Ω)) :=
    Polynomial.Monic.irreducible_of_irreducible_map C _ (hf₀.map _) hFΩ
  have hdeg₁ : f₀.natDegree = 1 := by
    have := IsAlgClosed.degree_eq_one_of_irreducible Ω hf₀Ω
    rw [Polynomial.degree_map] at this
    exact Polynomial.natDegree_eq_of_degree_eq_some this
  obtain ⟨c, hc⟩ : ∃ c, f₀ = Polynomial.X + Polynomial.C c := by
    refine ⟨f₀.coeff 0, ?_⟩
    rw [Polynomial.Monic.eq_X_add_C hf₀ hdeg₁]
    simp
  have hzero (v : Fin 2 → κ) : eval v (planePoly F) = v 0 + c := by
    rw [eval_planePoly, hevalF, show F.map (eval fun _ => 0) = f₀ from rfl, hc]
    simp
  apply Nat.card_congr
  refine
    { toFun := fun v => v.1 1
      invFun := fun t => ⟨![-c, t], by rw [hzero]; simp⟩
      left_inv := fun v => ?_
      right_inv := fun t => rfl }
  apply Subtype.ext
  have hv : v.1 0 = -c := eq_neg_of_add_eq_zero_left ((hzero v.1).symm.trans v.2)
  funext i
  fin_cases i
  · exact hv.symm
  · rfl

end Field

end Langlands.AlgebraicGeometry.LangWeil.CurvePlane

import Langlands.AlgebraicGeometry.LangWeil.PlaneCurveSeparableModel
import Mathlib.Algebra.MvPolynomial.Nilpotent
import Mathlib.Algebra.Polynomial.Degree.SmallDegree
import Mathlib.Algebra.Polynomial.Degree.Units
import Mathlib.Algebra.Polynomial.Roots

/-!
# Linear fibres of an absolutely irreducible plane curve

A curve linear in its second coordinate has one rational point above every
abscissa at which its leading coefficient is nonzero, and no point above the
other abscissae. The exceptional abscissae are roots of a nonzero polynomial
whose degree is bounded by the first partial degree.
-/

noncomputable section

universe u

namespace Langlands.AlgebraicGeometry.LangWeil

open MvPolynomial

theorem planeCurve_eval_unique {R : Type u} [CommRing R]
    (f : MvPolynomial (Fin 1) R) (x : R) :
    eval (fun _ : Fin 1 => x) f =
      Polynomial.eval x (uniqueAlgEquiv R (Fin 1) f) := by
  exact (eval₂_const_uniqueAlgEquiv (f := f) (φ := RingHom.id R) (a := x)).symm

theorem planeCurve_natDegree_unique_le {R : Type u} [CommRing R]
    (f : MvPolynomial (Fin 1) R) :
    (uniqueAlgEquiv R (Fin 1) f).natDegree ≤ f.degreeOf 0 := by
  classical
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [coeff_uniqueAlgEquiv]
  by_contra hc
  have hm : Finsupp.single (default : Fin 1) n ∈ f.support := mem_support_iff.mpr hc
  have hle := monomial_le_degreeOf (0 : Fin 1) hm
  have hd : (default : Fin 1) = 0 := Subsingleton.elim _ _
  simp only [hd, Finsupp.single_eq_same] at hle
  omega

variable {F : Type u} [Field F]

/-- Absolute irreducibility implies irreducibility over the original field. -/
theorem planeCurve_irreducible_of_absolute (f : MvPolynomial (Fin 2) F)
    (hf : Irreducible (map (algebraMap F (AlgebraicClosure F)) f)) :
    Irreducible f := by
  let φ := algebraMap F (AlgebraicClosure F)
  have hunit (g : MvPolynomial (Fin 2) F) (hg : IsUnit (map φ g)) : IsUnit g := by
    obtain ⟨a, ha, hga⟩ := isUnit_iff_eq_C_of_isReduced.mp hg
    have hc : φ (g.coeff 0) = a := by
      simpa only [coeff_map, coeff_zero_C] using congrArg (fun p => p.coeff 0) hga
    have heq : g = C (g.coeff 0) := by
      apply map_injective φ φ.injective
      rw [map_C, hc]
      exact hga
    rw [heq]
    apply IsUnit.map C
    apply isUnit_iff_ne_zero.mpr
    intro hz
    apply ha.ne_zero
    rw [← hc, hz, map_zero]
  refine ⟨fun hu => hf.not_isUnit (hu.map (map φ)), ?_⟩
  intro a b hab
  have heq : map φ f = map φ a * map φ b := by rw [hab, map_mul]
  exact (hf.isUnit_or_isUnit heq).imp (hunit a) (hunit b)

/-- The two coefficients of an irreducible linear polynomial in `Y` have
no common root in the first-coordinate field. -/
theorem planeCurve_iterated_linear_no_common_root
    (P : Polynomial (MvPolynomial (Fin 1) F))
    (hirr : Irreducible P) (hd : P.natDegree = 1) (x : F) :
    ¬ (eval (fun _ : Fin 1 => x) (P.coeff 1) = 0 ∧
      eval (fun _ : Fin 1 => x) (P.coeff 0) = 0) := by
  intro hroot
  let e := uniqueAlgEquiv F (Fin 1)
  let d := e.symm (Polynomial.X - Polynomial.C x)
  have hd_eval : eval (fun _ : Fin 1 => x) d = 0 := by
    rw [planeCurve_eval_unique]
    simp only [d, e, AlgEquiv.apply_symm_apply, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self]
  have hd_nonunit : ¬ IsUnit d := by
    intro hu
    have h := hu.map (eval (fun _ : Fin 1 => x))
    rw [hd_eval] at h
    exact not_isUnit_zero h
  have hdvd (q : MvPolynomial (Fin 1) F)
      (hq : eval (fun _ : Fin 1 => x) q = 0) : d ∣ q := by
    have heval : Polynomial.eval x (e q) = 0 := by
      rwa [planeCurve_eval_unique] at hq
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr heval
    refine ⟨e.symm r, ?_⟩
    apply e.injective
    simpa only [map_mul, d, AlgEquiv.apply_symm_apply] using hr
  obtain ⟨a, ha⟩ := hdvd (P.coeff 1) hroot.1
  obtain ⟨b, hb⟩ := hdvd (P.coeff 0) hroot.2
  have hdiv : Polynomial.C d ∣ P := by
    refine ⟨Polynomial.C a * Polynomial.X + Polynomial.C b, ?_⟩
    calc
      P = Polynomial.C (P.coeff 1) * Polynomial.X + Polynomial.C (P.coeff 0) :=
        Polynomial.eq_X_add_C_of_natDegree_le_one hd.le
      _ = Polynomial.C d * (Polynomial.C a * Polynomial.X + Polynomial.C b) := by
        rw [ha, hb, Polynomial.C_mul, Polynomial.C_mul]
        ring
  obtain ⟨Q, hQ⟩ := hdiv
  rcases hirr.isUnit_or_isUnit hQ with hleft | hright
  · exact hd_nonunit (Polynomial.isUnit_C.mp hleft)
  · have hdeg := Polynomial.natDegree_C_mul_le d Q
    rw [← hQ, hd, Polynomial.natDegree_eq_zero_of_isUnit hright] at hdeg
    omega

theorem planeCurve_linear_eval (f : MvPolynomial (Fin 2) F) (hf : f.degreeOf 1 = 1)
    (v : Fin 2 → F) :
    eval v f =
      Polynomial.eval (v 0)
        (uniqueAlgEquiv F (Fin 1) ((finSuccEquiv F 1 (planeCurveSwap f)).coeff 1)) * v 1 +
      Polynomial.eval (v 0)
        (uniqueAlgEquiv F (Fin 1) ((finSuccEquiv F 1 (planeCurveSwap f)).coeff 0)) := by
  have hd : (finSuccEquiv F 1 (planeCurveSwap f)).natDegree = 1 := by
    rw [natDegree_finSuccEquiv, planeCurveSwap_degree_first, hf]
  have hP := Polynomial.eq_X_add_C_of_natDegree_le_one hd.le
  have hv : eval v f = eval ![v 1, v 0] (planeCurveSwap f) := by
    rw [planeCurveSwap_eval, planeCurve_fin_two_eta]
  rw [hv, planeCurve_eval_finSuccEquiv]
  conv_lhs => rw [hP]
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    planeCurve_eval_unique]

/-- The concrete coefficients `a(X)` and `b(X)` of a linear-in-`Y` curve,
with the nonvanishing and no-common-root facts needed for fibre counting. -/
theorem planeCurve_linear_coefficients (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hf : f.degreeOf 1 = 1) :
    ∃ a b : Polynomial F,
      a ≠ 0 ∧ a.natDegree ≤ f.degreeOf 0 ∧
      (∀ x : F, ¬ (a.eval x = 0 ∧ b.eval x = 0)) ∧
      ∀ v : Fin 2 → F, eval v f = a.eval (v 0) * v 1 + b.eval (v 0) := by
  let P := finSuccEquiv F 1 (planeCurveSwap f)
  let e := uniqueAlgEquiv F (Fin 1)
  let a := e (P.coeff 1)
  let b := e (P.coeff 0)
  have hd : P.natDegree = 1 := by
    dsimp only [P]
    rw [natDegree_finSuccEquiv, planeCurveSwap_degree_first, hf]
  have hP : P ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hd
    omega
  have hcoeff : P.coeff 1 ≠ 0 := by
    simpa only [← Polynomial.coeff_natDegree, hd] using
      (Polynomial.leadingCoeff_ne_zero.mpr hP)
  have hi : Irreducible P := (MulEquiv.irreducible_iff (finSuccEquiv F 1)).mpr
    (planeCurve_irreducible_of_absolute (planeCurveSwap f)
      (planeCurveSwap_irreducible f hirr))
  refine ⟨a, b, ?_, ?_, ?_, ?_⟩
  · intro hz
    apply hcoeff
    apply e.injective
    simpa only [map_zero] using hz
  · have h := (planeCurve_natDegree_unique_le (P.coeff 1)).trans
      (degreeOf_coeff_finSuccEquiv (planeCurveSwap f) (0 : Fin 1) 1)
    change a.natDegree ≤ (planeCurveSwap f).degreeOf 1 at h
    exact h.trans_eq (planeCurveSwap_degree_second f)
  · intro x hx
    apply planeCurve_iterated_linear_no_common_root P hi hd x
    simpa only [planeCurve_eval_unique] using hx
  · intro v
    exact planeCurve_linear_eval f hf v

/-- Projecting a linear fibre onto its abscissa gives an equivalence with
the complement of the roots of its leading coefficient. -/
theorem planeCurve_linear_zero_count [Finite F] (f : MvPolynomial (Fin 2) F)
    (a b : Polynomial F) (hcop : ∀ x : F, ¬ (a.eval x = 0 ∧ b.eval x = 0))
    (heval : ∀ v : Fin 2 → F, eval v f = a.eval (v 0) * v 1 + b.eval (v 0)) :
    Nat.card {v : Fin 2 → F // eval v f = 0} =
      Nat.card {x : F // a.eval x ≠ 0} := by
  have ha (v : {v : Fin 2 → F // eval v f = 0}) : a.eval (v.val 0) ≠ 0 := by
    intro hx
    apply hcop (v.val 0)
    refine ⟨hx, ?_⟩
    have hz := v.property
    rw [heval, hx, zero_mul, zero_add] at hz
    exact hz
  let e : {v : Fin 2 → F // eval v f = 0} ≃ {x : F // a.eval x ≠ 0} :=
    { toFun := fun v => ⟨v.val 0, ha v⟩
      invFun := fun x => ⟨![x.val, -(b.eval x.val) / a.eval x.val], by
        rw [heval]
        dsimp
        field_simp [x.property]
        ring⟩
      left_inv := fun v => by
        apply Subtype.ext
        ext i
        fin_cases i
        · rfl
        · change -(b.eval (v.val 0)) / a.eval (v.val 0) = v.val 1
          apply (div_eq_iff (ha v)).mpr
          have hz := v.property
          rw [heval] at hz
          linear_combination -hz
      right_inv := fun x => by
        apply Subtype.ext
        rfl }
  exact Nat.card_congr e

theorem planeCurve_polynomial_root_count [Finite F] (a : Polynomial F) (ha : a ≠ 0) :
    Nat.card {x : F // a.eval x = 0} ≤ a.natDegree := by
  classical
  let := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  exact (Polynomial.mem_roots ha).mpr (Finset.mem_filter.mp hx).2

/-- The exact elementary estimate for a curve linear in its second coordinate. -/
theorem planeCurve_linear_zero_count_error [Finite F] (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hf : f.degreeOf 1 = 1) :
    |(Nat.card {v : Fin 2 → F // eval v f = 0} : ℝ) - (Nat.card F : ℝ)| ≤
      (f.degreeOf 0 : ℝ) := by
  classical
  let := Fintype.ofFinite F
  obtain ⟨a, b, ha, hdeg, hcop, heval⟩ := planeCurve_linear_coefficients f hirr hf
  have hcount := planeCurve_linear_zero_count f a b hcop heval
  have hpart :
      Nat.card {v : Fin 2 → F // eval v f = 0} +
        Nat.card {x : F // a.eval x = 0} = Nat.card F := by
    rw [hcount]
    simp only [Nat.card_eq_fintype_card, ne_eq]
    rw [Fintype.card_subtype_compl]
    exact Nat.sub_add_cancel (Fintype.card_subtype_le _)
  have hreal :
      (Nat.card {v : Fin 2 → F // eval v f = 0} : ℝ) +
        (Nat.card {x : F // a.eval x = 0} : ℝ) = (Nat.card F : ℝ) := by
    exact_mod_cast hpart
  have hsub :
      (Nat.card {v : Fin 2 → F // eval v f = 0} : ℝ) - (Nat.card F : ℝ) =
        -(Nat.card {x : F // a.eval x = 0} : ℝ) := by linarith
  rw [hsub, abs_neg, abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (planeCurve_polynomial_root_count a ha).trans hdeg

/-- Specialization of an irreducible positive-degree polynomial in `Y` at
an `X`-coordinate cannot vanish identically. -/
theorem planeCurve_iterated_specialization_ne_zero
    (P : Polynomial (MvPolynomial (Fin 1) F))
    (hirr : Irreducible P) (hd : 0 < P.natDegree) (x : F) :
    Polynomial.map (eval (fun _ : Fin 1 => x)) P ≠ 0 := by
  intro hz
  let e := uniqueAlgEquiv F (Fin 1)
  let d := e.symm (Polynomial.X - Polynomial.C x)
  have hd_eval : eval (fun _ : Fin 1 => x) d = 0 := by
    rw [planeCurve_eval_unique]
    simp only [d, e, AlgEquiv.apply_symm_apply, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self]
  have hd_nonunit : ¬ IsUnit d := by
    intro hu
    have h := hu.map (eval (fun _ : Fin 1 => x))
    rw [hd_eval] at h
    exact not_isUnit_zero h
  have hdiv : Polynomial.C d ∣ P := by
    apply (Polynomial.C_dvd_iff_dvd_coeff d P).mpr
    intro i
    have heval : Polynomial.eval x (e (P.coeff i)) = 0 := by
      rw [← planeCurve_eval_unique]
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using
        congrArg (fun Q : Polynomial F => Q.coeff i) hz
    obtain ⟨r, hr⟩ := Polynomial.dvd_iff_isRoot.mpr heval
    refine ⟨e.symm r, ?_⟩
    apply e.injective
    simpa only [map_mul, d, AlgEquiv.apply_symm_apply] using hr
  obtain ⟨Q, hQ⟩ := hdiv
  rcases hirr.isUnit_or_isUnit hQ with hleft | hright
  · exact hd_nonunit (Polynomial.isUnit_C.mp hleft)
  · have hdeg := Polynomial.natDegree_C_mul_le d Q
    rw [← hQ, Polynomial.natDegree_eq_zero_of_isUnit hright] at hdeg
    omega

/-- Every rational fibre of an absolutely irreducible plane curve of positive
second partial degree has at most that many points. -/
theorem planeCurve_fibre_count_le [Finite F] (f : MvPolynomial (Fin 2) F)
    (hirr : Irreducible (map (algebraMap F (AlgebraicClosure F)) f))
    (hn : 0 < f.degreeOf 1) (x : F) :
    Nat.card {y : F // eval ![x, y] f = 0} ≤ f.degreeOf 1 := by
  let P := finSuccEquiv F 1 (planeCurveSwap f)
  let Q := Polynomial.map (eval (fun _ : Fin 1 => x)) P
  have hi : Irreducible P := (MulEquiv.irreducible_iff (finSuccEquiv F 1)).mpr
    (planeCurve_irreducible_of_absolute (planeCurveSwap f)
      (planeCurveSwap_irreducible f hirr))
  have hdeg : P.natDegree = f.degreeOf 1 := by
    dsimp only [P]
    rw [natDegree_finSuccEquiv, planeCurveSwap_degree_first]
  have hQ : Q ≠ 0 := planeCurve_iterated_specialization_ne_zero P hi
    (by rwa [hdeg]) x
  have heval (y : F) : eval ![x, y] f = Q.eval y := by
    have h := planeCurveSwap_eval f y x
    rw [planeCurve_eval_finSuccEquiv] at h
    exact h.symm
  calc
    Nat.card {y : F // eval ![x, y] f = 0} = Nat.card {y : F // Q.eval y = 0} := by
      apply Nat.card_congr
      exact Equiv.subtypeEquiv (Equiv.refl F) (fun y => by
        simp only [Equiv.refl_apply, heval])
    _ ≤ Q.natDegree := planeCurve_polynomial_root_count Q hQ
    _ ≤ P.natDegree := Polynomial.natDegree_map_le
    _ = f.degreeOf 1 := hdeg

end Langlands.AlgebraicGeometry.LangWeil

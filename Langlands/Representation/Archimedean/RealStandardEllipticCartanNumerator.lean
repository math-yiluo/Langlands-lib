import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! # Recovering positive real block parameters from a Cartan numerator

A finite Fourier and exponential calculation for data consisting of positive-weight induced
blocks and real character blocks. See the paired Markdown.
-/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealStandardEllipticCartan

/-- The weight and exponent in each complex slot, and the sign and exponent in each real slot. -/
abbrev Parameters (r s : ℕ) := (Fin r → ℤ × ℂ) × (Fin s → Fin 2 × ℂ)

/-- Logarithmic radii and angles in the complex slots, and logarithmic absolute values
and exponents of the sign in the real slots. -/
abbrev Coordinates (r s : ℕ) :=
  (Fin r → Multiplicative (ℝ × ℝ)) × (Fin s → Multiplicative (ℝ × ℤ))

/-- The exponential in the logarithmic radius and the Fourier mode in the angle. -/
def complexTerm (p : ℤ × ℂ) : Multiplicative (ℝ × ℝ) →* ℂ where
  toFun x := Complex.exp ((x.toAdd.1 : ℂ) * (2 * p.2) +
    (x.toAdd.2 : ℂ) * (Complex.I * (p.1 : ℂ)))
  map_one' := by simp
  map_mul' x y := by
    simp only [show (x * y).toAdd = x.toAdd + y.toAdd by rfl, Prod.fst_add, Prod.snd_add,
      Complex.ofReal_add]
    rw [← Complex.exp_add]
    congr 1
    ring

/-- The exponential in the logarithmic absolute value and the prescribed sign. -/
def realTerm (p : Fin 2 × ℂ) : Multiplicative (ℝ × ℤ) →* ℂ where
  toFun x := Complex.exp ((x.toAdd.1 : ℂ) * p.2) * (-1 : ℂ) ^ ((p.1.val : ℤ) * x.toAdd.2)
  map_one' := by simp
  map_mul' x y := by
    simp only [show (x * y).toAdd = x.toAdd + y.toAdd by rfl, Prod.fst_add, Prod.snd_add,
      Complex.ofReal_add, add_mul, mul_add, Complex.exp_add,
      zpow_add₀ (show (-1 : ℂ) ≠ 0 by norm_num)]
    ring

private theorem exp_linear_injective :
    Function.Injective (fun a : ℂ => fun x : ℝ => Complex.exp ((x : ℂ) * a)) := by
  intro a b h
  have hd (c : ℂ) : HasDerivAt (fun x : ℝ => Complex.exp ((x : ℂ) * c)) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const c).cexp
  have ha := hd a
  change (fun x : ℝ => Complex.exp ((x : ℂ) * a)) =
    (fun x : ℝ => Complex.exp ((x : ℂ) * b)) at h
  rw [h] at ha
  exact ha.unique (hd b)

private theorem complexTerm_injective : Function.Injective complexTerm := by
  intro p q h
  apply Prod.ext
  · have hphase : (fun x : ℝ => Complex.exp ((x : ℂ) * (Complex.I * (p.1 : ℂ)))) =
        (fun x : ℝ => Complex.exp ((x : ℂ) * (Complex.I * (q.1 : ℂ)))) := by
      funext x
      simpa [complexTerm] using DFunLike.congr_fun h (Multiplicative.ofAdd (0, x))
    have hw := mul_left_cancel₀ Complex.I_ne_zero (exp_linear_injective hphase)
    exact_mod_cast hw
  · have hradial : (fun x : ℝ => Complex.exp ((x : ℂ) * (2 * p.2))) =
        (fun x : ℝ => Complex.exp ((x : ℂ) * (2 * q.2))) := by
      funext x
      simpa [complexTerm] using DFunLike.congr_fun h (Multiplicative.ofAdd (x, 0))
    exact mul_left_cancel₀ two_ne_zero (exp_linear_injective hradial)

private theorem parity_sign_injective :
    Function.Injective (fun e : Fin 2 => (-1 : ℂ) ^ (e.val : ℤ)) := by
  intro e e' h
  fin_cases e <;> fin_cases e' <;> first | rfl | norm_num at h

private theorem realTerm_injective : Function.Injective realTerm := by
  intro p q h
  apply Prod.ext
  · apply parity_sign_injective
    simpa [realTerm] using DFunLike.congr_fun h (Multiplicative.ofAdd (0, 1))
  · apply exp_linear_injective
    funext x
    simpa [realTerm] using DFunLike.congr_fun h (Multiplicative.ofAdd (x, 0))

private def term {r s : ℕ} (p : Parameters r s) : Coordinates r s →* ℂ where
  toFun x := (∏ i, complexTerm (p.1 i) (x.1 i)) * ∏ j, realTerm (p.2 j) (x.2 j)
  map_one' := by simp
  map_mul' x y := by
    simp only [Prod.fst_mul, Prod.snd_mul, Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
    ring

private theorem prod_eval_update {ι A : Type*} [Fintype ι] [DecidableEq ι] [MulOneClass A]
    (f : ι → A →* ℂ) (i : ι) (x : A) :
    (∏ j, f j (Function.update (1 : ι → A) i x j)) = f i x := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

private theorem term_injective {r s : ℕ} : Function.Injective (term (r := r) (s := s)) := by
  intro p q h
  apply Prod.ext
  · funext i
    apply complexTerm_injective
    apply MonoidHom.ext
    intro x
    let y : Coordinates r s := (Function.update (1 : Fin r → Multiplicative (ℝ × ℝ)) i x, 1)
    have he (t : Parameters r s) : term t y = complexTerm (t.1 i) x := by
      change (∏ j, complexTerm (t.1 j) (Function.update (1 : Fin r → Multiplicative (ℝ × ℝ)) i x j)) *
        (∏ j, realTerm (t.2 j) 1) = _
      rw [prod_eval_update (fun j => complexTerm (t.1 j)) i x]
      simp
    simpa only [he] using DFunLike.congr_fun h y
  · funext j
    apply realTerm_injective
    apply MonoidHom.ext
    intro x
    let y : Coordinates r s := (1, Function.update (1 : Fin s → Multiplicative (ℝ × ℤ)) j x)
    have he (t : Parameters r s) : term t y = realTerm (t.2 j) x := by
      change (∏ i, complexTerm (t.1 i) 1) *
        (∏ i, realTerm (t.2 i) (Function.update (1 : Fin s → Multiplicative (ℝ × ℤ)) j x i)) = _
      rw [prod_eval_update (fun i => realTerm (t.2 i)) j x]
      simp
    simpa only [he] using DFunLike.congr_fun h y

private abbrev Terms (r s : ℕ) :=
  Equiv.Perm (Fin r) × Equiv.Perm (Fin s) × (Fin r → Bool)

private def transform {r s : ℕ} (p : Parameters r s) (u : Terms r s) : Parameters r s :=
  ((fun i => let d := p.1 (u.1 i); (if u.2.2 i then -d.1 else d.1, d.2)), p.2 ∘ u.2.1)

private def orientationSign {r s : ℕ} (u : Terms r s) : ℂ :=
  ∏ i, if u.2.2 i then -1 else 1

private def coefficients {r s : ℕ} (p : Parameters r s) : Parameters r s →₀ ℂ :=
  ∑ u : Terms r s, Finsupp.single (transform p u) (orientationSign u)

/-- The numerator built by permuting complex and real slots and taking the signed
difference between the two orientations in each complex slot. -/
def numerator {r s : ℕ} (p : Parameters r s) : Coordinates r s → ℂ :=
  Finsupp.linearCombination ℂ (fun q : Parameters r s => (term q : Coordinates r s → ℂ))
    (coefficients p)

/-- The numerator as a sum of products of the signed complex-slot and real-slot factors. -/
theorem numerator_apply {r s : ℕ} (p : Parameters r s) (x : Coordinates r s) :
    numerator p x = ∑ π : Equiv.Perm (Fin r), ∑ σ : Equiv.Perm (Fin s),
      (∏ i, (complexTerm (p.1 (π i)) (x.1 i) -
        complexTerm (-(p.1 (π i)).1, (p.1 (π i)).2) (x.1 i))) *
      ∏ j, realTerm (p.2 (σ j)) (x.2 j) := by
  simp only [numerator, coefficients, map_sum, Finset.sum_apply,
    Finsupp.linearCombination_single, Pi.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro π _
  apply Finset.sum_congr rfl
  intro σ _
  let f (i : Fin r) (b : Bool) : ℂ :=
    if b then -complexTerm (-(p.1 (π i)).1, (p.1 (π i)).2) (x.1 i)
    else complexTerm (p.1 (π i)) (x.1 i)
  have h (b : Fin r → Bool) :
      orientationSign (π, σ, b) * term (transform p (π, σ, b)) x =
        (∏ i, f i (b i)) * ∏ j, realTerm (p.2 (σ j)) (x.2 j) := by
    simp only [term, MonoidHom.coe_mk, OneHom.coe_mk, orientationSign, transform,
      Function.comp_apply]
    rw [← mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    by_cases hb : b i = true <;> simp [f, hb]
  simp_rw [h]
  rw [← Finset.sum_mul, ← Fintype.prod_sum f]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [f, sub_eq_add_neg, add_comm]

private theorem no_flip_of_transform_eq {r s : ℕ} {p q : Parameters r s} {u : Terms r s}
    (hp : ∀ i, 0 < (p.1 i).1) (hq : ∀ i, 0 < (q.1 i).1)
    (h : transform p u = q) (i : Fin r) : u.2.2 i = false := by
  have hweight := congrArg (fun a : Parameters r s => (a.1 i).1) h
  cases hor : u.2.2 i with
  | false => rfl
  | true =>
    simp only [transform, hor, ↓reduceIte] at hweight
    have := hp (u.1 i)
    have := hq i
    omega

private theorem coefficients_at_positive {r s : ℕ} {p q : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) (hq : ∀ i, 0 < (q.1 i).1) :
    coefficients p q = ((Finset.univ.filter fun u : Terms r s => transform p u = q).card : ℂ) := by
  classical
  rw [coefficients, Finsupp.finsetSum_apply]
  calc
    _ = ∑ u : Terms r s, if transform p u = q then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro u _
      rw [Finsupp.single_apply]
      by_cases h : transform p u = q
      · simp [h, orientationSign, no_flip_of_transform_eq hp hq h]
      · simp [h]
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- Equality of these numerators determines all positive-weight complex parameters and
all signed real parameters, up to separate permutations of the two kinds of slots. -/
theorem exists_perm_of_numerator_eq {r s : ℕ} {p q : Parameters r s}
    (hp : ∀ i, 0 < (p.1 i).1) (hq : ∀ i, 0 < (q.1 i).1)
    (h : numerator p = numerator q) :
    ∃ (π : Equiv.Perm (Fin r)) (σ : Equiv.Perm (Fin s)),
      (∀ i, p.1 (π i) = q.1 i) ∧ ∀ j, p.2 (σ j) = q.2 j := by
  classical
  have hind := (linearIndependent_monoidHom (Coordinates r s) ℂ).comp term term_injective
  have hc : coefficients p = coefficients q := hind h
  have hv := congrArg (fun f : Parameters r s →₀ ℂ => f q) hc
  rw [coefficients_at_positive hp hq, coefficients_at_positive hq hq] at hv
  have hcard : (Finset.univ.filter fun u : Terms r s => transform p u = q).card =
      (Finset.univ.filter fun u : Terms r s => transform q u = q).card := by exact_mod_cast hv
  have hpos : 0 < (Finset.univ.filter fun u : Terms r s => transform q u = q).card := by
    apply Finset.card_pos.mpr
    refine ⟨(Equiv.refl _, Equiv.refl _, fun _ => false), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  rw [← hcard] at hpos
  obtain ⟨u, hu⟩ := Finset.card_pos.mp hpos
  have he := (Finset.mem_filter.mp hu).2
  have hn := no_flip_of_transform_eq hp hq he
  refine ⟨u.1, u.2.1, fun i => ?_, fun j => ?_⟩
  · simpa [transform, hn] using congrArg (fun a : Parameters r s => a.1 i) he
  · exact congrArg (fun a : Parameters r s => a.2 j) he

end Langlands.Archimedean.RealStandardEllipticCartan

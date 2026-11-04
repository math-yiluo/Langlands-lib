import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Algebra.Polynomial.HasseDeriv
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Algebra
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Additive polynomials over algebras in positive characteristic -/

noncomputable section

universe u

open MvPolynomial

namespace Langlands.GroupScheme.TorusLinearization

section Frobenius

variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime]

/-- Iterated Frobenius is additive as soon as the prime is zero in the ring. -/
theorem add_pow_prime_pow_of_natCast_eq_zero (h0 : (p : R) = 0) (x y : R) (m : ℕ) :
    (x + y) ^ p ^ m = x ^ p ^ m + y ^ p ^ m := by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hp.out x y m
  rw [hr, h0]
  ring

end Frobenius

section Additive

variable {n : ℕ} {A : Type u} [CommRing A]

/-- A polynomial is additive when its values on every commutative algebra in the
same universe are additive in the tuple of arguments. -/
def IsAddPoly (f : MvPolynomial (Fin n) A) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : Fin n → B),
    aeval (x + y) f = aeval x f + aeval y f

/-- Additivity of a one-variable polynomial on every commutative algebra. -/
def IsAddPoly₁ (φ : Polynomial A) : Prop :=
  ∀ (B : Type u) [CommRing B] [Algebra A B] (x y : B),
    Polynomial.aeval (x + y) φ = Polynomial.aeval x φ + Polynomial.aeval y φ

theorem IsAddPoly.aeval_zero {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f)
    {B : Type u} [CommRing B] [Algebra A B] : aeval (0 : Fin n → B) f = 0 := by
  have h := hf B 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem isAddPoly_zero : IsAddPoly (0 : MvPolynomial (Fin n) A) := by
  intro B _ _ x y
  simp

theorem IsAddPoly.add {f g : MvPolynomial (Fin n) A} (hf : IsAddPoly f) (hg : IsAddPoly g) :
    IsAddPoly (f + g) := by
  intro B _ _ x y
  simp only [map_add, hf B x y, hg B x y]
  abel

theorem IsAddPoly.smul {f : MvPolynomial (Fin n) A} (c : A) (hf : IsAddPoly f) :
    IsAddPoly (c • f) := by
  intro B _ _ x y
  simp only [map_smul, hf B x y, smul_add]

theorem IsAddPoly.neg {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) : IsAddPoly (-f) := by
  intro B _ _ x y
  simp only [map_neg, hf B x y, neg_add]

theorem isAddPoly_X (j : Fin n) : IsAddPoly (X j : MvPolynomial (Fin n) A) := by
  intro B _ _ x y
  simp

theorem IsAddPoly.pow_char (p : ℕ) [Fact p.Prime] (h0 : (p : A) = 0)
    {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) (m : ℕ) : IsAddPoly (f ^ p ^ m) := by
  intro B _ _ x y
  have hB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), h0, map_zero]
  simp only [map_pow, hf B x y]
  exact add_pow_prime_pow_of_natCast_eq_zero p hB _ _ m

variable (n A) in
/-- The additive polynomials, as a submodule over the coefficient ring. -/
def addPolys : Submodule A (MvPolynomial (Fin n) A) where
  carrier := {f | IsAddPoly f}
  zero_mem' := isAddPoly_zero
  add_mem' hf hg := IsAddPoly.add hf hg
  smul_mem' c _ hf := IsAddPoly.smul c hf

@[simp] theorem mem_addPolys {f : MvPolynomial (Fin n) A} : f ∈ addPolys n A ↔ IsAddPoly f :=
  Iff.rfl

theorem IsAddPoly.aeval_sum {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f)
    {B : Type u} [CommRing B] [Algebra A B] {ι : Type*} (s : Finset ι) (x : ι → Fin n → B) :
    aeval (∑ i ∈ s, x i) f = ∑ i ∈ s, aeval (x i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hf.aeval_zero
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, hf B, ih]

/-- The one-variable part of a polynomial along a coordinate. -/
def part (j : Fin n) : MvPolynomial (Fin n) A →ₐ[A] Polynomial A :=
  aeval (Pi.single j Polynomial.X)

theorem aeval_single_eq_part (j : Fin n) (f : MvPolynomial (Fin n) A)
    {B : Type*} [CommRing B] [Algebra A B] (b : B) :
    aeval (Pi.single j b) f = Polynomial.aeval b (part j f) := by
  have hfun : (fun i => Polynomial.aeval b
      ((Pi.single j (Polynomial.X : Polynomial A) : Fin n → Polynomial A) i)) =
      Pi.single j b := by
    funext i
    by_cases hi : i = j
    · subst hi
      simp
    · simp [Pi.single_eq_of_ne hi]
  rw [part, ← AlgHom.comp_apply, comp_aeval, hfun]

theorem IsAddPoly.isAddPoly₁_part (j : Fin n) {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) :
    IsAddPoly₁ (part j f) := by
  intro B _ _ x y
  rw [← aeval_single_eq_part, ← aeval_single_eq_part, ← aeval_single_eq_part,
    Pi.single_add]
  exact hf B _ _

/-- An additive polynomial is the sum of its one-variable parts. -/
theorem IsAddPoly.eq_sum_part {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) :
    f = ∑ j, Polynomial.aeval (X j : MvPolynomial (Fin n) A) (part j f) := by
  have h := hf.aeval_sum Finset.univ (fun j => Pi.single j (X j : MvPolynomial (Fin n) A))
  rw [Finset.univ_sum_single, aeval_X_left_apply] at h
  exact h.trans (Finset.sum_congr rfl fun j _ => aeval_single_eq_part j f _)

end Additive

section OneVariable

variable {A : Type u} [CommRing A]

/-- The higher Hasse derivatives of an additive polynomial are constant. -/
theorem IsAddPoly₁.hasseDeriv_eq {φ : Polynomial A} (hφ : IsAddPoly₁ φ) {i : ℕ} (hi : 1 ≤ i) :
    Polynomial.hasseDeriv i φ = Polynomial.C (φ.coeff i) := by
  have h := hφ (Polynomial (Polynomial A)) Polynomial.X (Polynomial.C Polynomial.X)
  have hl : Polynomial.aeval (Polynomial.X + Polynomial.C Polynomial.X :
      Polynomial (Polynomial A)) φ = Polynomial.taylor Polynomial.X (φ.map Polynomial.C) := by
    rw [Polynomial.taylor_apply, Polynomial.comp, Polynomial.eval₂_map, Polynomial.aeval_def]
    rfl
  have hc : Polynomial.aeval (Polynomial.C Polynomial.X : Polynomial (Polynomial A)) φ =
      Polynomial.C φ := by
    have := Polynomial.aeval_algHom_apply
      (IsScalarTower.toAlgHom A (Polynomial A) (Polynomial (Polynomial A))) Polynomial.X φ
    simpa [Polynomial.aeval_X_left_apply] using this
  have hr : Polynomial.aeval (Polynomial.X : Polynomial (Polynomial A)) φ =
      φ.map Polynomial.C := by
    rw [Polynomial.aeval_def]
    rfl
  have hcoeff := congrArg (fun q => Polynomial.coeff q i) h
  simp only [hl, hc, hr, Polynomial.taylor_coeff, Polynomial.hasseDeriv_map,
    Polynomial.coeff_add, Polynomial.coeff_C, Polynomial.coeff_map, Polynomial.eval_map,
    Polynomial.eval₂_C_X] at hcoeff
  simp [hcoeff, show i ≠ 0 by omega]

theorem IsAddPoly₁.add {φ ψ : Polynomial A} (hφ : IsAddPoly₁ φ) (hψ : IsAddPoly₁ ψ) :
    IsAddPoly₁ (φ + ψ) := by
  intro B _ _ x y
  simp only [map_add, hφ B x y, hψ B x y]
  abel

theorem IsAddPoly₁.smul {φ : Polynomial A} (c : A) (hφ : IsAddPoly₁ φ) :
    IsAddPoly₁ (c • φ) := by
  intro B _ _ x y
  simp only [map_smul, hφ B x y, smul_add]

theorem IsAddPoly₁.neg {φ : Polynomial A} (hφ : IsAddPoly₁ φ) : IsAddPoly₁ (-φ) := by
  intro B _ _ x y
  simp only [map_neg, hφ B x y, neg_add]

theorem IsAddPoly₁.sub {φ ψ : Polynomial A} (hφ : IsAddPoly₁ φ) (hψ : IsAddPoly₁ ψ) :
    IsAddPoly₁ (φ - ψ) := by
  rw [sub_eq_add_neg]
  exact hφ.add hψ.neg

theorem isAddPoly₁_zero : IsAddPoly₁ (0 : Polynomial A) := by
  intro B _ _ x y
  simp

theorem isAddPoly₁_X : IsAddPoly₁ (Polynomial.X : Polynomial A) := by
  intro B _ _ x y
  simp

theorem IsAddPoly₁.comp {φ ψ : Polynomial A} (hφ : IsAddPoly₁ φ) (hψ : IsAddPoly₁ ψ) :
    IsAddPoly₁ (φ.comp ψ) := by
  intro B _ _ x y
  simp only [Polynomial.aeval_comp, hψ B x y, hφ B]

theorem IsAddPoly₁.pow_char (p : ℕ) [Fact p.Prime] (h0 : (p : A) = 0)
    {φ : Polynomial A} (hφ : IsAddPoly₁ φ) (m : ℕ) : IsAddPoly₁ (φ ^ p ^ m) := by
  intro B _ _ x y
  have hB : (p : B) = 0 := by rw [← map_natCast (algebraMap A B), h0, map_zero]
  simp only [map_pow, hφ B x y]
  exact add_pow_prime_pow_of_natCast_eq_zero p hB _ _ m

/-- Substituting an additive polynomial into an additive one-variable polynomial gives an
additive polynomial. -/
theorem IsAddPoly₁.aeval {n : ℕ} {φ : Polynomial A} (hφ : IsAddPoly₁ φ)
    {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) : IsAddPoly (Polynomial.aeval f φ) := by
  intro B _ _ x y
  rw [← Polynomial.aeval_algHom_apply, ← Polynomial.aeval_algHom_apply,
    ← Polynomial.aeval_algHom_apply, hf B x y, hφ B]

variable (A) in
/-- The additive one-variable polynomials, as a submodule. -/
def addPolys₁ : Submodule A (Polynomial A) where
  carrier := {φ | IsAddPoly₁ φ}
  zero_mem' := isAddPoly₁_zero
  add_mem' hf hg := IsAddPoly₁.add hf hg
  smul_mem' c _ hf := IsAddPoly₁.smul c hf

@[simp] theorem mem_addPolys₁ {φ : Polynomial A} : φ ∈ addPolys₁ A ↔ IsAddPoly₁ φ :=
  Iff.rfl

/-- Additivity forces the binomial relations among coefficients. -/
theorem IsAddPoly₁.choose_mul_coeff {φ : Polynomial A} (hφ : IsAddPoly₁ φ) {d i : ℕ}
    (hi : 1 ≤ i) (hid : i < d) : (d.choose i : A) * φ.coeff d = 0 := by
  have h := congrArg (fun q => Polynomial.coeff q (d - i)) (hφ.hasseDeriv_eq hi)
  simp only [Polynomial.hasseDeriv_coeff, Polynomial.coeff_C] at h
  simpa [Nat.sub_add_cancel hid.le, show d - i ≠ 0 by omega] using h

theorem IsAddPoly₁.coeff_zero {φ : Polynomial A} (hφ : IsAddPoly₁ φ) : φ.coeff 0 = 0 := by
  have h := hφ A 0 0
  rw [add_zero, left_eq_add] at h
  rw [Polynomial.coeff_zero_eq_aeval_zero, h]

variable (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] [Algebra k A]

omit hp in
include k in
theorem natCast_isUnit_of_not_dvd {m : ℕ} (hm : ¬ p ∣ m) : IsUnit (m : A) := by
  have hk : (m : k) ≠ 0 := by
    rwa [Ne, CharP.cast_eq_zero_iff k p]
  simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hk).map (algebraMap k A)

include k in
/-- Over an algebra over a field of characteristic `p`, an additive polynomial only has
coefficients in degrees `p ^ r`. -/
theorem IsAddPoly₁.coeff_eq_zero {φ : Polynomial A} (hφ : IsAddPoly₁ φ) {d : ℕ}
    (hd : ∀ r, d ≠ p ^ r) : φ.coeff d = 0 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd0
  · exact hφ.coeff_zero
  by_contra hne
  apply hd (multiplicity p d)
  apply Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat hd0
  intro i hi
  rw [Finset.mem_Icc] at hi
  rw [Nat.modEq_zero_iff_dvd]
  by_contra hpi
  exact hne ((natCast_isUnit_of_not_dvd k p hpi).mul_right_eq_zero.mp
    (hφ.choose_mul_coeff hi.1 (by omega)))

end OneVariable

section Span

variable (n : ℕ) (A : Type u) [CommRing A] (p : ℕ)

/-- Exponent vectors of the monomials `X_j ^ (p ^ r)`. -/
def addExponents : Set (Fin n →₀ ℕ) := {s | ∃ j r, s = Finsupp.single j (p ^ r)}

/-- The span of the monomials `X_j ^ (p ^ r)`; these are the additive polynomials. -/
def addSpan : Submodule A (MvPolynomial (Fin n) A) := restrictSupport A (addExponents n p)

variable {n A p}

theorem aeval_X_mem_addSpan (j : Fin n) {φ : Polynomial A}
    (hφ : ∀ d ∈ φ.support, ∃ r, d = p ^ r) :
    Polynomial.aeval (X j : MvPolynomial (Fin n) A) φ ∈ addSpan n A p := by
  rw [φ.as_sum_support_C_mul_X_pow, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  obtain ⟨r, rfl⟩ := hφ d hd
  rw [map_mul, Polynomial.aeval_C, Polynomial.aeval_X_pow, algebraMap_eq,
    C_mul_X_pow_eq_monomial]
  exact (monomial_mem_restrictSupport _).mpr (Or.inl ⟨j, r, rfl⟩)

theorem X_pow_mem_addSpan (j : Fin n) (r : ℕ) :
    (X j : MvPolynomial (Fin n) A) ^ p ^ r ∈ addSpan n A p := by
  rw [X_pow_eq_monomial]
  exact (monomial_mem_restrictSupport _).mpr (Or.inl ⟨j, r, rfl⟩)

theorem addSpan_eq_span :
    addSpan n A p = Submodule.span A
      (Set.range fun jr : Fin n × ℕ => (X jr.1 : MvPolynomial (Fin n) A) ^ p ^ jr.2) := by
  rw [addSpan, restrictSupport_eq_span]
  congr 1
  ext f
  simp only [addExponents, Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Prod.exists]
  constructor
  · rintro ⟨s, ⟨j, r, rfl⟩, rfl⟩
    exact ⟨j, r, by rw [X_pow_eq_monomial]⟩
  · rintro ⟨j, r, rfl⟩
    exact ⟨_, ⟨j, r, rfl⟩, by rw [X_pow_eq_monomial]⟩

/-- Polynomials in the span of the `X_j ^ (p ^ r)` are additive in characteristic `p`. -/
theorem addSpan_le_addPolys [Fact p.Prime] (h0 : (p : A) = 0) :
    addSpan n A p ≤ addPolys n A := by
  rw [addSpan_eq_span, Submodule.span_le]
  rintro _ ⟨⟨j, r⟩, rfl⟩
  exact (isAddPoly_X j).pow_char p h0 r

variable (k : Type u) [Field k] [Fact p.Prime] [CharP k p] [Algebra k A]

include k in
/-- Over an algebra over a field of characteristic `p`, every additive polynomial is a linear
combination of the monomials `X_j ^ (p ^ r)`. -/
theorem IsAddPoly.mem_addSpan {f : MvPolynomial (Fin n) A} (hf : IsAddPoly f) :
    f ∈ addSpan n A p := by
  rw [hf.eq_sum_part]
  refine Submodule.sum_mem _ fun j _ => aeval_X_mem_addSpan j fun d hd => ?_
  by_contra hne
  push Not at hne
  exact Polynomial.mem_support_iff.mp hd ((hf.isAddPoly₁_part j).coeff_eq_zero k p hne)

end Span


end Langlands.GroupScheme.TorusLinearization

import Langlands.Algebra.GradedHopf.PolynomialFrobenius
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Descent of polynomials invariant under truncated translations -/

noncomputable section

open MvPolynomial

universe u v

namespace Langlands.Algebra.PolynomialFrobeniusDescent

variable {σ : Type v} {R : Type u} [CommRing R]

/-- Universal translation, with base variables in the coefficient ring and
translation variables in the outer polynomial ring. -/
def translation : MvPolynomial σ R →+* MvPolynomial σ (MvPolynomial σ R) :=
  eval₂Hom (C.comp C) (fun i => C (X i) + X i)

/-- The universal translation as a homomorphism of algebras over the original
coefficient ring. -/
def translationAlgebra :
    MvPolynomial σ R →ₐ[R] MvPolynomial σ (MvPolynomial σ R) where
  __ := translation
  commutes' a := by
    rw [IsScalarTower.algebraMap_apply R (MvPolynomial σ R)
      (MvPolynomial σ (MvPolynomial σ R))]
    simp [MvPolynomial.algebraMap_eq, translation]

@[simp]
theorem translation_C (a : R) : translation (C a : MvPolynomial σ R) = C (C a) :=
  eval₂Hom_C _ _ _

@[simp]
theorem translation_X (i : σ) : translation (X i : MvPolynomial σ R) = C (X i) + X i :=
  eval₂Hom_X' _ _ _

@[simp]
theorem constantCoeff_translation (F : MvPolynomial σ R) :
    constantCoeff (translation F) = F := by
  have he : constantCoeff.comp (translation (σ := σ) (R := R)) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext <;> intro a <;> simp
  exact RingHom.congr_fun he F

theorem pderiv_translation (i : σ) (F : MvPolynomial σ R) :
    pderiv i (translation F) = translation (pderiv i F) := by
  classical
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add F H hF hH => simp [hF, hH]
  | mul_X F j hF =>
      simp only [map_mul, pderiv_mul, translation_X, map_add, pderiv_C, zero_add,
        pderiv_X, Pi.single_apply, hF]
      split_ifs <;> simp

theorem coeff_single_translation (i : σ) (F : MvPolynomial σ R) :
    (translation F).coeff (Finsupp.single i 1) = pderiv i F := by
  calc
    (translation F).coeff (Finsupp.single i 1) =
        (pderiv i (translation F)).coeff 0 := by rw [coeff_pderiv]; simp
    _ = (translation (pderiv i F)).coeff 0 := by rw [pderiv_translation]
    _ = pderiv i F := constantCoeff_translation _

@[simp]
theorem coeff_zero_translation_sub (F : MvPolynomial σ R) :
    (translation F - C F).coeff 0 = 0 := by
  change constantCoeff (translation F - C F) = 0
  simp

/-- Expand both the translation variables and the base variables. -/
def doubleExpansion (q : ℕ) :
    MvPolynomial σ (MvPolynomial σ R) →+* MvPolynomial σ (MvPolynomial σ R) :=
  (MvPolynomial.map (expand q).toRingHom).comp (expand q).toRingHom

@[simp]
theorem doubleExpansion_C (q : ℕ) (F : MvPolynomial σ R) :
    doubleExpansion q (C F) = C (expand q F) := by
  simp [doubleExpansion]

@[simp]
theorem doubleExpansion_X (q : ℕ) (i : σ) :
    doubleExpansion q (X i : MvPolynomial σ (MvPolynomial σ R)) = X i ^ q := by
  simp [doubleExpansion]

theorem coeff_doubleExpansion (q : ℕ) (hq : q ≠ 0)
    (P : MvPolynomial σ (MvPolynomial σ R)) (m : σ →₀ ℕ) :
    (doubleExpansion q P).coeff (q • m) = expand q (P.coeff m) := by
  rw [doubleExpansion, RingHom.comp_apply, coeff_map]
  change expand q ((expand q P).coeff (q • m)) = _
  rw [coeff_expand_smul q hq]

variable (p : ℕ) [ExpChar R p]

theorem translation_expand (r : ℕ) (F : MvPolynomial σ R) :
    translation (expand (p ^ r) F) = doubleExpansion (p ^ r) (translation F) := by
  have he : (translation (σ := σ) (R := R)).comp (expand (p ^ r)).toRingHom =
      (doubleExpansion (p ^ r)).comp translation := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp
    · intro i
      simp [add_pow_expChar_pow]
  exact RingHom.congr_fun he F

theorem translation_sub_expand (r : ℕ) (F : MvPolynomial σ R) :
    translation (expand (p ^ r) F) - C (expand (p ^ r) F) =
      doubleExpansion (p ^ r) (translation F - C F) := by
  rw [map_sub, translation_expand, doubleExpansion_C]

/-- All translation coefficients strictly inside the `q`-box vanish after
subtracting the original polynomial. -/
def TruncatedInvariant (q : ℕ) (F : MvPolynomial σ R) : Prop :=
  ∀ m : σ →₀ ℕ, (∀ i, m i < q) →
    (translation F - C F).coeff m = 0

/-- The monomial ideal whose support is outside the strict `q`-box. -/
def truncationIdeal (q : ℕ) : Ideal (MvPolynomial σ R) :=
  restrictSupportIdeal (R := R) {m | ∃ i, q ≤ m i} (by
    intro a b hab
    rintro ⟨i, hi⟩
    exact ⟨i, hi.trans (hab i)⟩)

theorem mem_truncationIdeal (q : ℕ) (P : MvPolynomial σ R) :
    P ∈ truncationIdeal q ↔ ∀ m, (∀ i, m i < q) → P.coeff m = 0 := by
  classical
  change P ∈ restrictSupport R {m | ∃ i, q ≤ m i} ↔ _
  rw [mem_restrictSupport_iff]
  constructor
  · intro h m hm
    by_contra hc
    obtain ⟨i, hi⟩ := h (mem_support_iff.mpr hc)
    exact (not_le_of_gt (hm i)) hi
  · intro h m hm
    by_contra hn
    exact (mem_support_iff.mp hm)
      (h m fun i => Nat.lt_of_not_ge (fun hi => hn ⟨i, hi⟩))

theorem X_pow_mem_truncationIdeal (q : ℕ) (i : σ) :
    (X i : MvPolynomial σ R) ^ q ∈ truncationIdeal q := by
  change (X i : MvPolynomial σ R) ^ q ∈ restrictSupport R {m | ∃ j, q ≤ m j}
  rw [X_pow_eq_monomial, monomial_mem_restrictSupport]
  exact Or.inl ⟨i, by simp⟩

theorem truncatedInvariant_iff_mem (q : ℕ) (F : MvPolynomial σ R) :
    TruncatedInvariant q F ↔
      translation F - C F ∈ truncationIdeal q :=
  (mem_truncationIdeal q _).symm

omit [ExpChar R p] in
theorem pderiv_eq_zero_of_truncatedInvariant (q : ℕ) (hq : 1 < q)
    {F : MvPolynomial σ R} (hF : TruncatedInvariant q F) :
    ∀ i, pderiv i F = 0 := by
  classical
  intro i
  have he := hF (Finsupp.single i 1) (by
    intro j
    by_cases hj : i = j
    · subst j
      simpa using hq
    · simpa [Finsupp.single_apply, hj] using (Nat.zero_lt_of_lt hq))
  simpa [coeff_single_translation, eq_comm, Finsupp.single_ne_zero] using he

theorem truncatedInvariant_expand (r : ℕ) (H : MvPolynomial σ R) :
    TruncatedInvariant (p ^ r) (expand (p ^ r) H) := by
  classical
  intro m hm
  by_cases h0 : m = 0
  · subst m
    exact coeff_zero_translation_sub _
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra hn
    push Not at hn
    exact h0 (Finsupp.ext hn)
  have hnot : ¬p ^ r ∣ m i := by
    intro hd
    exact (not_le_of_gt (hm i)) (Nat.le_of_dvd (Nat.pos_of_ne_zero hi) hd)
  rw [translation_sub_expand, doubleExpansion, RingHom.comp_apply, coeff_map]
  change expand (p ^ r) ((expand (p ^ r) (translation H - C H)).coeff m) = 0
  rw [coeff_expand_of_not_dvd _ hnot, map_zero]

theorem truncatedInvariant_of_expand_step (r : ℕ) {H : MvPolynomial σ R}
    (hH : TruncatedInvariant (p ^ (r + 1)) (expand p H)) :
    TruncatedInvariant (p ^ r) H := by
  intro m hm
  have he := hH (p • m) (by
    intro i
    simpa only [Finsupp.smul_apply, smul_eq_mul, pow_succ'] using
      (Nat.mul_lt_mul_of_pos_left (hm i) (expChar_pos R p)))
  have hshift : translation (expand p H) - C (expand p H) =
      doubleExpansion p (translation H - C H) := by
    simpa only [pow_one] using translation_sub_expand p 1 H
  rw [hshift, coeff_doubleExpansion p (expChar_ne_zero R p)] at he
  exact (expand_eq_zero (expChar_pos R p)).mp he

variable {k : Type u} [Field k]

/-- Truncated universal translation invariance forces a polynomial to be in
the image of the characteristic-power expansion. -/
theorem exists_expand_of_truncatedInvariant (p : ℕ) [ExpChar k p] (r : ℕ)
    {F : MvPolynomial σ k} (hF : TruncatedInvariant (p ^ r) F) :
    ∃ H : MvPolynomial σ k, F = expand (p ^ r) H := by
  rcases expChar_is_prime_or_one k p with hp | rfl
  · let : Fact p.Prime := ⟨hp⟩
    let : CharP k p := (expChar_prime_iff k hp).mp inferInstance
    induction r generalizing F with
    | zero => exact ⟨F, by simp⟩
    | succ r ih =>
        have hq : 1 < p ^ (r + 1) := by
          rw [pow_succ']
          have hpow : 1 ≤ p ^ r := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hp.ne_zero)
          nlinarith [hp.two_le]
        obtain ⟨H, hH⟩ := GradedHopf.exists_expand_of_pderiv_eq_zero p
          (pderiv_eq_zero_of_truncatedInvariant _ hq hF)
        obtain ⟨K, hK⟩ := ih (truncatedInvariant_of_expand_step p r (hH ▸ hF))
        refine ⟨K, ?_⟩
        rw [hH, hK, pow_succ', expand_mul]
  · exact ⟨F, by simp⟩

theorem truncatedInvariant_iff_exists_expand (p : ℕ) [ExpChar k p] (r : ℕ)
    (F : MvPolynomial σ k) :
    TruncatedInvariant (p ^ r) F ↔ ∃ H : MvPolynomial σ k, F = expand (p ^ r) H := by
  constructor
  · exact exists_expand_of_truncatedInvariant p r
  · rintro ⟨H, rfl⟩
    exact truncatedInvariant_expand p r H

/-- Equality on every pair of coefficient-algebra points with equal `q`-th
powers of all coordinates. The test universe contains the polynomial ring. -/
def UniversalPowerInvariant (q : ℕ) (F : MvPolynomial σ k) : Prop :=
  ∀ (A : Type (max u v)) [CommRing A] [Algebra k A]
    (f g : MvPolynomial σ k →ₐ[k] A),
    (∀ a, f a ^ q = g a ^ q) → f F = g F

theorem universalPowerInvariant_expand (q : ℕ) (H : MvPolynomial σ k) :
    UniversalPowerInvariant q (expand q H) := by
  intro A _ _ f g hfg
  have he : f.toRingHom.comp (expand q).toRingHom =
      g.toRingHom.comp (expand q).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change f (expand q (C a)) = g (expand q (C a))
      rw [expand_C]
      exact (f.commutes a).trans (g.commutes a).symm
    · intro i
      change f (expand q (X i)) = g (expand q (X i))
      rw [expand_X, map_pow, map_pow]
      exact hfg (X i)
  exact RingHom.congr_fun he H

theorem truncatedInvariant_of_universalPowerInvariant
    (p : ℕ) [ExpChar k p] (r : ℕ) {F : MvPolynomial σ k}
    (hF : UniversalPowerInvariant (p ^ r) F) :
    TruncatedInvariant (p ^ r) F := by
  let P := MvPolynomial σ (MvPolynomial σ k)
  let I : Ideal P := truncationIdeal (p ^ r)
  let Q := P ⧸ I
  let π : P →+* Q := Ideal.Quotient.mk I
  let f : MvPolynomial σ k →ₐ[k] Q :=
    (Ideal.Quotient.mkₐ k I).comp translationAlgebra
  let g : MvPolynomial σ k →ₐ[k] Q :=
    (Ideal.Quotient.mkₐ k I).comp (IsScalarTower.toAlgHom k (MvPolynomial σ k) P)
  have hf (a : MvPolynomial σ k) : f a = π (translation a) := rfl
  have hg (a : MvPolynomial σ k) : g a = π (C a) := by
    change π (algebraMap (MvPolynomial σ k) P a) = π (C a)
    rw [MvPolynomial.algebraMap_eq]
  let φ : P →+* Q := π.comp (iterateFrobenius P p r)
  have hφ : φ.comp translation = φ.comp C := by
    apply MvPolynomial.ringHom_ext
    · intro a
      exact congrArg φ (translation_C (σ := σ) a)
    · intro i
      simp only [RingHom.comp_apply]
      rw [translation_X (R := k) i]
      change π ((C (X i) + X i) ^ p ^ r) = π ((C (X i)) ^ p ^ r)
      rw [add_pow_expChar_pow, map_add]
      have hz : π ((X i : P) ^ p ^ r) = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (X_pow_mem_truncationIdeal _ _)
      rw [hz, add_zero]
  have he := hF Q f g (by
    intro a
    rw [hf, hg]
    simpa only [φ, RingHom.comp_apply, iterateFrobenius_def, map_pow] using
      RingHom.congr_fun hφ a)
  apply (truncatedInvariant_iff_mem _ _).mpr
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change π (translation F - C F) = 0
  rw [map_sub, sub_eq_zero]
  simpa only [hf, hg] using he

theorem exists_expand_of_universalPowerInvariant
    (p : ℕ) [ExpChar k p] (r : ℕ) {F : MvPolynomial σ k}
    (hF : UniversalPowerInvariant (p ^ r) F) :
    ∃ H : MvPolynomial σ k, F = expand (p ^ r) H :=
  exists_expand_of_truncatedInvariant p r
    (truncatedInvariant_of_universalPowerInvariant p r hF)

theorem universalPowerInvariant_iff_exists_expand
    (p : ℕ) [ExpChar k p] (r : ℕ) (F : MvPolynomial σ k) :
    UniversalPowerInvariant (p ^ r) F ↔
      ∃ H : MvPolynomial σ k, F = expand (p ^ r) H := by
  constructor
  · exact exists_expand_of_universalPowerInvariant p r
  · rintro ⟨H, rfl⟩
    exact universalPowerInvariant_expand _ H

end Langlands.Algebra.PolynomialFrobeniusDescent

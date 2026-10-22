import Langlands.Geometry.Analytic.WeierstrassPreparation

/-! # Leading-unit normalization of distinguished Tate series -/

noncomputable section

universe u

namespace Langlands.Analytic.RestrictedSeries

variable {A : Type u} [NormedCommRing A] [IsUltrametricDist A]

theorem coeff_constant_mul (a : A) (f : Algebra A) (n : ℕ) :
    coeff A n (algebraMap A (Algebra A) a * f) = a * coeff A n f := by
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

/-- An actual coefficient unit gives an actual constant unit in the
restricted-series ring. -/
def constantUnit (a : Aˣ) : (Algebra A)ˣ :=
  Units.map (algebraMap A (Algebra A)).toMonoidHom a

@[simp]
theorem constantUnit_val (a : Aˣ) :
    (constantUnit a : Algebra A) = algebraMap A (Algebra A) (a : A) := rfl

variable [Nontrivial A] [NormOneClass A] [NormMulClass A]

/-- Multiplicativity of the coefficient norm verifies normalization after
multiplication by the inverse of the distinguished coefficient. -/
theorem normalizedDistinguished_of_unit_coefficient
    (f : Algebra A) (d : ℕ) (a : Aˣ) (ha : (a : A) = coeff A d f)
    (hbound : ∀ n, ‖coeff A n f‖ ≤ ‖coeff A d f‖)
    (htail : ∀ n, d < n → ‖coeff A n f‖ < ‖coeff A d f‖) :
    IsNormalizedDistinguished ((constantUnit a⁻¹ : Algebra A) * f) d := by
  have hprod : ‖((a⁻¹ : Aˣ) : A)‖ * ‖(a : A)‖ = 1 := by
    rw [← norm_mul]
    simp
  have hpos : 0 < ‖((a⁻¹ : Aˣ) : A)‖ := Units.norm_pos _
  refine ⟨?_, ?_, ?_⟩
  · rw [constantUnit_val, coeff_constant_mul, ← ha]
    simp
  · intro n
    rw [constantUnit_val, coeff_constant_mul, norm_mul, ← hprod]
    apply mul_le_mul_of_nonneg_left _ hpos.le
    simpa only [ha] using hbound n
  · intro n hn
    rw [constantUnit_val, coeff_constant_mul, norm_mul, ← hprod]
    apply mul_lt_mul_of_pos_left _ hpos
    simpa only [ha] using htail n hn

variable [CompleteSpace A]

/-- Division by an arbitrary distinguished series. Both the product of
divisor and quotient and the remainder have norm at most the dividend. -/
theorem existsUnique_distinguished_division
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) (g : Algebra A) :
    ∃! qr : Algebra A × Polynomial A,
      g = f * qr.1 + ofPolynomial A qr.2 ∧ qr.2.degree < d ∧
      ‖f * qr.1‖ ≤ ‖g‖ ∧ ‖ofPolynomial A qr.2‖ ≤ ‖g‖ := by
  obtain ⟨a, ha⟩ := hf.1
  let c := constantUnit a
  let h := ((c⁻¹ : (Algebra A)ˣ) : Algebra A) * f
  have hh : IsNormalizedDistinguished h d := by
    simpa only [h, c, constantUnit, map_inv] using
      normalizedDistinguished_of_unit_coefficient f d a ha hf.2.1 hf.2.2
  have hhnorm : ‖h‖ ≤ 1 := (norm_le_iff A h zero_le_one).mpr hh.2.1
  obtain ⟨qr, hqr, huniq⟩ := existsUnique_normalizedDistinguished_division h d hh g
  let q := ((c⁻¹ : (Algebra A)ˣ) : Algebra A) * qr.1
  have hproduct : f * q = h * qr.1 := by
    dsimp [q, h]
    ring
  have heq : g = f * q + ofPolynomial A qr.2 := by
    rw [hproduct]
    exact hqr.1
  have hbound : ‖f * q‖ ≤ ‖g‖ := by
    rw [hproduct]
    exact ((norm_mul_le _ _).trans
      (mul_le_of_le_one_left (norm_nonneg _) hhnorm)).trans hqr.2.2.1
  refine ⟨(q, qr.2), ⟨heq, hqr.2.1, hbound, hqr.2.2.2⟩, ?_⟩
  rintro ⟨q', r'⟩ ⟨heq', hdegree', _, _⟩
  have hproduct' : h * ((c : Algebra A) * q') = f * q' := by
    dsimp [h]
    calc
      ((c⁻¹ : (Algebra A)ˣ) : Algebra A) * f * ((c : Algebra A) * q') =
          (((c⁻¹ : (Algebra A)ˣ) : Algebra A) * (c : Algebra A)) * (f * q') := by
        ring
      _ = _ := by simp
  have heq'' : g = h * ((c : Algebra A) * q') + ofPolynomial A r' := by
    rw [hproduct']
    exact heq'
  have hb := norm_le_normalizedDistinguished_mul_add h d hh
    ((c : Algebra A) * q') r' hdegree'
  rw [← heq''] at hb
  have hpair := huniq ((c : Algebra A) * q', r') ⟨heq'', hdegree', hb.1, hb.2⟩
  have hqeq : q' = q := by
    have hc : (c : Algebra A) * q' = qr.1 := congrArg Prod.fst hpair
    have hm := congrArg (fun t : Algebra A => ((c⁻¹ : (Algebra A)ˣ) : Algebra A) * t) hc
    simpa only [← mul_assoc, Units.inv_mul, one_mul, q] using hm
  have hreq : r' = qr.2 := congrArg Prod.snd hpair
  exact Prod.ext hqeq hreq

/-- Analytic preparation for an actual distinguished restricted series over
a multiplicatively normed coefficient ring. -/
theorem existsUnique_distinguished_preparation
    (f : Algebra A) (d : ℕ) (hf : IsDistinguished f d) :
    ∃! ew : (Algebra A)ˣ × Polynomial A,
      f = (ew.1 : Algebra A) * ofPolynomial A ew.2 ∧
      ew.2.Monic ∧ ew.2.natDegree = d ∧ ∀ n, ‖ew.2.coeff n‖ ≤ 1 := by
  obtain ⟨a, ha⟩ := hf.1
  let c := constantUnit a
  let g := ((c⁻¹ : (Algebra A)ˣ) : Algebra A) * f
  have hg : IsNormalizedDistinguished g d := by
    simpa only [g, c, constantUnit, map_inv] using
      normalizedDistinguished_of_unit_coefficient f d a ha hf.2.1 hf.2.2
  obtain ⟨ew, hfactor, huniq⟩ := existsUnique_normalizedDistinguished_preparation g d hg
  have heq : f = ((c * ew.1 : (Algebra A)ˣ) : Algebra A) * ofPolynomial A ew.2 := by
    calc
      f = (c : Algebra A) * g := by
        dsimp [g]
        rw [← mul_assoc]
        simp
      _ = _ := by rw [hfactor.1, Units.val_mul, mul_assoc]
  refine ⟨(c * ew.1, ew.2), ⟨heq, hfactor.2⟩, ?_⟩
  rintro ⟨e', w'⟩ ⟨heq', hw', hdegree', hcoeff'⟩
  have hg' : g = ((c⁻¹ * e' : (Algebra A)ˣ) : Algebra A) * ofPolynomial A w' := by
    dsimp [g]
    rw [heq']
    simp only [mul_assoc]
  have hpair := huniq (c⁻¹ * e', w') ⟨hg', hw', hdegree', hcoeff'⟩
  have he' : e' = c * ew.1 := by
    have h := congrArg Prod.fst hpair
    simpa only [Prod.fst, mul_inv_cancel_left] using congrArg (c * ·) h
  have hw'eq : w' = ew.2 := congrArg Prod.snd hpair
  exact Prod.ext he' hw'eq

end Langlands.Analytic.RestrictedSeries

namespace Langlands.Analytic.StrictTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The previously proved Gauss multiplicativity supplies the coefficient
norm structure needed to prepare series over an actual smaller Tate algebra. -/
instance (n : ℕ) : NormMulClass (StrictTateAlgebra (Fin n) K) where
  norm_mul := norm_mul_of_monomialOrder MonomialOrder.lex

end Langlands.Analytic.StrictTateAlgebra

import Langlands.Representation.Conductor.SchurIndependence

/-! # Polynomial support of a finite dominant Schur expansion -/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear.Spherical

universe uK

variable (K : Type uK) [Field K]

/-- A finite dominant Schur expansion comes from the ordinary polynomial ring. -/
def HasPolynomialTorusSchurExpansion {n : ℕ}
    (s : Finset {lam : Fin (n + 1) → ℤ // Antitone lam})
    (c : {lam : Fin (n + 1) → ℤ // Antitone lam} → K) : Prop :=
  ∃ p : MvPolynomial (Fin (n + 1)) K,
    ∑ μ ∈ s, c μ • torusSchur K μ.val =
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (TorusPolynomialAlgebra (Fin (n + 1)) K) p

/-- A polynomial multiple of the `N`th power of the coordinate product has no
monomial with any coordinate exponent less than `N`. -/
theorem coeff_mul_coordinateProduct_pow_eq_zero {n : ℕ}
    (p : MvPolynomial (Fin (n + 1)) K) (N : ℕ)
    (m : Fin (n + 1) →₀ ℕ) (i : Fin (n + 1)) (hi : m i < N) :
    (p * (∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) K)) ^ N).coeff m = 0 := by
  classical
  rw [← Finset.prod_pow, prod_X_pow_eq_monomial K, coeff_mul_monomial', ite_eq_right]
  intro hle
  have h := hle i
  change N ≤ m i at h
  omega

/-- In a finite expansion in dominant integral-weight Schur expressions, every
coefficient with negative last coordinate vanishes if the expansion is an ordinary
polynomial in the Laurent coordinate ring. -/
theorem torusSchur_coefficient_eq_zero_of_polynomial {n : ℕ}
    (s : Finset {lam : Fin (n + 1) → ℤ // Antitone lam})
    (c : {lam : Fin (n + 1) → ℤ // Antitone lam} → K)
    (p : MvPolynomial (Fin (n + 1)) K)
    (hsum : ∑ μ ∈ s, c μ • torusSchur K μ.val =
      algebraMap (MvPolynomial (Fin (n + 1)) K)
        (TorusPolynomialAlgebra (Fin (n + 1)) K) p)
    (i : {lam : Fin (n + 1) → ℤ // Antitone lam}) (hi : i ∈ s)
    (hneg : i.val (Fin.last n) < 0) : c i = 0 := by
  classical
  set N : ℕ := ∑ μ ∈ s, (-(μ.val (Fin.last n))).toNat
  have hNμ : ∀ μ ∈ s, 0 ≤ μ.val (Fin.last n) + N := by
    intro μ hμ
    have h1 : (-(μ.val (Fin.last n))).toNat ≤ N :=
      Finset.single_le_sum (f := fun μ : {lam : Fin (n + 1) → ℤ // Antitone lam} =>
        (-(μ.val (Fin.last n))).toNat) (fun _ _ => Nat.zero_le _) hμ
    omega
  have hpos : ∀ μ ∈ s, ∀ j, 0 ≤ μ.val j + (N : ℤ) := by
    intro μ hμ j
    have := μ.property (Fin.le_last j)
    have := hNμ μ hμ
    omega
  have hpoly : ∑ μ ∈ s, c μ • jacobiTrudi K (fun j => μ.val j + N) =
      p * (∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) K)) ^ N := by
    apply torusPolynomialAlgebraMap_injective (Fin (n + 1)) K
    rw [map_mul, map_pow, map_sum]
    have h := congrArg (· * ((torusDeterminantUnit (Fin (n + 1)) K ^ N :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) K)) hsum
    simp only [Finset.sum_mul] at h
    have hD : ((torusDeterminantUnit (Fin (n + 1)) K ^ N :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) K) =
        algebraMap (MvPolynomial (Fin (n + 1)) K)
          (TorusPolynomialAlgebra (Fin (n + 1)) K) (∏ j, X j) ^ N := by
      rw [Units.val_pow_eq_pow_val, torusDeterminantUnit_val]
    rw [← hD, ← h]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    rw [smul_mul_assoc,
      torusSchur_mul_determinantUnit_pow K μ.property N (hNμ μ hμ),
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  have halt : ∑ μ ∈ s, c μ • Matrix.det
      (alternantMatrix K (fun j => μ.val j + (N : ℤ))) =
      (p * Matrix.det (alternantMatrix K (0 : Fin (n + 1) → ℤ))) *
        (∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) K)) ^ N := by
    calc
      _ = (∑ μ ∈ s, c μ • jacobiTrudi K (fun j => μ.val j + N)) *
          Matrix.det (alternantMatrix K (0 : Fin (n + 1) → ℤ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun μ hμ => ?_)
        rw [smul_mul_assoc, jacobiTrudi_mul_baseAlternant _ (hpos μ hμ)]
      _ = (p * (∏ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) K)) ^ N) *
          Matrix.det (alternantMatrix K (0 : Fin (n + 1) → ℤ)) := by rw [hpoly]
      _ = _ := by ring
  have hanti : ∀ μ : {lam : Fin (n + 1) → ℤ // Antitone lam},
      Antitone (fun j => μ.val j + (N : ℤ)) :=
    fun μ a b hab => by have := μ.property hab; simp only; omega
  have hcoeff := congrArg (fun p : MvPolynomial (Fin (n + 1)) K => p.coeff
    (Finsupp.equivFunOnFinite.symm (alternantExponent (fun j => i.val j + (N : ℤ))))) halt
  rw [coeff_mul_coordinateProduct_pow_eq_zero K _ N _ (Fin.last n)] at hcoeff
  · simp only [coeff_sum] at hcoeff
    rw [Finset.sum_eq_single i] at hcoeff
    · rw [coeff_smul, coeff_det_alternantMatrix K (hanti i) (hpos i hi) (hanti i) (hpos i hi),
        ite_eq_left rfl, smul_eq_mul, mul_one] at hcoeff
      exact hcoeff
    · intro μ hμ hne
      rw [coeff_smul, coeff_det_alternantMatrix K (hanti μ) (hpos μ hμ) (hanti i) (hpos i hi),
        ite_eq_right, smul_zero]
      intro h
      apply hne
      apply Subtype.ext
      funext j
      have : μ.val j + (N : ℤ) = i.val j + N := congrFun h j
      omega
    · intro h
      exact absurd hi h
  · change (i.val (Fin.last n) + (N : ℤ) - (Fin.last n : ℤ) + n).toNat < N
    simp only [Fin.val_last]
    have := hNμ i hi
    omega

/-- Polynomial dominant Schur expansions have no negative last weight. -/
theorem HasPolynomialTorusSchurExpansion.coefficient_eq_zero {n : ℕ}
    {s : Finset {lam : Fin (n + 1) → ℤ // Antitone lam}}
    {c : {lam : Fin (n + 1) → ℤ // Antitone lam} → K}
    (h : HasPolynomialTorusSchurExpansion K s c)
    (i : {lam : Fin (n + 1) → ℤ // Antitone lam}) (hi : i ∈ s)
    (hneg : i.val (Fin.last n) < 0) : c i = 0 := by
  obtain ⟨p, hp⟩ := h
  exact torusSchur_coefficient_eq_zero_of_polynomial K s c p hp i hi hneg

end Langlands.Conductor

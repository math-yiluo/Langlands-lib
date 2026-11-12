import Langlands.Representation.Conductor.SphericalSeries
import Langlands.Representation.Conductor.SphericalNumeratorIdeal
import Langlands.Representation.RankinSelberg.SymmetricDominant

/-!
# Linear independence of the dominant Schur expressions

The integral-weight Schur expressions `torusSchur K lam` of the dominant (antitone)
weights `lam : Fin (n + 1) → ℤ` are linearly independent over any field `K`, both in
the Laurent coordinate ring and in its symmetric subalgebra. The proof reads off the
coefficient of the leading monomial `x^(lam + δ)` of the alternant of a dominant
nonnegative weight.
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear Langlands.GeneralLinear.Spherical

universe uK

section Alternant

variable (R : Type uK) [CommRing R]

/-- The exponents `i ↦ α_i - i + n` of the monomials in an alternant row. -/
def alternantExponent {n : ℕ} (α : Fin (n + 1) → ℤ) : Fin (n + 1) → ℕ :=
  fun i => (α i - i + n).toNat

theorem alternantExponent_strictAnti {n : ℕ} {α : Fin (n + 1) → ℤ}
    (hα : Antitone α) (hpos : ∀ i, 0 ≤ α i) :
    StrictAnti (alternantExponent α) := by
  intro i j hij
  simp only [alternantExponent]
  have h1 := hα hij.le
  have h2 := hpos j
  have hi : (i : ℤ) < j := by exact_mod_cast hij
  have hj : (j : ℤ) ≤ n := by have := j.isLt; omega
  omega

theorem alternantExponent_injective {n : ℕ} {α β : Fin (n + 1) → ℤ}
    (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h : alternantExponent α = alternantExponent β) : α = β := by
  funext i
  have hi := congrFun h i
  simp only [alternantExponent] at hi
  have := hα i
  have := hβ i
  have : (i : ℤ) ≤ n := by have := i.isLt; omega
  omega

/-- A permutation carrying one strictly antitone tuple to another is trivial. -/
theorem perm_eq_one_of_strictAnti_comp {m : ℕ} {f g : Fin m → ℕ}
    (hf : StrictAnti f) (hg : StrictAnti g) (σ : Equiv.Perm (Fin m))
    (h : f ∘ σ = g) : σ = 1 := by
  have hmono : StrictMono σ := by
    intro i j hij
    by_contra hle
    have h1 : f (σ i) ≤ f (σ j) := hf.antitone (not_lt.mp hle)
    have h2 : g j < g i := hg hij
    rw [← h] at h2
    exact absurd h2 (not_lt.mpr h1)
  ext i
  exact congrArg Fin.val (congrFun hmono.eq_id i)

theorem prod_X_pow_eq_monomial {σ : Type*} [Fintype σ] (k : σ → ℕ) :
    ∏ i, (X i : MvPolynomial σ R) ^ k i =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  rfl

/-- The coefficient of the monomial `x^(β + δ)` in the alternant of `α + δ`, for
dominant nonnegative weights. -/
theorem coeff_det_alternantMatrix {n : ℕ} {α β : Fin (n + 1) → ℤ}
    (hα : Antitone α) (hαpos : ∀ i, 0 ≤ α i)
    (hβ : Antitone β) (hβpos : ∀ i, 0 ≤ β i) :
    (Matrix.det (alternantMatrix R α)).coeff
      (Finsupp.equivFunOnFinite.symm (alternantExponent β)) = if α = β then 1 else 0 := by
  classical
  have hterm : ∀ σ : Equiv.Perm (Fin (n + 1)),
      (Equiv.Perm.sign σ • ∏ i, alternantMatrix R α (σ i) i).coeff
        (Finsupp.equivFunOnFinite.symm (alternantExponent β)) =
      ((Equiv.Perm.sign σ : ℤ) : R) *
        if alternantExponent α ∘ σ = alternantExponent β then 1 else 0 := by
    intro σ
    have hprod : ∏ i, alternantMatrix R α (σ i) i =
        monomial (Finsupp.equivFunOnFinite.symm (alternantExponent α ∘ σ)) 1 := by
      rw [← prod_X_pow_eq_monomial]
      rfl
    rw [hprod, Units.smul_def, coeff_smul, coeff_monomial, zsmul_eq_mul]
    congr 1
    simp only [EmbeddingLike.apply_eq_iff_eq]
  rw [Matrix.det_apply, coeff_sum, Finset.sum_eq_single (1 : Equiv.Perm (Fin (n + 1)))]
  · rw [hterm, Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
    by_cases hab : α = β
    · subst hab
      simp
    · have hne : ¬(alternantExponent α ∘ ⇑(1 : Equiv.Perm (Fin (n + 1))) =
          alternantExponent β) := fun h => hab (alternantExponent_injective hαpos hβpos h)
      rw [ite_eq_right hne, ite_eq_right hab]
  · intro σ _ hσ
    rw [hterm, ite_eq_right, mul_zero]
    intro h
    exact hσ (perm_eq_one_of_strictAnti_comp (alternantExponent_strictAnti hα hαpos)
      (alternantExponent_strictAnti hβ hβpos) σ h)
  · intro h
    exact absurd (Finset.mem_univ _) h

end Alternant

section Independence

variable (K : Type uK) [Field K]

/-- Multiplying the Schur expression of a dominant weight by a large power of the
coordinate product gives the Jacobi--Trudi polynomial of the shifted weight. -/
theorem torusSchur_mul_determinantUnit_pow {n : ℕ} {lam : Fin (n + 1) → ℤ}
    (hlam : Antitone lam) (N : ℕ) (hN : 0 ≤ lam (Fin.last n) + N) :
    torusSchur K lam *
        ((torusDeterminantUnit (Fin (n + 1)) K ^ N :
          (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
          TorusPolynomialAlgebra (Fin (n + 1)) K) =
      algebraMap (MvPolynomial (Fin (n + 1)) K) (TorusPolynomialAlgebra (Fin (n + 1)) K)
        (jacobiTrudi K (fun i => lam i + N)) := by
  set c : ℕ := (lam (Fin.last n) + N).toNat with hc
  have hc' : ((c : ℕ) : ℤ) = lam (Fin.last n) + N := Int.toNat_of_nonneg hN
  have hshift : (fun i => lam i + (N : ℤ)) =
      fun i => (lam i - lam (Fin.last n)) + (c : ℤ) := by
    funext i
    omega
  have hnonneg : ∀ i, 0 ≤ lam i - lam (Fin.last n) := fun i => by
    have := hlam (Fin.le_last i)
    omega
  rw [hshift, jacobiTrudi_add_nat _ hnonneg c, map_mul, map_pow, map_prod, torusSchur]
  have hD : ((torusDeterminantUnit (Fin (n + 1)) K ^ lam (Fin.last n) :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) K) *
      ((torusDeterminantUnit (Fin (n + 1)) K ^ N :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) K) =
      (∏ i : Fin (n + 1), algebraMap (MvPolynomial (Fin (n + 1)) K)
        (TorusPolynomialAlgebra (Fin (n + 1)) K) (X i)) ^ c := by
    rw [← Units.val_mul, ← zpow_natCast, ← zpow_add, ← hc', zpow_natCast, Units.val_pow_eq_pow_val,
      torusDeterminantUnit_val, map_prod]
  rw [mul_comm (algebraMap _ _ _), mul_assoc, mul_comm (algebraMap _ _ _), ← mul_assoc, hD]

/-- The Schur expressions of the dominant integral weights are linearly independent
in the Laurent coordinate ring. -/
theorem torusSchur_linearIndependent (n : ℕ) :
    LinearIndependent K (fun lam : {lam : Fin (n + 1) → ℤ // Antitone lam} =>
      torusSchur K lam.val) := by
  classical
  rw [linearIndependent_iff']
  intro s g hsum i hi
  set N : ℕ := ∑ μ ∈ s, (-(μ.val (Fin.last n))).toNat with hN
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
  -- Clear denominators and pass to polynomials.
  have hpoly : ∑ μ ∈ s, g μ • jacobiTrudi K (fun j => μ.val j + N) = 0 := by
    apply torusPolynomialAlgebraMap_injective (Fin (n + 1)) K
    rw [map_zero, map_sum]
    have h := congrArg (· * ((torusDeterminantUnit (Fin (n + 1)) K ^ N :
        (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) :
        TorusPolynomialAlgebra (Fin (n + 1)) K)) hsum
    simp only [zero_mul, Finset.sum_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    rw [smul_mul_assoc, torusSchur_mul_determinantUnit_pow K μ.property N (hNμ μ hμ),
      Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, Algebra.smul_def]
  -- Multiply by the base alternant.
  have halt : ∑ μ ∈ s, g μ • Matrix.det
      (alternantMatrix K (fun j => μ.val j + (N : ℤ))) = 0 := by
    have h := congrArg (· * Matrix.det (alternantMatrix K (0 : Fin (n + 1) → ℤ))) hpoly
    simp only [zero_mul, Finset.sum_mul] at h
    rw [← h]
    refine Finset.sum_congr rfl (fun μ hμ => ?_)
    rw [smul_mul_assoc, jacobiTrudi_mul_baseAlternant _ (hpos μ hμ)]
  -- Read off the coefficient of the leading monomial of `i`.
  have hanti : ∀ μ : {lam : Fin (n + 1) → ℤ // Antitone lam},
      Antitone (fun j => μ.val j + (N : ℤ)) :=
    fun μ a b hab => by have := μ.property hab; simp only; omega
  have hcoeff := congrArg (fun p : MvPolynomial (Fin (n + 1)) K => p.coeff
    (Finsupp.equivFunOnFinite.symm (alternantExponent (fun j => i.val j + (N : ℤ))))) halt
  simp only [coeff_sum, AddMonoidAlgebra.coeff_zero, Finsupp.coe_zero, Pi.zero_apply] at hcoeff
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
    have : μ.val j + (N : ℤ) = i.val j + N :=
      congrFun h j
    omega
  · intro h
    exact absurd hi h

/-- The same independence in the symmetric Laurent algebra. -/
theorem symmetricTorusSchur_linearIndependent (n : ℕ) :
    LinearIndependent K (fun lam : {lam : Fin (n + 1) → ℤ // Antitone lam} =>
      symmetricTorusSchur K lam.val) := by
  apply LinearIndependent.of_comp (symmetricTorusSubalgebra (Fin (n + 1)) K).val.toLinearMap
  exact torusSchur_linearIndependent K n

end Independence

end Langlands.Conductor

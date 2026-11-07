import Langlands.Representation.Conductor.TorusIdeal
import Langlands.Representation.Whittaker.Spherical
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# The symmetric Laurent polynomial form of the spherical Whittaker function

The integral-weight Schur expression is formed in the actual Laurent coordinate
ring. Evaluation at every unit tuple recovers the existing explicit function.
-/

noncomputable section

namespace Langlands.Conductor

open MvPolynomial Langlands.GeneralLinear Langlands.GeneralLinear.Spherical

universe uK uσ uF uΓ

section Laurent

variable (σ : Type uσ) (K : Type uK) [Fintype σ] [Field K]

/-- The product of the Laurent coordinates, as a unit. -/
def torusDeterminantUnit : (TorusPolynomialAlgebra σ K)ˣ :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := TorusPolynomialAlgebra σ K) (∏ i : σ, (X i : MvPolynomial σ K))).unit

@[simp] theorem torusDeterminantUnit_val :
    (torusDeterminantUnit σ K : TorusPolynomialAlgebra σ K) =
      algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (∏ i : σ, X i) :=
  IsUnit.unit_spec _

@[simp] theorem torusPolynomialPermutation_determinantUnit (e : Equiv.Perm σ) :
    Units.map (torusPolynomialPermutation σ K e).toMonoidHom
      (torusDeterminantUnit σ K) = torusDeterminantUnit σ K := by
  apply Units.ext
  change torusPolynomialPermutation σ K e
    (torusDeterminantUnit σ K : TorusPolynomialAlgebra σ K) = _
  simp only [torusDeterminantUnit_val,
    torusPolynomialPermutation_algebraMap, map_prod, rename_X]
  exact Equiv.prod_comp e
    (fun i => algebraMap (MvPolynomial σ K) (TorusPolynomialAlgebra σ K) (X i))

@[simp] theorem torusPolynomialEvaluation_determinantUnit (x : σ → Kˣ) :
    Units.map (torusPolynomialEvaluation σ K x).toMonoidHom
      (torusDeterminantUnit σ K) = ∏ i, x i := by
  apply Units.ext
  change torusPolynomialEvaluation σ K x
    (torusDeterminantUnit σ K : TorusPolynomialAlgebra σ K) = _
  simp only [torusDeterminantUnit_val,
    torusPolynomialEvaluation_algebraMap, map_prod, aeval_X, Units.coe_prod]

/-- Algebra evaluation of an arbitrary integral power of a unit. -/
theorem algHom_apply_unit_zpow
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (f : R →ₐ[K] S) (u : Rˣ) (m : ℤ) :
    f (u ^ m : Rˣ) = (Units.map f.toMonoidHom u ^ m : Sˣ) := by
  exact congrArg Units.val ((Units.map f.toMonoidHom).map_zpow u m)

/-- Unit-tuple evaluations separate Laurent polynomials over an infinite field. -/
theorem torusPolynomial_eq_zero_of_evaluations [Infinite K]
    (p : TorusPolynomialAlgebra σ K)
    (hp : ∀ x : σ → Kˣ, torusPolynomialEvaluation σ K x p = 0) : p = 0 := by
  obtain ⟨m, a, ha⟩ := IsLocalization.Away.surj (∏ i : σ, (X i : MvPolynomial σ K)) p
  have hazero : a = 0 := by
    apply MvPolynomial.funext_set (fun _ : σ => ({0} : Set K)ᶜ)
      (fun _ => by
        rw [Set.compl_eq_univ_sdiff]
        exact (Set.infinite_univ : (Set.univ : Set K).Infinite).sdiff
          (Set.finite_singleton 0))
    intro x hx
    let xu : σ → Kˣ := fun i => Units.mk0 (x i) (hx i (Set.mem_univ i))
    have he := congrArg (torusPolynomialEvaluation σ K xu) ha
    rw [map_mul, hp, zero_mul, torusPolynomialEvaluation_algebraMap] at he
    change (0 : K) = MvPolynomial.eval x a at he
    simpa only [map_zero] using he.symm
  rw [hazero, map_zero] at ha
  exact ((IsLocalization.Away.algebraMap_isUnit
    (S := TorusPolynomialAlgebra σ K) (∏ i : σ, (X i : MvPolynomial σ K))).pow m
      ).mul_right_cancel (by simpa only [zero_mul] using ha)

theorem torusPolynomial_eq_of_evaluations [Infinite K]
    (p r : TorusPolynomialAlgebra σ K)
    (h : ∀ x : σ → Kˣ,
      torusPolynomialEvaluation σ K x p = torusPolynomialEvaluation σ K x r) : p = r := by
  apply sub_eq_zero.mp
  apply torusPolynomial_eq_zero_of_evaluations σ K
  intro x
  rw [map_sub, h x, sub_self]

/-- Evaluation restricted to the actual symmetric Laurent subalgebra. -/
def symmetricTorusEvaluation (x : σ → Kˣ) : symmetricTorusSubalgebra σ K →ₐ[K] K :=
  (torusPolynomialEvaluation σ K x).comp (symmetricTorusSubalgebra σ K).val

theorem symmetricTorus_eq_of_evaluations [Infinite K]
    (p r : symmetricTorusSubalgebra σ K)
    (h : ∀ x : σ → Kˣ,
      symmetricTorusEvaluation σ K x p = symmetricTorusEvaluation σ K x r) : p = r := by
  apply Subtype.ext
  exact torusPolynomial_eq_of_evaluations σ K p.val r.val h

end Laurent

section Schur

variable (K : Type uK) [Field K]

/-- The complete homogeneous polynomial, including the negative-index convention,
is symmetric in its variables. -/
theorem completeSymm_isSymmetric (m : ℕ) (k : ℤ) :
    (completeSymm (Fin m) K k).IsSymmetric := by
  unfold completeSymm
  split_ifs
  · exact hsymm_isSymmetric _ _ _
  · exact IsSymmetric.zero

/-- The Jacobi--Trudi determinant is a symmetric polynomial. -/
theorem jacobiTrudi_isSymmetric {m : ℕ} (lam : Fin m → ℤ) :
    (jacobiTrudi K lam).IsSymmetric := by
  intro e
  rw [jacobiTrudi, AlgHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  exact completeSymm_isSymmetric K m _ e

/-- The integral-weight Schur expression in the Laurent coordinate ring. -/
def torusSchur {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    TorusPolynomialAlgebra (Fin (n + 1)) K :=
  (torusDeterminantUnit (Fin (n + 1)) K ^ lam (Fin.last n) :
    (TorusPolynomialAlgebra (Fin (n + 1)) K)ˣ) *
    algebraMap (MvPolynomial (Fin (n + 1)) K)
      (TorusPolynomialAlgebra (Fin (n + 1)) K)
      (jacobiTrudi K (fun i => lam i - lam (Fin.last n)))

theorem torusSchur_mem {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    torusSchur K lam ∈ symmetricTorusSubalgebra (Fin (n + 1)) K := by
  intro e
  rw [torusSchur, map_mul, algHom_apply_unit_zpow,
    torusPolynomialPermutation_determinantUnit, torusPolynomialPermutation_algebraMap,
    jacobiTrudi_isSymmetric K _ e]

/-- The same expression as an element of the symmetric Laurent algebra. -/
def symmetricTorusSchur {n : ℕ} (lam : Fin (n + 1) → ℤ) :
    symmetricTorusSubalgebra (Fin (n + 1)) K :=
  ⟨torusSchur K lam, torusSchur_mem K lam⟩

@[simp] theorem torusSchur_zero (n : ℕ) :
    torusSchur K (0 : Fin (n + 1) → ℤ) = 1 := by
  have h : (fun i : Fin (n + 1) =>
      (0 : Fin (n + 1) → ℤ) i - (0 : Fin (n + 1) → ℤ) (Fin.last n)) = 0 := by
    funext i
    simp
  rw [torusSchur, h, jacobiTrudi_zero]
  simp

@[simp] theorem symmetricTorusSchur_zero (n : ℕ) :
    symmetricTorusSchur K (0 : Fin (n + 1) → ℤ) = 1 := by
  apply Subtype.ext
  exact torusSchur_zero K n

end Schur

@[simp] theorem symmetricTorusEvaluation_schur {n : ℕ}
    (x : Fin (n + 1) → ℂˣ) (lam : Fin (n + 1) → ℤ) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x (symmetricTorusSchur ℂ lam) =
      satakeSchur x lam := by
  change torusPolynomialEvaluation (Fin (n + 1)) ℂ x (torusSchur ℂ lam) = _
  rw [torusSchur, map_mul, algHom_apply_unit_zpow,
    torusPolynomialEvaluation_determinantUnit, torusPolynomialEvaluation_algebraMap]
  simp only [Units.val_zpow_eq_zpow_val, Units.coe_prod, satakeSchur, aeval_eq_eval]

section SphericalFunction

open Iwasawa

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}
variable (hϖ : IsUniformizingElement v ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)

open scoped Classical in
/-- The spherical Whittaker formula with values in the actual symmetric Laurent
algebra. Its specialization at every unit tuple is `sphericalWhittaker`. -/
def sphericalWhittakerPolynomial
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    symmetricTorusSubalgebra (Fin (n + 1)) ℂ :=
  if Antitone (exponent hϖ g) then
    algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
      ((θ (unipotentPart hϖ g) : ℂ) * halfModulus q (exponent hϖ g)) *
      symmetricTorusSchur ℂ (exponent hϖ g)
  else 0

@[simp] theorem symmetricTorusEvaluation_sphericalWhittakerPolynomial
    (x : Fin (n + 1) → ℂˣ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    symmetricTorusEvaluation (Fin (n + 1)) ℂ x
      (sphericalWhittakerPolynomial hϖ θ q g) =
      sphericalWhittaker hϖ θ q x g := by
  classical
  unfold sphericalWhittakerPolynomial sphericalWhittaker cellFunction
  split_ifs
  · rw [map_mul, AlgHom.commutes, symmetricTorusEvaluation_schur]
    simp only [Algebra.algebraMap_self, RingHom.id_apply, mul_assoc]
  · exact map_zero _

theorem sphericalWhittakerPolynomial_of_not_antitone
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    (hg : ¬ Antitone (exponent hϖ g)) :
    sphericalWhittakerPolynomial hϖ θ q g = 0 := by
  classical
  exact ite_eq_right hg

theorem sphericalWhittakerPolynomial_of_antitone
    (hθ : IsIntegrallyTrivial v θ) (u : upperUnipotent (n + 1) F)
    {lam : Fin (n + 1) → ℤ} (hlam : Antitone lam)
    {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) :
    sphericalWhittakerPolynomial hϖ θ q
      ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * torus ϖ lam * k) =
      algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
        ((θ u : ℂ) * halfModulus q lam) * symmetricTorusSchur ℂ lam := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    map_mul, AlgHom.commutes, symmetricTorusEvaluation_schur]
  simpa only [sphericalWhittaker, Algebra.algebraMap_self, RingHom.id_apply, mul_assoc] using
    cellFunction_of_antitone hϖ
      (fun lam => halfModulus q lam * satakeSchur x lam) hθ u hlam hk

theorem sphericalWhittakerPolynomial_torus
    (hθ : IsIntegrallyTrivial v θ) (lam : Fin (n + 1) → ℤ) :
    sphericalWhittakerPolynomial hϖ θ q (torus ϖ lam) =
      if Antitone lam then
        algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) (halfModulus q lam) *
          symmetricTorusSchur ℂ lam
      else 0 := by
  classical
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    sphericalWhittaker_torus hϖ q x hθ]
  split_ifs
  · rw [map_mul, AlgHom.commutes, symmetricTorusEvaluation_schur]
    rfl
  · exact (map_zero _).symm

@[simp] theorem sphericalWhittakerPolynomial_one (hθ : IsIntegrallyTrivial v θ) :
    sphericalWhittakerPolynomial hϖ θ q 1 = 1 := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    sphericalWhittaker_one hϖ q x hθ, map_one]

theorem sphericalWhittakerPolynomial_unipotent_mul
    (hθ : IsIntegrallyTrivial v θ) (u : upperUnipotent (n + 1) F)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    sphericalWhittakerPolynomial hϖ θ q
      ((u : Matrix.GeneralLinearGroup (Fin (n + 1)) F) * g) =
      algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) (θ u : ℂ) *
        sphericalWhittakerPolynomial hϖ θ q g := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    map_mul, AlgHom.commutes, symmetricTorusEvaluation_sphericalWhittakerPolynomial]
  exact cellFunction_unipotent_mul hϖ _ hθ u g

theorem sphericalWhittakerPolynomial_mul_integral
    (hθ : IsIntegrallyTrivial v θ)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    {k : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hk : k ∈ integralSubgroup v.integer n) :
    sphericalWhittakerPolynomial hϖ θ q (g * k) =
      sphericalWhittakerPolynomial hϖ θ q g := by
  apply symmetricTorus_eq_of_evaluations
  intro x
  rw [symmetricTorusEvaluation_sphericalWhittakerPolynomial,
    symmetricTorusEvaluation_sphericalWhittakerPolynomial]
  exact sphericalWhittaker_mul_integral hϖ q x hθ g hk

end SphericalFunction

end Langlands.Conductor

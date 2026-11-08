import Langlands.Representation.Conductor.SphericalPieri

/-! # The actual minuscule sum and its full-group spherical eigenidentity -/

noncomputable section

namespace Langlands.Conductor

open Langlands.GeneralLinear Langlands.GeneralLinear.Spherical
open Langlands.GeneralLinear.Iwasawa Langlands.Unramified.MinusculeCosets
open Langlands.RankinSelberg.UnramifiedWhittaker
open Langlands.Whittaker.UpperUnipotentCharacter (adjacentUnit)
open scoped BigOperators

universe uF uΓ uΛ uR

variable {F : Type uF} [Field F] {Γ₀ : Type uΓ} [LinearOrderedCommGroupWithZero Γ₀]
variable {v : Valuation F Γ₀} {n : ℕ} {ϖ : Fˣ}
variable {Λ : Type uΛ} [Fintype Λ]

/-- The finite minuscule right-translation operator on actual functions. -/
def minusculeSumOperator (R : Type uR) [CommSemiring R]
    (ϖ : Fˣ) (σ : Λ → F) (k : ℕ) :
    (Matrix.GeneralLinearGroup (Fin (n + 1)) F → R) →ₗ[R]
      (Matrix.GeneralLinearGroup (Fin (n + 1)) F → R) where
  toFun f g := ∑ a : CosetIndex Λ (n + 1) k, f (g * labelledRep ϖ σ a)
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    funext g
    simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem minusculeSumOperator_apply {R : Type uR} [CommSemiring R]
    (σ : Λ → F) (k : ℕ) (f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → R)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    minusculeSumOperator R ϖ σ k f g =
      ∑ a : CosetIndex Λ (n + 1) k, f (g * labelledRep ϖ σ a) := rfl

theorem minusculeSumOperator_mul_integral {R : Type uR} [CommSemiring R]
    (hϖ : IsUniformizingElement v ϖ) (σ : Λ → F)
    (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (k : ℕ) (f : Matrix.GeneralLinearGroup (Fin (n + 1)) F → R)
    (hK : ∀ g, ∀ c ∈ integralSubgroup v.integer n, f (g * c) = f g)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    {c : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hc : c ∈ integralSubgroup v.integer n) :
    minusculeSumOperator R ϖ σ k f (g * c) =
      minusculeSumOperator R ϖ σ k f g := by
  classical
  have hex (a : CosetIndex Λ (n + 1) k) :
      ∃ b : CosetIndex Λ (n + 1) k,
        (labelledRep ϖ σ b)⁻¹ * (c * labelledRep ϖ σ a) ∈
          integralSubgroup v.integer n := by
    obtain ⟨c₁, hc₁, c₂, hc₂, ha⟩ := labelledRep_mem_doubleCoset hσ a.1.property a
    apply exists_labelledRep hϖ hsurj a.1.property (mul_mem hc hc₁) hc₂
    rw [ha]
    group
  choose p hp using hex
  have hpi : Function.Injective p := by
    intro a b hab
    have habK : (labelledRep ϖ σ a)⁻¹ * labelledRep ϖ σ b ∈
        integralSubgroup v.integer n := by
      have h := mul_mem (inv_mem (hp a)) (hp b)
      rw [← hab] at h
      convert h using 1
      group
    apply labelledRep_unique hϖ hinj habK
    simpa only [inv_mul_cancel] using (one_mem (integralSubgroup v.integer n))
  apply Fintype.sum_bijective p ⟨hpi, Finite.surjective_of_injective hpi⟩
  intro a
  have he : (g * c) * labelledRep ϖ σ a =
      (g * labelledRep ϖ σ (p a)) *
        ((labelledRep ϖ σ (p a))⁻¹ * (c * labelledRep ϖ σ a)) := by group
  rw [he, hK _ _ (hp a)]

variable (hϖ : IsUniformizingElement v ϖ)
  (θ : upperUnipotent (n + 1) F →* ℂˣ) (q : ℕ)

theorem sphericalWhittakerMinusculeSum_eq_operator (σ : Λ → F) (k : ℕ) :
    sphericalWhittakerMinusculeSum hϖ θ q σ k =
      minusculeSumOperator (symmetricTorusSubalgebra (Fin (n + 1)) ℂ)
        ϖ σ k (sphericalWhittakerPolynomial hϖ θ q) := rfl

theorem sphericalWhittakerMinusculeSum_mul_integral
    (hθ : IsIntegrallyTrivial v θ) (σ : Λ → F)
    (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F)
    {c : Matrix.GeneralLinearGroup (Fin (n + 1)) F}
    (hc : c ∈ integralSubgroup v.integer n) :
    sphericalWhittakerMinusculeSum hϖ θ q σ k (g * c) =
      sphericalWhittakerMinusculeSum hϖ θ q σ k g := by
  rw [sphericalWhittakerMinusculeSum_eq_operator]
  exact minusculeSumOperator_mul_integral hϖ σ hσ hinj hsurj k _
    (fun g _ hc => sphericalWhittakerPolynomial_mul_integral hϖ θ q hθ g hc) g hc

theorem sphericalWhittakerMinusculeSum_unipotent_mul
    (hθ : IsIntegrallyTrivial v θ) (σ : Λ → F) (k : ℕ)
    (u : upperUnipotent (n + 1) F)
    (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    sphericalWhittakerMinusculeSum hϖ θ q σ k (u.val * g) =
      algebraMap ℂ (symmetricTorusSubalgebra (Fin (n + 1)) ℂ) (θ u : ℂ) *
        sphericalWhittakerMinusculeSum hϖ θ q σ k g := by
  simp only [sphericalWhittakerMinusculeSum, mul_assoc,
    sphericalWhittakerPolynomial_unipotent_mul hϖ θ q hθ, Finset.mul_sum]

/-- The actual finite minuscule sum satisfies the spherical Hecke eigenidentity
on the entire group over an arbitrary valued field. -/
theorem sphericalWhittakerMinusculeSum_eq
    (hq : 0 < q) (hcard : Fintype.card Λ = q)
    (hθ : IsIntegrallyTrivial v θ)
    (hgeneric : ∀ i : Fin n, ∃ x : F,
      v x * v (ϖ : F) ≤ 1 ∧ θ (adjacentUnit i x) ≠ 1)
    (σ : Λ → F) (hσ : ∀ x, σ x ∈ v.integer)
    (hinj : ∀ x y, v (σ x - σ y) < 1 → x = y)
    (hsurj : ∀ z ∈ v.integer, ∃ x, v (z - σ x) < 1)
    (k : ℕ) (g : Matrix.GeneralLinearGroup (Fin (n + 1)) F) :
    sphericalWhittakerMinusculeSum hϖ θ q σ k g =
      symmetricTorusHeckeScalar n q k * sphericalWhittakerPolynomial hϖ θ q g := by
  have hU := sphericalWhittakerMinusculeSum_unipotent_mul hϖ θ q hθ σ k
  have hK : ∀ (g c : Matrix.GeneralLinearGroup (Fin (n + 1)) F),
      c ∈ integralSubgroup v.integer n →
      sphericalWhittakerMinusculeSum hϖ θ q σ k (g * c) =
        sphericalWhittakerMinusculeSum hϖ θ q σ k g :=
    fun g _ hc =>
      sphericalWhittakerMinusculeSum_mul_integral hϖ θ q hθ σ hσ hinj hsurj k g hc
  have ht (lam : Fin (n + 1) → ℤ) :
      sphericalWhittakerMinusculeSum hϖ θ q σ k (torus ϖ lam) =
        symmetricTorusHeckeScalar n q k *
          sphericalWhittakerPolynomial hϖ θ q (torus ϖ lam) := by
    by_cases hlam : Antitone lam
    · exact sphericalWhittakerMinusculeSum_torus hϖ θ q hq hcard hθ σ hσ lam hlam k
    · rw [sphericalWhittakerPolynomial_of_not_antitone hϖ θ q _
        (by rwa [exponent_torus]), mul_zero]
      apply symmetricTorus_eq_of_evaluations
      intro x
      rw [map_zero]
      apply eval_torus_eq_zero_of_not_antitone hϖ
        (f := fun g => symmetricTorusEvaluation (Fin (n + 1)) ℂ x
          (sphericalWhittakerMinusculeSum hϖ θ q σ k g))
      · intro u g
        rw [hU, map_mul, AlgHom.commutes]
        rfl
      · intro g c hc
        rw [hK g c hc]
      · exact hgeneric
      · exact hlam
  obtain ⟨c, hc, hg⟩ := exists_eq_unipotentPart hϖ g
  conv_lhs => rw [hg, hK _ c hc, hU, ht]
  conv_rhs => rw [hg, sphericalWhittakerPolynomial_mul_integral hϖ θ q hθ _ hc,
    sphericalWhittakerPolynomial_unipotent_mul hϖ θ q hθ]
  ring

end Langlands.Conductor

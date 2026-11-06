import Langlands.Representation.RankinSelberg.LaurentDivisibilityProof
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof
import Mathlib.FieldTheory.Separable

/-! # Binomial denominator bounds from central translation -/

noncomputable section

namespace Langlands.RankinSelberg

open Polynomial

universe uV uW uS

/-- A polynomial clearing all generating values is divisible by the
normalized polynomial of their Laurent span. -/
theorem IsNormalizedGenerator.dvd_of_clears
    {values : Set RationalFunctions} {P D : ℂ[X]}
    (hP : IsNormalizedGenerator values P) (hD : D ≠ 0)
    (hclear : ∀ R ∈ values, ∃ b : LaurentCoefficients,
      laurentToRatFunc b = algebraMap ℂ[X] RationalFunctions D * R) :
    P ∣ D := by
  have hmem : (algebraMap ℂ[X] RationalFunctions P)⁻¹ ∈ zetaSpan values := by
    rw [hP.2]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨b, hb⟩ := RationalContinuationLinear.denominator_clears_span D.toLaurent
    (by simpa only [laurentToRatFunc_toLaurent] using hclear) hmem
  rw [laurentToRatFunc_toLaurent] at hb
  apply (normalizedReciprocalLaurentSpanDivisibility P D hP.1 hD).mp
  refine Submodule.mem_span_singleton.mpr ⟨b, ?_⟩
  rw [Algebra.smul_def, algebraMap_laurent, hb, mul_right_comm,
    mul_inv_cancel₀ (RatFunc.algebraMap_ne_zero hD), one_mul]

section Trilinear

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {S : Type uS} [AddCommGroup S] [Module ℂ S]

/-- The scalar central-translation recurrence for a rational trilinear family.
Its intended application has `c` the product of the two central characters,
and `m` the positive determinant exponent of an inverse uniformizer. -/
def CentralShiftLaw
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (a : S →ₗ[ℂ] S) (c : ℂ) (m : ℕ) : Prop :=
  ∀ v w φ, c • C v w (a φ) = (RatFunc.X : RationalFunctions) ^ m * C v w φ

/-- An invariant test functional makes the central difference lie in its
kernel. Laurent regularity on that kernel therefore gives a binomial
denominator for every value of the family. -/
theorem CentralShiftLaw.clears
    {C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions}
    {a : S →ₗ[ℂ] S} {c : ℂ} {m : ℕ}
    (hshift : CentralShiftLaw C a c m)
    (e : S →ₗ[ℂ] ℂ) (he : ∀ φ, e (a φ) = e φ)
    (hregular : ∀ v w φ, e φ = 0 → ∃ b : LaurentCoefficients,
      laurentToRatFunc b = C v w φ) :
    ∀ v w φ, ∃ b : LaurentCoefficients,
      laurentToRatFunc b =
        algebraMap ℂ[X] RationalFunctions (X ^ m - Polynomial.C c) * C v w φ := by
  intro v w φ
  obtain ⟨b, hb⟩ := hregular v w (a φ - φ) (by rw [map_sub, he, sub_self])
  have hsc := hshift v w φ
  rw [RatFunc.smul_eq_C_mul] at hsc
  have hdiff :
      algebraMap ℂ[X] RationalFunctions (X ^ m - Polynomial.C c) * C v w φ =
        RatFunc.C c * C v w (a φ - φ) := by
    rw [map_sub, map_pow, RatFunc.algebraMap_X, RatFunc.algebraMap_C, map_sub,
      mul_sub, hsc]
    ring
  refine ⟨LaurentPolynomial.C c * b, ?_⟩
  rw [map_mul, laurentToRatFunc_C, hb, hdiff]

/-- If the family generates the normalized Laurent module, its normalized
polynomial divides the central binomial and is separable and squarefree.
No analytic regularity or central-character assertion is supplied here. -/
theorem CentralShiftLaw.normalizedGenerator_bound
    {values : Set RationalFunctions} {P : ℂ[X]}
    (hP : IsNormalizedGenerator values P)
    (C : V →ₗ[ℂ] W →ₗ[ℂ] S →ₗ[ℂ] RationalFunctions)
    (hvalues : ∀ R ∈ values, ∃ v w φ, C v w φ = R)
    (a : S →ₗ[ℂ] S) (c : ℂ) (hc : c ≠ 0) (m : ℕ) (hm : m ≠ 0)
    (hshift : CentralShiftLaw C a c m)
    (e : S →ₗ[ℂ] ℂ) (he : ∀ φ, e (a φ) = e φ)
    (hregular : ∀ v w φ, e φ = 0 → ∃ b : LaurentCoefficients,
      laurentToRatFunc b = C v w φ) :
    P ∣ X ^ m - Polynomial.C c ∧ P.Separable ∧ Squarefree P := by
  have hsep : (X ^ m - Polynomial.C c).Separable :=
    Polynomial.separable_X_pow_sub_C c (Nat.cast_ne_zero.mpr hm) hc
  have hD : X ^ m - Polynomial.C c ≠ 0 := hsep.squarefree.ne_zero
  have hdiv : P ∣ X ^ m - Polynomial.C c := hP.dvd_of_clears hD (by
    intro R hR
    obtain ⟨v, w, φ, rfl⟩ := hvalues R hR
    exact hshift.clears e he hregular v w φ)
  exact ⟨hdiv, hsep.of_dvd hdiv, (hsep.of_dvd hdiv).squarefree⟩

end Trilinear

end Langlands.RankinSelberg

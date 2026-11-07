import Langlands.Representation.Families.MatrixGenerationWitness
import Langlands.Representation.Families.UnramifiedPolynomialWitness
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Principal polynomial neighborhoods from localized coefficient matrices

A matrix family may be free only after localization. Clearing the determinant
witness gives a regular numerator; multiplying it by the localization parameter
retains the domain on which the matrix specialization is defined.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.LocalizedMatrixPrincipalOpen

open Plancherel MatrixGenerationWitness UnramifiedPolynomialWitness

universe uB uS uJ un u

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {S : Type uS} [CommRing S] [Algebra B S] [Algebra ℂ S]
  [IsScalarTower ℂ B S] (g : B) [IsLocalization.Away g S]

/-- Specialize a localization at a character where its parameter is nonzero. -/
def awayEvaluation (χ : B →ₐ[ℂ] ℂ) (hχ : χ g ≠ 0) : S →ₐ[ℂ] ℂ :=
  IsLocalization.Away.liftAlgHom g (isUnit_iff_ne_zero.mpr hχ)

@[simp]
theorem awayEvaluation_algebraMap (χ : B →ₐ[ℂ] ℂ) (hχ : χ g ≠ 0) (b : B) :
    awayEvaluation (S := S) g χ hχ (algebraMap B S b) = χ b := by
  simp [awayEvaluation]

/-- A regular numerator of a localized element, with a power of `g` as
denominator. -/
def localizedNumerator (z : S) : B :=
  (IsLocalization.Away.sec g z).1

/-- Nonvanishing of the numerator detects nonvanishing of the localized
element at every character where the localization is defined. -/
theorem awayEvaluation_ne_zero_iff (z : S) (χ : B →ₐ[ℂ] ℂ) (hχ : χ g ≠ 0) :
    awayEvaluation g χ hχ z ≠ 0 ↔ χ (localizedNumerator g z) ≠ 0 := by
  have he := congrArg (awayEvaluation (S := S) g χ hχ)
    (IsLocalization.Away.sec_spec g z)
  simp only [map_mul, awayEvaluation_algebraMap, map_pow] at he
  change awayEvaluation g χ hχ z * χ g ^ (IsLocalization.Away.sec g z).2 =
    χ (localizedNumerator g z) at he
  rw [← he, mul_ne_zero_iff, and_iff_left (pow_ne_zero _ hχ)]

/-- A regular witness that also retains the localization's nonzero parameter. -/
def regularWitness (z : S) : B :=
  localizedNumerator g z * g

/-- A nonzero witness gives both a defined specialization and a nonzero
specialized localized element. -/
theorem regularWitness_ne_zero_iff (z : S) (χ : B →ₐ[ℂ] ℂ) :
    χ (regularWitness g z) ≠ 0 ↔
      ∃ hχ : χ g ≠ 0, awayEvaluation g χ hχ z ≠ 0 := by
  rw [regularWitness, map_mul, mul_ne_zero_iff]
  constructor
  · rintro ⟨ha, hg⟩
    exact ⟨hg, (awayEvaluation_ne_zero_iff g z χ hg).mpr ha⟩
  · rintro ⟨hg, hz⟩
    exact ⟨(awayEvaluation_ne_zero_iff g z χ hg).mp hz, hg⟩

/-- The determinant method for localized matrices produces a regular principal
nonvanishing neighborhood containing the original character and contained
in the original localization domain. -/
theorem exists_regular_principal_neighborhood
    {J : Type uJ} {n : Type un} [Fintype n] [DecidableEq n]
    (A : J → Matrix n n S) (χ₀ : B →ₐ[ℂ] ℂ) (hg₀ : χ₀ g ≠ 0)
    (h₀ : UnitarizabilityContinuation.IsIrreducibleFamily
      (specialize A (awayEvaluation g χ₀ hg₀))) :
    ∃ f : B, χ₀ f ≠ 0 ∧ ∀ χ : B →ₐ[ℂ] ℂ, χ f ≠ 0 →
      ∃ hg : χ g ≠ 0, UnitarizabilityContinuation.IsIrreducibleFamily
        (specialize A (awayEvaluation g χ hg)) := by
  obtain ⟨z, hz₀, hz⟩ :=
    exists_principal_neighborhood A (awayEvaluation g χ₀ hg₀) h₀
  refine ⟨regularWitness g z, ?_, ?_⟩
  · apply (regularWitness_ne_zero_iff g z χ₀).mpr
    exact ⟨hg₀, by rw [hz₀]; exact one_ne_zero⟩
  · intro χ hχ
    obtain ⟨hg, hzχ⟩ := (regularWitness_ne_zero_iff g z χ).mp hχ
    exact ⟨hg, hz _ hzχ⟩

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : GroupScheme.IsConnectedReductive G)

local instance actualTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- Evaluation through a complex-algebra equivalence with the actual scalar
algebra. This includes a transported coefficient algebra on a literal Levi. -/
def coefficientCharacter
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    B →ₐ[ℂ] ℂ :=
  ((Pi.evalAlgHom ℂ (fun _ : unramifiedCharacters
      (fun ψ => (rationalNormCharacters G ψ).toMul) => ℂ) χ).comp
        (unramifiedRegularFunctions
          (fun ψ => (rationalNormCharacters G ψ).toMul)).val).comp e.toAlgHom

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem coefficientCharacter_apply
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (b : B) :
    coefficientCharacter G e χ b = (e b).val χ := rfl

/-- Localized coefficient matrices give a polynomial principal neighborhood
in exactly the canonical coordinates of the actual unramified characters. -/
theorem exists_polynomial_principal_neighborhood
    {J : Type uJ} {n : Type un} [Fintype n] [DecidableEq n]
    (e : B ≃ₐ[ℂ]
      unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (A : J → Matrix n n S)
    (χ₀ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul))
    (hg₀ : coefficientCharacter G e χ₀ g ≠ 0)
    (h₀ : UnitarizabilityContinuation.IsIrreducibleFamily
      (specialize A (awayEvaluation g (coefficientCharacter G e χ₀) hg₀))) :
    ∃ p : MvPolynomial (Fin (rationalImageRank G)) ℂ,
      χ₀ ∈ rationalUnramifiedPrincipalOpen G hG p ∧
      ∀ χ ∈ rationalUnramifiedPrincipalOpen G hG p,
        ∃ hg : coefficientCharacter G e χ g ≠ 0,
          UnitarizabilityContinuation.IsIrreducibleFamily
            (specialize A (awayEvaluation g (coefficientCharacter G e χ) hg)) := by
  obtain ⟨f, hf₀, hf⟩ :=
    exists_regular_principal_neighborhood g A (coefficientCharacter G e χ₀) hg₀ h₀
  refine ⟨rationalRegularPolynomial G hG (e f), ?_, ?_⟩
  · rw [principalOpen_rationalRegularPolynomial]
    exact hf₀
  · intro χ hχ
    rw [principalOpen_rationalRegularPolynomial] at hχ
    exact hf (coefficientCharacter G e χ) hχ

end ActualCharacters

end Langlands.Renard.AlgebraicFamily.LocalizedMatrixPrincipalOpen

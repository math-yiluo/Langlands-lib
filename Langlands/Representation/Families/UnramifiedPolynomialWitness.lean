import Langlands.Representation.Plancherel.RationalUnramifiedDensity
import Langlands.Representation.Plancherel.RationalUnramifiedCharacterDensity
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Polynomial witnesses for nonvanishing of unramified regular functions

Negative exponents in a finite Laurent polynomial can be cleared by one
monomial, which is everywhere nonzero on the complex torus. This gives exactly
the same nonvanishing set in the published polynomial coordinates.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily.UnramifiedPolynomialWitness

open Plancherel

universe u

/-- Include ordinary polynomials in the finite Laurent algebra. -/
def polynomialToLaurent (n : ℕ) :
    MvPolynomial (Fin n) ℂ →ₐ[ℂ] AddMonoidAlgebra ℂ (Fin n → ℤ) :=
  AddMonoidAlgebra.mapDomainAlgHom ℂ ℂ
    (Finsupp.coeFnAddHom.comp
      (Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)))

@[simp]
theorem polynomialToLaurent_monomial {n : ℕ} (d : Fin n →₀ ℕ) (b : ℂ) :
    polynomialToLaurent n (MvPolynomial.monomial d b) =
      AddMonoidAlgebra.single (fun i => (d i : ℤ)) b := by
  rw [← MvPolynomial.single_eq_monomial]
  simp only [polynomialToLaurent, AddMonoidAlgebra.mapDomainAlgHom_apply,
    AddMonoidAlgebra.mapDomain_single]
  congr 1

/-- Polynomial evaluation is Laurent evaluation after the inclusion. -/
theorem polynomialToLaurent_eval {n : ℕ} (c : Fin n → ℂˣ)
    (p : MvPolynomial (Fin n) ℂ) :
    finiteLaurentEvaluation c (polynomialToLaurent n p) =
      MvPolynomial.eval (fun i => (c i : ℂ)) p := by
  classical
  induction p using MvPolynomial.induction_on' with
  | monomial d b =>
      rw [polynomialToLaurent_monomial, finiteLaurentEvaluation_single,
        MvPolynomial.eval_monomial,
        Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
      simp
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]

/-- One nonnegative monomial clears all negative exponents. The induction is
adapted from the local clearing argument in the published
`finiteLaurent_exists_zero_eval_ne_zero` proof by Worker 1664. -/
theorem exists_monomial_clearing {n : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    ∃ (N : Fin n →₀ ℕ) (p : MvPolynomial (Fin n) ℂ),
      AddMonoidAlgebra.single (fun i => (N i : ℤ)) 1 * f =
        polynomialToLaurent n p := by
  classical
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg =>
      obtain ⟨N₁, p₁, h₁⟩ := hf
      obtain ⟨N₂, p₂, h₂⟩ := hg
      refine ⟨N₁ + N₂,
        MvPolynomial.monomial N₂ 1 * p₁ + MvPolynomial.monomial N₁ 1 * p₂, ?_⟩
      rw [map_add, map_mul, map_mul, polynomialToLaurent_monomial,
        polynomialToLaurent_monomial, ← h₁, ← h₂]
      have hs : AddMonoidAlgebra.single (fun i => ((N₁ + N₂) i : ℤ)) (1 : ℂ) =
          AddMonoidAlgebra.single (fun i => (N₁ i : ℤ)) 1 *
            AddMonoidAlgebra.single (fun i => (N₂ i : ℤ)) 1 := by
        rw [AddMonoidAlgebra.single_mul_single, one_mul]
        congr 1
      rw [hs]
      ring
  | single m b =>
      refine ⟨Finsupp.equivFunOnFinite.symm (fun i => (-m i).toNat),
        MvPolynomial.monomial
          (Finsupp.equivFunOnFinite.symm (fun i => (m i).toNat)) b, ?_⟩
      rw [polynomialToLaurent_monomial, AddMonoidAlgebra.single_mul_single, one_mul]
      congr 1
      funext i
      simp only [Pi.add_apply, Finsupp.coe_equivFunOnFinite_symm]
      omega

/-- A chosen nonnegative exponent clearing a given finite Laurent polynomial. -/
def clearingExponent {n : ℕ} (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    Fin n →₀ ℕ :=
  (exists_monomial_clearing f).choose

/-- An ordinary polynomial obtained by clearing the negative exponents. -/
def polynomialNumerator {n : ℕ} (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    MvPolynomial (Fin n) ℂ :=
  (exists_monomial_clearing f).choose_spec.choose

/-- The chosen numerator satisfies the exact clearing identity. -/
theorem monomial_mul_eq_polynomialNumerator {n : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) :
    AddMonoidAlgebra.single (fun i => (clearingExponent f i : ℤ)) 1 * f =
      polynomialToLaurent n (polynomialNumerator f) :=
  (exists_monomial_clearing f).choose_spec.choose_spec

/-- The clearing monomial is nonzero at every torus point, so the numerator
has exactly the same nonvanishing locus, also in rank zero. -/
theorem polynomialNumerator_eval_ne_zero_iff {n : ℕ}
    (f : AddMonoidAlgebra ℂ (Fin n → ℤ)) (c : Fin n → ℂˣ) :
    MvPolynomial.eval (fun i => (c i : ℂ)) (polynomialNumerator f) ≠ 0 ↔
      finiteLaurentEvaluation c f ≠ 0 := by
  have he := congrArg (finiteLaurentEvaluation c)
    (monomial_mul_eq_polynomialNumerator f)
  rw [map_mul, polynomialToLaurent_eval] at he
  rw [← he, mul_ne_zero_iff]
  have hn : finiteLaurentEvaluation c
      (AddMonoidAlgebra.single (fun i => (clearingExponent f i : ℤ)) 1) ≠ 0 := by
    rw [finiteLaurentEvaluation_single, one_mul]
    exact Finset.prod_ne_zero_iff.mpr fun i _ => Units.ne_zero _
  exact and_iff_right hn

section ActualCharacters

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (hG : GroupScheme.IsConnectedReductive G)

local instance actualTopology : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- A polynomial with the same nonvanishing set as an actual regular function
on the full unramified character space, in its canonical coordinates. -/
def rationalRegularPolynomial
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    MvPolynomial (Fin (rationalImageRank G)) ℂ :=
  polynomialNumerator ((rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG).symm b)

/-- The Laurent-coordinate equivalence evaluates in the canonical coordinates. -/
theorem canonicalLaurent_eval
    (f : AddMonoidAlgebra ℂ (Fin (rationalImageRank G) → ℤ))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    (rationalCanonicalUnramifiedLaurentAlgebraEquiv G hG f).val χ =
      finiteLaurentEvaluation (rationalCanonicalUnramifiedCharacterCoordinates G hG χ) f :=
  rationalUnramifiedLaurentAlgebraEquiv_eval G
    (continuous_rationalValuationImageProjection G) hG f χ

/-- The constructed polynomial detects nonvanishing of the given actual
regular function at every actual unramified character. -/
theorem rationalRegularPolynomial_eval_ne_zero_iff
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul))
    (χ : unramifiedCharacters (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    MvPolynomial.eval
        (fun i => (rationalCanonicalUnramifiedCharacterCoordinates G hG χ i : ℂ))
        (rationalRegularPolynomial G hG b) ≠ 0 ↔ b.val χ ≠ 0 := by
  rw [rationalRegularPolynomial, polynomialNumerator_eval_ne_zero_iff]
  rw [← canonicalLaurent_eval G hG, AlgEquiv.apply_symm_apply]

/-- The nonzero locus of any actual regular scalar is exactly a polynomial
principal open set of the form used in Renard VI.8.4's published statement. -/
theorem principalOpen_rationalRegularPolynomial
    (b : unramifiedRegularFunctions (fun ψ => (rationalNormCharacters G ψ).toMul)) :
    rationalUnramifiedPrincipalOpen G hG (rationalRegularPolynomial G hG b) =
      {χ | b.val χ ≠ 0} := by
  ext χ
  rw [mem_rationalUnramifiedPrincipalOpen]
  exact rationalRegularPolynomial_eval_ne_zero_iff G hG b χ

end ActualCharacters

end Langlands.Renard.AlgebraicFamily.UnramifiedPolynomialWitness

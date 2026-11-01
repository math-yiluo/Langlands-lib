import Langlands.AlgebraicGeometry.Modules.CoherentEulerPolynomial
import Langlands.Algebra.RationalPolynomialNewtonAdditivity
import Langlands.Algebra.RationalPolynomialDilationProof

/-! # Additivity and truncation independence of coherent Euler polynomials -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

open Langlands.Scheme.Modules
open Langlands.Algebra.RationalPolynomial

variable {X : Scheme.{u}} {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Coherent Euler polynomial truncations are invariant under actual sheaf isomorphisms. -/
theorem coherentEulerPolynomial_iso {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L : Picard.LineBundle X) (d : ℕ) (i : M ≅ N) :
    coherentEulerPolynomial f M hM L d = coherentEulerPolynomial f N hN L d := by
  unfold coherentEulerPolynomial
  rw [coherentEulerSequence_iso f hM hN L i]

/-- Each truncation is additive on actual short exact sequences of coherent sheaves. -/
theorem coherentEulerPolynomial_add (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : HasFiniteAffineSections S.X₁) (h₂ : HasFiniteAffineSections S.X₂)
    (h₃ : HasFiniteAffineSections S.X₃) (L : Picard.LineBundle X) (d : ℕ) :
    coherentEulerPolynomial f S.X₂ h₂ L d =
      coherentEulerPolynomial f S.X₁ h₁ L d + coherentEulerPolynomial f S.X₃ h₃ L d := by
  unfold coherentEulerPolynomial
  rw [coherentEulerSequence_add f S hS h₁ h₂ h₃ L, newtonPolynomial_add]

/-- A zero coherent sheaf has zero Euler polynomial at every truncation. -/
theorem coherentEulerPolynomial_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d : ℕ)
    (hz : IsZero M) :
    coherentEulerPolynomial f M hM L d = 0 := by
  unfold coherentEulerPolynomial
  rw [coherentEulerSequence_zero f M hM L hz, newtonPolynomial_zero]

/-- Two truncations reconstructing the same coherent Euler sequence are equal. -/
theorem coherentEulerPolynomial_eq_of_supportDimensionLT
    [IsNoetherian X] [X.IsSeparated] (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (d e : ℕ)
    (hd : HasSupportDimensionLT M (d + 1))
    (he : HasSupportDimensionLT M (e + 1)) :
    coherentEulerPolynomial f M hM L d = coherentEulerPolynomial f M hM L e := by
  apply eq_of_eventually_nat_eval_eq
  apply Filter.Eventually.of_forall
  intro n
  rw [coherentEulerPolynomial_eval f M hM L d hd,
    coherentEulerPolynomial_eval f M hM L e he]

end Langlands.AlgebraicGeometry.Modules.DerivedSections

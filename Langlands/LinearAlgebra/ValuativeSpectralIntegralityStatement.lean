import Mathlib.RingTheory.Valuation.ValuativeRel.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.Polynomial.Splits

/-! # Valuative coefficient and root integrality targets -/

universe u v

namespace Langlands

/-- Integral coefficients of a monic polynomial are equivalent to integral roots
in any compatible valued extension in which the polynomial splits. -/
def ValuativePolynomialRootsStatement : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E]
    [ValuativeRel F] [ValuativeRel E] [Algebra F E] [ValuativeExtension F E]
    (p : Polynomial F), p.Monic → (p.map (algebraMap F E)).Splits →
      ((∀ i : ℕ, p.coeff i ≤ᵥ (1 : F)) ↔
        ∀ x : E, (p.map (algebraMap F E)).IsRoot x → x ≤ᵥ (1 : E))

/-- The coefficient/root comparison for the actual characteristic polynomial of
a finite matrix after scalar extension, including matrices of dimension zero. -/
def ValuativeMatrixRootsStatement : Prop :=
  ∀ (F : Type u) (E : Type v) [Field F] [Field E]
    [ValuativeRel F] [ValuativeRel E] [Algebra F E] [ValuativeExtension F E]
    (N : ℕ) (A : Matrix (Fin N) (Fin N) F),
      (A.map (algebraMap F E)).charpoly.Splits →
      ((∀ i : ℕ, A.charpoly.coeff i ≤ᵥ (1 : F)) ↔
        ∀ x : E, (A.map (algebraMap F E)).charpoly.IsRoot x → x ≤ᵥ (1 : E))

/-- Both scalar-polynomial and matrix forms of the valuative spectral bridge. -/
def ValuativeSpectralIntegralityStatement : Prop :=
  ValuativePolynomialRootsStatement.{u, v} ∧ ValuativeMatrixRootsStatement.{u, v}

end Langlands

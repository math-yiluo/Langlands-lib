import Langlands.BaseChange.Norm
import Langlands.TraceFormula.TwistedOrbital
import Langlands.Group.GL.IntegralSubgroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.LocalRing.ResidueField.Defs

/-!
# Twisted conjugates into `GL_n(O)` at an unramified field place

This module states the local coset property for a cyclic field extension,
with the cyclic norm as in Henniart–Lemaire. It adapts the support argument
in Getz–Hahn, Lemma 17.8.3, to the twisted conjugation used in (18.32).
See the paired Markdown for the source comparison.
-/

namespace Langlands.TraceFormula

open Langlands.BaseChange

universe u v

/-- Let `σ` generate the Galois group of a cyclic field extension `E/F` of degree `l`
(`IsCyclicAlgebra σ l`), and let `O` be a valuation subring of `E` that is a discrete valuation
ring, is stable under `σ`, has finite residue field, and has an irreducible element lying in
the image of `F`. Let `δ ∈ GL_n(E)` have entries and inverse entries in `O`, and let the
characteristic polynomial of its norm `cyclicNorm σ l δ` have discriminant of valuation `1`.
Then every `x ∈ GL_n(E)` with `x⁻¹ * δ * x^σ ∈ GL_n(O)` is `c * k` with `c` in the
`σ`-centralizer of `δ` and `k ∈ GL_n(O)`. -/
def InertTwistedCosetStatement : Prop :=
  ∀ {F : Type u} [Field F] {E : Type v} [Field E] [Algebra F E]
    (σ : E ≃ₐ[F] E) (l : ℕ), IsCyclicAlgebra σ l →
    ∀ (O : ValuationSubring E) [IsDiscreteValuationRing O],
      (∀ x ∈ O, σ x ∈ O) →
      Finite (IsLocalRing.ResidueField O) →
      (∃ ϖ : O, Irreducible ϖ ∧ (ϖ : E) ∈ (algebraMap F E).range) →
      ∀ (n : ℕ) (δ : GeneralLinear n E),
        δ ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring →
        O.valuation
            (Matrix.charpoly (cyclicNorm σ l δ : Matrix (Fin n) (Fin n) E)).discr = 1 →
        ∀ x : GeneralLinear n E,
          x⁻¹ * δ * entrywiseAut σ n x ∈
              Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring →
            ∃ c ∈ twistedCentralizer (entrywiseAut σ n) δ,
              ∃ k ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring,
                x = c * k

end Langlands.TraceFormula

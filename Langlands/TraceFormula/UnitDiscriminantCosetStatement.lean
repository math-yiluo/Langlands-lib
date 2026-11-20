import Langlands.Group.GL.IntegralSubgroup
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

/-!
# Conjugates of a unit-discriminant matrix into `GL_n(O)`

Let `O` be a discrete valuation ring with fraction field `F`, given as a valuation subring
of `F`, and let `γ ∈ GL_n(O)` have a characteristic polynomial whose discriminant is a unit
of `O`. Then every `x ∈ GL_n(F)` with `x⁻¹ γ x ∈ GL_n(O)` lies in `Z(γ) · GL_n(O)`, where
`Z(γ)` is the centralizer of `γ` in `GL_n(F)`.

This derived statement isolates an explicit local condition for the ordinary coset property
used in a twisted orbital integral calculation as in Getz–Hahn 2024, (18.32) (printed p. 487).
Lemma 17.8.3 and its proof (printed p. 464) obtain a coset description at almost all places
using properness and Exercise 17.15 (printed p. 470). The unit-discriminant hypothesis
specifies the input for a local lattice argument for `GL_n`.
-/

namespace Langlands.TraceFormula

universe u

/-- Let `O` be a valuation subring of the field `F` that is a discrete valuation ring, and let
`γ ∈ GL_n(F)` have entries and inverse entries in `O` and a characteristic polynomial whose
discriminant has valuation `1`. Then every `x ∈ GL_n(F)` with `x⁻¹ * γ * x ∈ GL_n(O)` is
`c * k` with `c` in the centralizer of `γ` and `k ∈ GL_n(O)`. -/
def UnitDiscriminantCentralizerCosetStatement : Prop :=
  ∀ {F : Type u} [Field F] (O : ValuationSubring F) [IsDiscreteValuationRing O] (n : ℕ)
    (γ : GL (Fin n) F),
    γ ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring →
    O.valuation (Matrix.charpoly (γ : Matrix (Fin n) (Fin n) F)).discr = 1 →
    ∀ x : GL (Fin n) F,
      x⁻¹ * γ * x ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring →
      ∃ c ∈ Subgroup.centralizer {γ},
        ∃ k ∈ Langlands.GeneralLinearGroup.integralSubgroup (Fin n) O.toSubring, x = c * k

end Langlands.TraceFormula

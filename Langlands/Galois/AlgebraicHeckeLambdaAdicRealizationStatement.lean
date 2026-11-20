import Langlands.Galois.HeckeCharacterRealization
import Langlands.Global.Arithmetic.HarrisSetup

/-! # Compatible rank-one realizations of algebraic Hecke characters -/

noncomputable section

universe uK uL

set_option autoImplicit false

namespace Langlands.GaloisRepresentation

open Langlands.Global
open scoped Valued

/-- A rank-one compatible realization with a common exceptional set and common
Frobenius values in the coefficient number field. At each good place the
comparison uses a uniformizer and geometric Frobenius as in
`IsLambdaAdicRealization`. -/
def IsCompatibleLambdaAdicRealization {K : Type uK} [Field K] [NumberField K]
    {L : Type uL} [Field L] [NumberField L] (ι : L →+* ℂ) (χ : HeckeCharacter K)
    (ψ : (lam : FinitePlace L) → LambdaAdicCharacter K L lam) : Prop :=
  ∃ S : Finset (FinitePlace K), ∀ v : FinitePlace K, v ∉ S →
    χ.IsUnramifiedAt v ∧
      ∃ a : L,
        (∃ ϖ : (FiniteCompletion K v)ˣ,
          Valued.v (ϖ : FiniteCompletion K v) = WithZero.exp (-1 : ℤ) ∧
            (χ.finiteComponent v ϖ : ℂ) = ι a) ∧
        ∀ lam : FinitePlace L, residueCharacteristic v ≠ residueCharacteristic lam →
          (ψ lam).IsUnramifiedAt v ∧
          ∀ g : LocalGroup v, IsGeometricFrobeniusLift v g →
            ((ψ lam).atFinitePlace v g : FiniteCompletion L lam) =
              NumberField.FinitePlace.embedding lam a

/-- The rank-one algebraic Hecke-character construction on a totally complex
number field, with realizations at all finite places of one coefficient number
field. -/
def AlgebraicHeckeLambdaAdicRealizationStatement : Prop :=
  ∀ (K : Type uK) [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
    (χ : HeckeCharacter K), Harris.IsAlgebraic χ →
    ∃ (L : Type uL) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (numberFieldL : NumberField L),
        letI : NumberField L := numberFieldL
        ∃ (ι : L →+* ℂ) (ψ : (lam : FinitePlace L) → LambdaAdicCharacter K L lam),
          IsCompatibleLambdaAdicRealization ι χ ψ

end Langlands.GaloisRepresentation

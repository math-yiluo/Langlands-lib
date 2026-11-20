import Langlands.Automorphic.ConjugateContragredient
import Langlands.Automorphic.CuspidalSpectralPresentation
import Langlands.Automorphic.RegularAlgebraic
import Langlands.Cohomology.Weights.Polynomial
import Langlands.Galois.HeckeCharacterRealization
import Langlands.Global.Arithmetic.HarrisSetup

/-! # Rank-one inputs for the cuspidal case of Harris's Theorem 1.2 -/

noncomputable section

universe uE uL uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Global Langlands.Unramified
open NumberField (IsCMField)
open scoped Valued

/-- The determinant identification at rank one, including the algebraic
infinity type and the spherical spectrum of the given cuspidal class. -/
def HarrisRankOneHeckeSpectrumStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (c : CuspidalOperatorRealization.IsoClass E 0),
    c.IsRegularAlgebraic → c.IsConjugateSelfDual →
    ∃ (χ : HeckeCharacter E) (s : SpectralSystem (FinitePlace E) 1)
      (S : Finset (FinitePlace E)) (hS : s.exceptional ⊆ S),
      Harris.IsAlgebraic χ ∧ χ.IsUnitary ∧
      CuspidalOperatorRealization.IsoClass.HasSpectralSystem.{uE, uW} c s ∧
      ∀ v (hv : v ∉ S), χ.IsUnramifiedAt v ∧
        ∀ ϖ : (FiniteCompletion E v)ˣ,
          Valued.v (ϖ : FiniteCompletion E v) = WithZero.exp (-1 : ℤ) →
          s.eulerPolynomial v (fun hs => hv (hS hs)) =
            1 - Polynomial.C (χ.finiteComponent v ϖ : ℂ) * Polynomial.X

/-- Uniform realization of an algebraic unitary Hecke character of a CM
field by actual completion-valued Galois characters. A uniformizer matches
geometric Frobenius, in the convention of `IsLambdaAdicRealization`. -/
def AlgebraicUnitaryHeckeCharacterRealizationStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] (χ : HeckeCharacter E),
    Harris.IsAlgebraic χ → χ.IsUnitary →
    ∃ (L : Type uL) (fieldL : Field L),
      letI : Field L := fieldL
      ∃ (numberFieldL : NumberField L),
        letI : NumberField L := numberFieldL
        ∃ (ι : L →+* ℂ) (S : Finset (FinitePlace E))
          (a : FinitePlace E → Lˣ) (ψ : ∀ lam : FinitePlace L, LambdaAdicCharacter E L lam),
          ∀ v ∉ S,
            χ.IsUnramifiedAt v ∧
            (∃ ϖ : (FiniteCompletion E v)ˣ,
              Valued.v (ϖ : FiniteCompletion E v) = WithZero.exp (-1 : ℤ) ∧
                (χ.finiteComponent v ϖ : ℂ) = ι (a v : L)) ∧
            Cohomology.Weights.IsPurePolynomial
              (residueCardinality v) 0 ((Polynomial.X : Polynomial L) -
                Polynomial.C (a v : L)) ∧
            ∀ lam : FinitePlace L, residueCharacteristic v ≠ residueCharacteristic lam →
              (ψ lam).IsUnramifiedAt v ∧
                ∃ g : LocalGroup v, IsGeometricFrobeniusLift v g ∧
                  ((ψ lam).atFinitePlace v g : FiniteCompletion L lam) =
                    NumberField.FinitePlace.embedding lam (a v : L)

end Langlands.GaloisRepresentation

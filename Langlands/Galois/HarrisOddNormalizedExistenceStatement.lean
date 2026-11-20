import Langlands.Galois.AbsoluteGeometricFrobeniusDensityStatement
import Langlands.Galois.FiniteCoefficientModelStatement
import Langlands.Galois.HarrisEvenGeometricStatement
import Langlands.Galois.HarrisParityBaseChangeStatement
import Langlands.Galois.QuadraticFrobeniusPatchingStatement
import Langlands.Global.Arithmetic.HarrisAuxiliaryConjugatePairStatement
import Langlands.Global.Arithmetic.HarrisParityAuxiliaryFieldsStatement

/-! # The odd-real-degree branch of the cuspidal Harris reduction -/

noncomputable section

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Automorphic.Unramified Langlands.Global
open NumberField (IsCMField IsTotallyComplex IsTotallyReal)

/-- The odd-real-degree output has the same normalized polynomial and
labelled Hodge–Tate conditions as the even-degree output. -/
def HarrisOddNormalizedExistenceStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    (¬ Even (Module.finrank ℚ E₀)) →
    ∀ (r : ℕ), 1 ≤ r → ∀ (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
      c.IsRegularAlgebraic → c.IsConjugateSelfDual →
      CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uE, uW} c v →
      Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀ →
      ∀ e : E →+* ℂ,
        ∃ (L : Type uL) (fieldL : Field L),
          letI : Field L := fieldL
          ∃ (numberFieldL : NumberField L),
            letI : NumberField L := numberFieldL
            ∃ (ι : L →+* ℂ) (j : E →+* L) (R : Collection.{uE, uL, uV} E L ∅),
              ι.comp j = e ∧ HarrisNormalizedSystem.{uE, uL, uV, uW} c ι ∅ R ∧
                (∀ lam, Representation.IsSemisimpleRepresentation (R lam).val.representation) ∧
                HarrisLabelledWeights R j (r + 1) 1

/-- The even-degree result and the named automorphic, arithmetic, patching,
and coefficient inputs imply the odd-degree result. -/
def HarrisOddNormalizedExistenceReductionStatement : Prop :=
  HarrisEvenNormalizedExistenceStatement.{uE, uL, uV, uW} →
  Harris.HarrisParityAuxiliaryFieldsStatement.{uE} →
  Harris.ConjugateSelfDualUnitaryCentralCharacterStatement.{uE} →
  CyclicPrimeIsobaricBaseChangeTCStatement.{uE, uE, uW, uW} →
  QuadraticWeakBaseChangeSplitSquareIntegrableStatement.{uE, uE, uW, uW} →
  CyclicWeakBaseChangeComplexPlaceTCStatement.{uE, uE, uW, uW} →
  CuspidalComplexParameterBridgeTCStatement.{uE} →
  HarrisParityBaseChangeStatement.{uE, uW} →
  QuadraticPatchingStatement.{uE, uL, uV} →
  QuadraticFrobeniusPatchingStatement.{uE, uL, uV} →
  AbsoluteGeometricFrobeniusDensityStatement.{uE} →
  FiniteCoefficientModelStatement.{uE, uL, uV} →
  RegularHodgeTateCoefficientDescentStatement.{uE, uL, uV} →
  HarrisOddNormalizedExistenceStatement.{uE, uL, uV, uW}

end Langlands.GaloisRepresentation

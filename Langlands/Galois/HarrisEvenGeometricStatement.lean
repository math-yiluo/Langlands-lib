import Langlands.Galois.Harris1998ExistenceStatement
import Langlands.Galois.HarrisLabelledMultiplicityStatement
import Langlands.Galois.HarrisNormalizedSystem

/-! # The even-real-degree branch of the cuspidal Harris reduction -/

noncomputable section

universe uE uL uV uW

namespace Langlands.GaloisRepresentation

open Langlands.Automorphic Langlands.Global
open NumberField (IsCMField IsTotallyComplex IsTotallyReal)

/-- Regular labelled Hodge–Tate weights of the indicated common
multiplicity at every coefficient place of a collection. -/
def HarrisLabelledWeights {E : Type uE} [Field E] {L : Type uL} [Field L] [NumberField L]
    {excluded : Finset (FinitePlace L)} (R : Collection.{uE, uL, uV} E L excluded)
    (j : E →+* L) (n m : ℕ) : Prop :=
  ∀ lam : {lam : FinitePlace L // lam ∉ excluded},
    ∃ k : Fin n → ℤ, Function.Injective k ∧
      HasLabelledHodgeTateAt lam.1 (R lam)
        ((NumberField.FinitePlace.embedding lam.1).comp j) n m k

/-- The output of the even-degree Clozel transfer and Kottwitz comparison,
with the labelled Hodge–Tate comparison for the same genuine cohomological
multiplicity representations. This is the input before Taylor's extraction. -/
def HarrisEvenGeometricPowerStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    Even (Module.finrank ℚ E₀) →
    ∀ (r : ℕ), 1 ≤ r → ∀ (c : CuspidalOperatorRealization.IsoClass E r) (v : FinitePlace E),
      c.IsRegularAlgebraic → c.IsConjugateSelfDual →
      CuspidalOperatorRealization.IsoClass.HasSquareIntegrableComponent.{uE, uW} c v →
      Harris.IsSplitImaginaryQuadratic (residueCharacteristic v) K₀ →
      ∀ e : E →+* ℂ,
        ∃ (L : Type uL) (fieldL : Field L),
          letI : Field L := fieldL
          ∃ (numberFieldL : NumberField L),
            letI : NumberField L := numberFieldL
            ∃ (ι : L →+* ℂ) (j : E →+* L) (a : ℕ)
              (R : Collection.{uE, uL, uV} E L ∅),
              ι.comp j = e ∧ HarrisPowerSystem.{uE, uL, uV, uW} c ι ∅ R a ∧
                HarrisLabelledWeights R j (r + 1) a

/-- The even-degree output used by quadratic patching, with multiplicity one
and coefficient models at all completions of one field. -/
def HarrisEvenNormalizedExistenceStatement : Prop :=
  ∀ (E : Type uE) [Field E] [NumberField E] [IsCMField E] [CompactSpace (AdeleQuotient E)]
    (E₀ K₀ : IntermediateField ℚ E),
    IsTotallyReal E₀ → Module.finrank ℚ K₀ = 2 → IsTotallyComplex K₀ → E₀ ⊔ K₀ = ⊤ →
    Even (Module.finrank ℚ E₀) →
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

/-- Assemble the even-degree normalized family from the geometric
multiplicity family and the two local steps. -/
def HarrisEvenMultiplicityReductionStatement : Prop :=
  HarrisEvenGeometricPowerStatement.{uE, uL, uV, uW} →
  TaylorLabelledMultiplicityRemovalStatement.{uE, uL, uV} →
  RegularHodgeTateCoefficientDescentStatement.{uE, uL, uV} →
  HarrisEvenNormalizedExistenceStatement.{uE, uL, uV, uW}

end Langlands.GaloisRepresentation

import Langlands.Automorphic.OperatorDeterminantTwistClasses
import Langlands.Automorphic.Unramified.IsobaricCyclicTransferStatement

/-! # Pair multiplicities under cyclic weak base change -/

noncomputable section

open scoped BigOperators

universe uF uE uV uW

set_option autoImplicit false

namespace Langlands.Automorphic.IsobaricData

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Count pairs of equal cuspidal constituents, with the multiplicity of each
constituent in each datum. -/
def equalConstituentPairCount (D D' : IsobaricData F) : ℕ := by
  classical
  exact (D.map fun c => D'.count c).sum

end Langlands.Automorphic.IsobaricData

namespace Langlands.Automorphic.Unramified

open Langlands.Global

section

variable (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
  [Algebra F E]
  [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)]

/-- Over a fixed cyclic extension, compare the number of equal constituent pairs
in two supplied unitary weak base changes with the sum of the numbers of equal
pairs after twisting the first base datum by every norm character. -/
def CyclicWeakBaseChangePairMultiplicityOver
    [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)] : Prop :=
  ∀ (η : HeckeCharacter F) (hη : η.HasNormKernel E)
    (DF DF' : IsobaricData F) (DE DE' : IsobaricData E),
    DF.IsUnitary → DF'.IsUnitary → DE.IsUnitary → DE'.IsUnitary →
    IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE DF →
    IsobaricData.IsWeakBaseChangeOf.{uF, uE, uV, uW} DE' DF' →
    let finiteOrder (i : ℕ) : (η ^ i).HasFiniteOrder :=
      HeckeCharacter.IsTrivialOnNorm.hasFiniteOrder E (by
        intro x
        rw [ContinuousMonoidHom.pow_apply, hη.isTrivialOnNorm x, one_pow])
    (∑ i ∈ Finset.range (Module.finrank F E),
      IsobaricData.equalConstituentPairCount
        (DF.map fun c => PositiveRankCuspidalClass.determinantTwist c
          (η ^ i) (finiteOrder i)) DF') =
      IsobaricData.equalConstituentPairCount DE DE'

end

/-- The constituent-pair comparison for cyclic extensions of arbitrary number fields. -/
def CyclicWeakBaseChangePairMultiplicityStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    CyclicWeakBaseChangePairMultiplicityOver.{uF, uE, uV, uW} F E

/-- The constituent-pair comparison over a totally complex base field. -/
def CyclicWeakBaseChangePairMultiplicityTCStatement : Prop :=
  ∀ (F : Type uF) (E : Type uE) [Field F] [NumberField F] [NumberField.IsTotallyComplex F]
    [Field E] [NumberField E] [Algebra F E] [IsGalois F E] [IsCyclic (E ≃ₐ[F] E)]
    [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)],
    CyclicWeakBaseChangePairMultiplicityOver.{uF, uE, uV, uW} F E

end Langlands.Automorphic.Unramified

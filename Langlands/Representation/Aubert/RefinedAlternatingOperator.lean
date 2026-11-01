import Langlands.Representation.Aubert.RefinedAlternatingConstruction
import Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorProof

/-! Exact refined K0 maps and the alternating operator on an actual product Levi. -/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

open SmoothRep

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Actual normalized refined induction on the exact finite-length K0. -/
def normalizedRefinedInductionK0
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (Geometric.refinedLevi F.Carrier B S) →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  normalizedRefinedInductionK0Of.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B S

/-- Actual normalized refined Jacquet restriction on the exact finite-length K0. -/
def normalizedRefinedJacquetK0
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (Geometric.refinedLevi F.Carrier B S) :=
  normalizedRefinedJacquetK0Of.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B S

/-- Induction computes as the class of the actual induced object. -/
theorem normalizedRefinedInductionK0_finiteLengthClass
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S))
      (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedRefinedInductionK0.{uF, uV} F T B S
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        B.finiteLengthClass F.Carrier
          ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj A) hOut :=
  normalizedRefinedInductionK0Of_finiteLengthClass.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B S

/-- Jacquet restriction computes as the class of the actual Jacquet object. -/
theorem normalizedRefinedJacquetK0_finiteLengthClass
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedRefinedJacquetK0.{uF, uV} F T B S
          (B.finiteLengthClass F.Carrier A hA) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A) hOut :=
  normalizedRefinedJacquetK0Of_finiteLengthClass.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B S

end Langlands.Parabolic

namespace Langlands.Aubert

universe uF uV

open Parabolic SmoothRep

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The unadjusted alternating induction-after-Jacquet sum over all actual
refinements of a product Levi, using proved finite length and exactness. -/
def alternatingOperatorOnLevi
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  alternatingOperatorOnLeviOf.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B

/-- The defining sum may use any enumeration of the actual refinements. -/
theorem alternatingOperatorOnLevi_eq_sum
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    alternatingOperatorOnLevi.{uF, uV} F T B =
      ∑ S : Geometric.BlockRefinement B,
        ((-1 : ℤ) ^ refinementSignExponent B S) •
          (normalizedRefinedInductionK0.{uF, uV} F T B S).comp
            (normalizedRefinedJacquetK0.{uF, uV} F T B S) :=
  alternatingOperatorOnLeviOf_eq_sum.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B

/-- Evaluation on every virtual finite-length class. -/
theorem alternatingOperatorOnLevi_apply
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    ∀ x : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier,
      alternatingOperatorOnLevi.{uF, uV} F T B x =
        ∑ S : Geometric.BlockRefinement B,
          ((-1 : ℤ) ^ refinementSignExponent B S) •
            normalizedRefinedInductionK0.{uF, uV} F T B S
              (normalizedRefinedJacquetK0.{uF, uV} F T B S x) :=
  alternatingOperatorOnLeviOf_apply.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B

/-- The actual induction of an actual refined Jacquet object has finite length. -/
theorem refinedInductionJacquet_hasFiniteLength
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      A.HasFiniteLength → ∀ S : Geometric.BlockRefinement B,
        ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj
          ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A)).HasFiniteLength :=
  refinedInductionJacquet_hasFiniteLength_of.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B

/-- Evaluation on an actual finite-length object, using the proved output lengths. -/
theorem alternatingOperatorOnLevi_finiteLengthClass
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength),
      alternatingOperatorOnLevi.{uF, uV} F T B (B.finiteLengthClass F.Carrier A hA) =
        ∑ S : Geometric.BlockRefinement B,
          ((-1 : ℤ) ^ refinementSignExponent B S) •
            B.finiteLengthClass F.Carrier
              ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj
                ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A))
              (refinedInductionJacquet_hasFiniteLength.{uF, uV} F T B A hA S) := by
  let := T.topology
  intro A hA
  exact alternatingOperatorOnLeviOf_finiteLengthClass.{uF, uV} F T
    (normalizedRefinedFiniteLengthExactness.{uF, max uF uV} F T) B A hA
    (refinedInductionJacquet_hasFiniteLength.{uF, uV} F T B A hA)

end Langlands.Aubert

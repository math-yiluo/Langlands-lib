import Langlands.Representation.Parabolic.RefinedFiniteLengthFunctorStatement
import Langlands.Representation.CuspidalSupport.FiniteBlockShapes

/-!
# Conditional exact K0 maps and alternating sums inside a product Levi

The published preservation proposition is an explicit argument of every map
constructed here. This module does not prove that proposition.
-/

noncomputable section

namespace Langlands.Parabolic

universe uF uV

open SmoothRep

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The exact K0 map of actual refined induction, supplied with the published
four-clause preservation proposition at the saturated carrier universe. -/
def normalizedRefinedInductionK0Of
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (Geometric.refinedLevi F.Carrier B S) →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  letI := T.topology
  FiniteLengthGrothendieckGroup.map
    (T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S)
    (h.1 n B S) (h.2.2.1 n B S)

/-- The exact K0 map of the actual refined Jacquet functor, supplied with the
published four-clause preservation proposition at the saturated universe. -/
def normalizedRefinedJacquetK0Of
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, uF, max uF uV} ℂ
        (Geometric.refinedLevi F.Carrier B S) :=
  letI := T.topology
  FiniteLengthGrothendieckGroup.map
    (T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S)
    (h.2.1 n B S) (h.2.2.2 n B S)

/-- Computation on each actual finite-length refined-Levi object, for any
choice of the output finite-length proof. -/
theorem normalizedRefinedInductionK0Of_finiteLengthClass
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (Geometric.refinedLevi F.Carrier B S))
      (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedRefinedInductionK0Of.{uF, uV} F T h B S
          (FiniteLengthGrothendieckGroup.ofRepresentation A hA) =
        B.finiteLengthClass F.Carrier
          ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro A hA _
  exact FiniteLengthGrothendieckGroup.map_ofRepresentation _ _ _ A hA

/-- Computation on each actual finite-length product-Levi object, for any
choice of the output finite-length proof. -/
theorem normalizedRefinedJacquetK0Of_finiteLengthClass
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) (S : Geometric.BlockRefinement B) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A).HasFiniteLength),
      normalizedRefinedJacquetK0Of.{uF, uV} F T h B S
          (B.finiteLengthClass F.Carrier A hA) =
        FiniteLengthGrothendieckGroup.ofRepresentation
          ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A) hOut := by
  let := T.topology
  intro A hA _
  exact FiniteLengthGrothendieckGroup.map_ofRepresentation _ _ _ A hA

end Langlands.Parabolic

namespace Langlands.Aubert

universe uF uV

open Parabolic SmoothRep

/-- The sum of the numbers of simple roots retained inside each outer block. -/
def refinementSignExponent {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : Geometric.BlockRefinement B) : ℕ :=
  ∑ i, (B.size i - (S i).length)

/-- The exponent is the total rank minus the number of refined blocks. -/
theorem refinementSignExponent_eq {n : ℕ} (B : GeneralLinear.BlockShape n)
    (S : Geometric.BlockRefinement B) :
    refinementSignExponent B S = n - ∑ i, (S i).length := by
  unfold refinementSignExponent
  rw [Finset.sum_tsub_distrib _ (fun i _ => (S i).length_le), B.sum_eq]

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- The alternating refinement sum on the exact K0 of an actual product Levi.
The preservation proposition is an explicit input; no proof of it is supplied. -/
def alternatingOperatorOnLeviOf
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier →ₗ[ℤ]
      B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier :=
  letI := T.topology
  letI : Fintype (Geometric.BlockRefinement B) := Fintype.ofFinite _
  ∑ S : Geometric.BlockRefinement B,
    ((-1 : ℤ) ^ refinementSignExponent B S) •
      (normalizedRefinedInductionK0Of.{uF, uV} F T h B S).comp
        (normalizedRefinedJacquetK0Of.{uF, uV} F T h B S)

/-- The sum is independent of the enumeration of actual block refinements. -/
theorem alternatingOperatorOnLeviOf_eq_sum
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    alternatingOperatorOnLeviOf.{uF, uV} F T h B =
      ∑ S : Geometric.BlockRefinement B,
        ((-1 : ℤ) ^ refinementSignExponent B S) •
          (normalizedRefinedInductionK0Of.{uF, uV} F T h B S).comp
            (normalizedRefinedJacquetK0Of.{uF, uV} F T h B S) := by
  let := T.topology
  unfold alternatingOperatorOnLeviOf
  congr
  exact Subsingleton.elim _ _

/-- Evaluation of the defining sum on an arbitrary virtual class. -/
theorem alternatingOperatorOnLeviOf_apply
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    ∀ x : B.FiniteLengthGrothendieckGroup.{uV, uF} F.Carrier,
      alternatingOperatorOnLeviOf.{uF, uV} F T h B x =
        ∑ S : Geometric.BlockRefinement B,
          ((-1 : ℤ) ^ refinementSignExponent B S) •
            normalizedRefinedInductionK0Of.{uF, uV} F T h B S
              (normalizedRefinedJacquetK0Of.{uF, uV} F T h B S x) := by
  let := T.topology
  intro x
  rw [alternatingOperatorOnLeviOf_eq_sum, LinearMap.sum_apply]
  rfl

/-- Actual induction after an actual refined Jacquet module has finite length,
conditionally on the two preservation clauses supplied in `h`. -/
theorem refinedInductionJacquet_hasFiniteLength_of
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)),
      A.HasFiniteLength → ∀ S : Geometric.BlockRefinement B,
        ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj
          ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A)).HasFiniteLength := by
  let := T.topology
  intro A hA S
  exact h.1 n B S _ (h.2.1 n B S A hA)

/-- Generator evaluation, with any supplied finite-length proofs on the outputs. -/
theorem alternatingOperatorOnLeviOf_finiteLengthClass
    (h : NormalizedRefinedFiniteLengthExactnessStatement.{uF, max uF uV} F T)
    {n : ℕ} (B : GeneralLinear.BlockShape n) [Fintype (Geometric.BlockRefinement B)] :
    letI := T.topology
    ∀ (A : SmoothRep.{0, uF, max uF uV} ℂ (B.Levi F.Carrier)) (hA : A.HasFiniteLength)
      (hOut : ∀ S : Geometric.BlockRefinement B,
        ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj
          ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A)).HasFiniteLength),
      alternatingOperatorOnLeviOf.{uF, uV} F T h B (B.finiteLengthClass F.Carrier A hA) =
        ∑ S : Geometric.BlockRefinement B,
          ((-1 : ℤ) ^ refinementSignExponent B S) •
            B.finiteLengthClass F.Carrier
              ((T.normalizedRefinedInductionFunctor.{uF, max uF uV} B S).obj
                ((T.normalizedRefinedJacquetFunctor.{uF, max uF uV} B S).obj A)) (hOut S) := by
  let := T.topology
  intro A hA hOut
  rw [alternatingOperatorOnLeviOf_apply]
  refine Finset.sum_congr rfl fun S _ => ?_
  have hJ := h.2.1 n B S A hA
  rw [normalizedRefinedJacquetK0Of_finiteLengthClass F T h B S A hA hJ,
    normalizedRefinedInductionK0Of_finiteLengthClass F T h B S _ hJ (hOut S)]

end Langlands.Aubert

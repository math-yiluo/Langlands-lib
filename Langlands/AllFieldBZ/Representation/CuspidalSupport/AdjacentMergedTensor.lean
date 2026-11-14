import Langlands.AllFieldBZ.Group.GL.AdjacentMergeShape
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AssociationReduction
import Langlands.AllFieldBZ.Representation.CuspidalSupport.CuspidalTensorProof
import Langlands.AllFieldBZ.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Representation.CuspidalSupport.AdjacentMergedTensor

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AdjacentMergedTensor`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AdjacentMergedTensor` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.GeneralLinear.BlockShape
open Langlands.GeneralLinear.BlockShape
open Langlands.Geometric hiding GeometricLemmaTheorem PadicGeometricLemmaTheorem PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem geometricPieceFunctor jacquetInductionFunctor
open Langlands.AllFieldBZ.Geometric
variable {n : ℕ} (B : Langlands.GeneralLinear.BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

end Langlands.AllFieldBZ.GeneralLinear.BlockShape
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem PadicAssociatedGeometricPiecesTheorem TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem adjacentInnerTensor adjacentInnerTensorTransportEquiv adjacentInnerTensors_cuspidal adjacentReverseTensor adjacentReverseTensorFactors_eq adjacentReverseTensorStagesEquiv adjacentTensorStagesEquiv associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv glCuspidalTensor isIrreducible_normalizedParabolicInduced_singleBlock minimalNonzeroJacquet refinedHalfModulus_eq_one_of_full refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full totalConjugatingCount
open Langlands.GeneralLinear
open Langlands.Parabolic hiding NormalizedRefinementInductionTransitivityClause ParabolicQuotientCompactClause RefinedInductionTensorTheorem RefinementCoordinatesNormalizationTheorem UnipotentFiniteContainmentClause isCompact_integralRange normalizedRefinementInductionTransitivity orderedRefinementInductionEquiv orderedRefinementIteratedInduced orderedRefinementTensorFactors orderedRefinementTensorInductionEquiv parabolicQuotientCompact quotientMap_image_integralRange refinedInductionTensor refinementCoordinatesNormalization
open Langlands.AllFieldBZ.Parabolic
universe uF uV

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

/-- The actual supercuspidal tensor inside each original merged block. -/
def adjacentInnerTensor :
    letI := T.topology
    (∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) →
      Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T (B.adjacentMerge j hj)
        (B.adjacentRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,k⟩)).obj)

/-- The actual supercuspidal tensor with each inner order reversed. -/
def adjacentReverseTensor :
    letI := T.topology
    (∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) →
      Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T (B.adjacentMerge j hj)
        (B.adjacentReverseRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,Fin.rev k⟩)).obj)

private theorem _root_.Langlands.CuspidalSupport.family_rankCast_eq {ι : Sort*} (r : ι → ℕ) {X : ℕ → Sort*}
    (A : ∀ i, X (r i)) {a b : ι} (hab : a = b) (h : r a = r b) :
    (h.symm ▸ A b : X (r a)) = A a := by
  subst b
  rfl

/-- The regrouped target factors are the actual reversed inner tensor objects,
including the transports of their carriers. -/
theorem adjacentReverseTensorFactors_eq :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      Langlands.AllFieldBZ.Parabolic.orderedRefinementTensorFactors F T (B.permute (B.adjacentSwap j hj))
        (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
        (B.adjacentBlockEquiv j hj) (B.adjacentReverse_size j hj)
        (fun i => (A (B.adjacentSwap j hj i)).obj) =
      adjacentReverseTensor F T B j hj A := by
  let := T.topology
  intro A
  funext m
  apply congrArg FiniteTensor.externalSmoothObject
  funext k
  exact family_rankCast_eq B.size
    (X := fun r => SmoothRep.{0,uF,uV} ℂ (GeneralLinear r F.Carrier))
    (fun i => (A i).obj)
    (B.adjacentBlockEquiv_rev j hj m k) (B.adjacentReverse_size j hj ⟨m,k⟩)

/-- The source normalized product is outer induction of the actual normalized
inner tensor inductions in the common merged shape. -/
def adjacentTensorStagesEquiv
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Langlands.AllFieldBZ.Parabolic.orderedRefinementTensorInductionEquiv F T B (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
    (B.adjacentBlock_size j hj) (B.adjacent_index j hj) (fun i => (A i).obj)

private def _root_.Langlands.CuspidalSupport.stagesFactorsCast {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    {A A' : Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S} (h : A = A')
    {V : Type*} {_ : AddCommMonoid V} {_ : Module ℂ V}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    (E : Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S A))) :
    Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S A')) := by
  subst A'
  exact E

/-- The swapped normalized product is outer induction of the actual reversed
inner tensor inductions in the same merged shape. -/
def adjacentReverseTensorStagesEquiv
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  stagesFactorsCast F T (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
    (adjacentReverseTensorFactors_eq F T B j hj A)
    (Langlands.AllFieldBZ.Parabolic.orderedRefinementTensorInductionEquiv F T
      (B.permute (B.adjacentSwap j hj)) (B.adjacentMerge j hj)
      (B.adjacentReverseRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentReverse_size j hj) (B.adjacentReverse_index j hj)
      (fun i => (A (B.adjacentSwap j hj i)).obj))

/-- Both actual inner tensors are irreducible and Levi-cuspidal. -/
theorem adjacentInnerTensors_cuspidal :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (m : Fin (B.adjacentMerge j hj).length),
      ((adjacentInnerTensor F T B j hj A m).IsIrreducible ∧
        IsLeviCuspidal (B.adjacentRefinement j hj m)
          (adjacentInnerTensor F T B j hj A m).representation) ∧
      ((adjacentReverseTensor F T B j hj A m).IsIrreducible ∧
        IsLeviCuspidal (B.adjacentReverseRefinement j hj m)
          (adjacentReverseTensor F T B j hj A m).representation) := by
  let := T.topology
  intro A m
  exact ⟨glCuspidalTensor F T _ ((B.adjacentMerge j hj).positive m)
      (B.adjacentRefinement j hj m) (fun k => A (B.adjacentBlockEquiv j hj ⟨m,k⟩)),
    glCuspidalTensor F T _ ((B.adjacentMerge j hj).positive m)
      (B.adjacentReverseRefinement j hj m)
      (fun k => A (B.adjacentBlockEquiv j hj ⟨m,Fin.rev k⟩))⟩

/-- The canonical inner block permutation carries each source tensor to its
actual reversed tensor. -/
def adjacentInnerTensorTransportEquiv :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (m : Fin (B.adjacentMerge j hj).length),
      Representation.Equiv
        (transport (B.adjacentRefinement j hj m) (B.adjacentReverseRefinement j hj m)
          ((B.adjacentRefinement j hj m).blockPermutation Fin.revPerm)
          (conjugatesLevi_blockPermutation (F := F.Carrier)
            (B.adjacentRefinement j hj m) Fin.revPerm)
          (adjacentInnerTensor F T B j hj A m).representation)
        (adjacentReverseTensor F T B j hj A m).representation := by
  letI := T.topology
  intro A m
  exact blockPermutationTensorEquiv (B.adjacentRefinement j hj m) Fin.revPerm
    (conjugatesLevi_blockPermutation (F := F.Carrier)
      (B.adjacentRefinement j hj m) Fin.revPerm)
    (fun k => (A (B.adjacentBlockEquiv j hj ⟨m,k⟩)).obj.representation)

end Langlands.AllFieldBZ.CuspidalSupport

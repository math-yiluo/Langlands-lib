import Langlands.AllFieldBZ.Representation.CuspidalSupport.AdjacentMergedTensor
import Langlands.AllFieldBZ.Representation.CuspidalSupport.AdjacentTensorReduction
import Langlands.AllFieldBZ.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.InducedJacquetCount
import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetDetectingFamilyLengthProof
import Langlands.AllFieldBZ.Representation.CuspidalSupport.LeviQuasicuspidalDecompositionProof
import Langlands.AllFieldBZ.Representation.Induction.SingleBlock
import Langlands.AllFieldBZ.Representation.Jacquet.CanonicalLiftBijectivityProof
import Langlands.AllFieldBZ.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.AllFieldBZ.Representation.Parabolic.RefinedInnerInductionObjects
import Langlands.AllFieldBZ.Representation.Tensor.FactorMatchingProof
import Langlands.Representation.CuspidalSupport.AdjacentMatchingAssembly

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.AdjacentMatchingAssembly`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.AdjacentMatchingAssembly` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AdjacentBlockSwapCuspidalInductionFactorsTheorem AssociatedCuspidalInductionFactorsTheorem AssociatedCuspidalInductionHomTheorem AssociatedGeometricPieceEquivalenceTheorem AssociatedGeometricPieceVanishingTheorem AssociatedJacquetFiltrationTheorem CanonicalAdjacentSupercuspidalProductMatchingStatement CompactCoefficientFixedLevelFinitenessTheorem CuspidalEmbeddingTheorem CuspidalInductionLengthTheorem DeterminantUnitCornerStructureStatement DeterminantUnitSmoothDualStatement GLCuspidalTensorAssociationStatement GLCuspidalTensorStatement IrreducibleQuasicuspidalLeviAdmissibilityTheorem JacquetDetectingFamilyLengthTheorem LeviCuspidalConstituentTheorem LeviHarishChandraConverseTheorem LeviHarishChandraRankZeroStatement LeviHarishChandraTheorem LeviQuasicuspidalDecompositionTheorem MinimalNonzeroJacquetTheorem MinimalWeylTransportQuasicuspidalTheorem NonassociatedJacquetSubquotientsTheorem NormalizedJacquetEquivalenceTheorem NormalizedJacquetSubquotientTheorem NormalizedQuasicuspidalEmbeddingTheorem PadicAssociatedGeometricPiecesTheorem PadicLeviAdmissibleFactorizationStatement PadicLeviCuspidalFactorizationStatement PadicLeviTensorSupercuspidalReflectionStatement TotalConjugatingCountTheorem TwoBlockAssociatedCuspidalInductionFactorsTheorem ZeroRankCuspidalEmbeddingTheorem adjacentBlockSwap_of_canonicalProducts adjacentBlockSwap_of_twoBlock_and_length adjacentInnerExternalTensors_matching adjacentInnerInductions_matching adjacentInnerTensor adjacentInnerTensorTransportEquiv adjacentInnerTensors_cuspidal adjacentReverseTensor adjacentReverseTensorFactors_eq adjacentReverseTensorStagesEquiv adjacentTensorStagesEquiv associatedCuspidalInductionFactors_of_adjacent associatedCuspidalInductionFactors_of_length_lt_two associatedGeometricPieceEquivalence canonicalAdjacentProducts_of_twoBlock_and_length canonicalCuspidalTensorData compactCoefficientFixedLevelFiniteness compactCoefficientFixedLevelFiniteness_of_cornerStructure continuous_determinantUnitInclusion cuspidalDatum_eq_of_equiv determinantUnitCompactOpenCofinal determinantUnitCornerStructure determinantUnitInclusion determinantUnitInclusion_apply determinantUnitIsotypic_isCompl determinantUnitLocallyCompactSpace determinantUnitNonarchimedean determinantUnitOpenSubgroup determinantUnitRestriction determinantUnitRestrictionMap determinantUnitRestrictionMap_apply determinantUnitRestrictionMap_comp determinantUnitRestrictionMap_id determinantUnitRestriction_apply determinantUnitSmoothDual determinantUnitSubgroup determinantUnitSubgroup_normal determinantUnitTotalIsotypic_compact determinantUnitTotalIsotypic_exhaust determinantUnit_sup_center_finiteIndex exists_leviPiOpenSubgroup_subset factors_of_blockMap factors_step fullRefinedInductionEquiv fullRefinedJacquetEquiv glCuspidalTensor glCuspidalTensorAssociation isCompact_leviPiOpenSubgroup isIrreducible_normalizedParabolicInduced_singleBlock isOpen_determinantUnitSubgroup jacquetDetectingFamilyLength leviDeterminantNorm leviDeterminantNorm_apply leviHarishChandraConverseTheorem leviHarishChandraRankZero leviHarishChandraTheorem leviPiOpenSubgroup leviQuasicuspidalDecomposition leviQuasicuspidalDecomposition_of_inputs levi_exists_compact_openSubgroup_subset mem_determinantUnitSubgroup mem_determinantUnitSubgroup_iff_normalizedAbs mem_determinantUnitSubgroup_iff_valuation mem_leviPiOpenSubgroup minimalNonzeroJacquet normalizedAbs_eq_one_iff normalizedJacquetEquivalence normalizedJacquetSubquotient normalizedQuasicuspidalEmbedding normalizedQuasicuspidalEmbedding_of padicLeviAdmissibleFactorization padicLeviCuspidalFactorization padicLeviTensorSupercuspidalReflection refinedHalfModulus_eq_one_of_full refinedInnerInductionObjects refinedInverseHalfModulus_eq_one_of_full refinedModulus_eq_one_of_full supercuspidalProductInduced_finiteLength totalConjugatingCount
open Langlands.GeneralLinear
open Langlands.Parabolic hiding LeviInflationAdmissibilityClause NormalizedInducedSurjectivity NormalizedInductionAdmissibilityClause NormalizedInductionFactorMatchingTheorem NormalizedInductionOutputFiniteLength NormalizedInductionOutputMatching NormalizedInductionSourceMatching NormalizedJacquetExactnessClause NormalizedRefinementInductionTransitivityClause ParabolicQuotientCompactClause RefinedInductionTensorTheorem RefinementCoordinatesNormalizationTheorem UnipotentFiniteContainmentClause isCompact_integralRange isSmooth_radical leviInflationAdmissibility nonempty_valueQuotient_equiv_induced normalizedInducedSurjectivity_of_smoothInductionSurjectivity normalizedInductionAdmissibility normalizedInductionFactorMatchingTheorem normalizedInductionFactorMatchingTheorem_of_smoothInductionSurjectivity normalizedInductionObject normalizedInductionOutputMatching_of_surjectivity normalizedJacquetExactness normalizedRefinementInductionTransitivity orderedRefinementInductionEquiv orderedRefinementIteratedInduced orderedRefinementTensorFactors orderedRefinementTensorInductionEquiv parabolicQuotientCompact quotientMap_image_integralRange radicalCoinvariants_exact refinedInductionTensor refinementCoordinatesNormalization unipotentFiniteContainment
open Langlands.AllFieldBZ.Parabolic
universe uF uV uW

variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

/-- The exact two-block theorem compares the merged slot; the published
one-block comparison handles every other actual inner tensor induction. -/
theorem adjacentInnerInductions_matching
    (hTwo : TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV}) :
    letI := T.topology
    ∀ (A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i))
      (m : Fin (B.adjacentMerge j hj).length),
      letI := T.generalLinearTopologicalGroup ((B.adjacentMerge j hj).size m)
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced (B.adjacentRefinement j hj m)
          (adjacentInnerTensor F T B j hj A m).representation))
        (Rep.of (T.normalizedParabolicInduced (B.adjacentReverseRefinement j hj m)
          (adjacentReverseTensor F T B j hj A m).representation)) := by
  let := T.topology
  intro A m
  let := T.generalLinearTopologicalGroup ((B.adjacentMerge j hj).size m)
  have hc := adjacentInnerTensors_cuspidal F T B j hj A m
  have ha : RepresentationsAssociated
      (B.adjacentRefinement j hj m) (B.adjacentReverseRefinement j hj m)
      (adjacentInnerTensor F T B j hj A m).representation
      (adjacentReverseTensor F T B j hj A m).representation :=
    ⟨_, conjugatesLevi_blockPermutation (F := F.Carrier)
      (B.adjacentRefinement j hj m) Fin.revPerm,
      ⟨adjacentInnerTensorTransportEquiv F T B j hj A m⟩⟩
  by_cases hm : m.val = j
  · exact hTwo F T _ ((B.adjacentMerge j hj).positive m) _ _ _ _
      (by change (if m.val = j then 2 else 1) = 2; simp [hm])
      hc.1.1 hc.1.2 hc.2.1 hc.2.2 ha
  · exact associatedCuspidalInductionFactors_of_length_lt_two T _
      ((B.adjacentMerge j hj).positive m) _ _ _ _
      (by change (if m.val = j then 2 else 1) < 2; simp [hm])
      hc.1.1 hc.1.2 hc.2.1 hc.2.2 ha

/-- The actual external tensors of the inner inductions match, with
admissibility established separately for both families. -/
theorem adjacentInnerExternalTensors_matching (hn : 0 < n)
    (hTwo : TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV}) :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      HaveSameJordanHolderFactors
        (Rep.of (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T
          (B.adjacentMerge j hj) (B.adjacentRefinement j hj)
          (adjacentInnerTensor F T B j hj A)))
        (Rep.of (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T
          (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
          (adjacentReverseTensor F T B j hj A))) := by
  let := T.topology
  intro A
  let β := refinedInnerInductionObjects F T (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (adjacentInnerTensor F T B j hj A)
  let β' := refinedInnerInductionObjects F T (B.adjacentMerge j hj)
    (B.adjacentReverseRefinement j hj) (adjacentReverseTensor F T B j hj A)
  have hβ : ∀ m, (β m).IsAdmissible := by
    intro m
    exact Langlands.AllFieldBZ.Parabolic.normalizedInductionAdmissibility F T (B.adjacentRefinement j hj m) _
      (adjacentInnerTensor F T B j hj A m).representation
      (adjacentInnerTensors_cuspidal F T B j hj A m).1.2.1
  have hβ' : ∀ m, (β' m).IsAdmissible := by
    intro m
    exact Langlands.AllFieldBZ.Parabolic.normalizedInductionAdmissibility F T (B.adjacentReverseRefinement j hj m) _
      (adjacentReverseTensor F T B j hj A m).representation
      (adjacentInnerTensors_cuspidal F T B j hj A m).2.2.1
  exact FiniteTensor.padicExternalTensorFactors F T n hn (B.adjacentMerge j hj)
    β β' hβ hβ' (adjacentInnerInductions_matching F T B j hj hTwo A)

/-- The full cuspidal length input applies to the actual global tensor. -/
theorem supercuspidalProductInduced_finiteLength (hn : 0 < n)
    (hLength : CuspidalInductionLengthTheorem.{uF,uV} F T n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        (T.normalizedProductInduced B (fun i => (A i).obj.representation)).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A
  have hc := glCuspidalTensor F T n hn B A
  exact (hLength B (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    hc.1 hc.2).1

private theorem _root_.Langlands.CuspidalSupport.finiteLength_throughEquiv {G : Type*} [Monoid G]
    {V W : Type*} {_ : AddCommGroup V} {_ : Module ℂ V}
    {_ : AddCommGroup W} {_ : Module ℂ W}
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (E : Representation.Equiv ρ τ)
    (h : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ G) τ.asModule :=
  FiniteLengthAssembly.finiteLength_of_surjective E.toIntertwiningMap E.surjective h

private theorem _root_.Langlands.CuspidalSupport.matchingThroughStages {r : ℕ} (D : BlockShape r)
    (S S' : Langlands.Geometric.BlockRefinement D)
    (C : Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S)
    (C' : Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S')
    {V W : Type*} {_ : AddCommGroup V} {_ : Module ℂ V}
    {_ : AddCommGroup W} {_ : Module ℂ W}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear r F.Carrier) W}
    (E : Representation.Equiv ρ (T.normalizedParabolicInduced D
      (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S C)))
    (E' : Representation.Equiv τ (T.normalizedParabolicInduced D
      (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S' C')))
    (h : HaveSameJordanHolderFactors
      (Rep.of (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S C))
      (Rep.of (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S' C')))
    (hρ : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear r F.Carrier)) ρ.asModule)
    (hτ : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear r F.Carrier)) τ.asModule) :
    HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of τ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  let σ := FiniteTensor.externalSmoothObject (refinedInnerInductionObjects F T D S C)
  let σ' := FiniteTensor.externalSmoothObject (refinedInnerInductionObjects F T D S' C')
  have houter := Langlands.AllFieldBZ.Parabolic.normalizedInductionFactorMatchingTheorem F T r D σ σ' h
    (finiteLength_throughEquiv E hρ) (finiteLength_throughEquiv E' hτ)
  exact haveSameJordanHolderFactors_transport houter E.symm E'.symm

private theorem _root_.Langlands.CuspidalSupport.sourceTensorFactors_eq :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      Langlands.AllFieldBZ.Parabolic.orderedRefinementTensorFactors F T B (B.adjacentMerge j hj)
        (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
        (B.adjacentBlock_size j hj) (fun i => (A i).obj) =
      adjacentInnerTensor F T B j hj A := by
  let := T.topology
  intro A
  rfl

private def _root_.Langlands.CuspidalSupport.stagesFactorsCast {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    {C C' : Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.Factors.{uF,uV} F T D S} (h : C = C')
    {V : Type*} {_ : AddCommMonoid V} {_ : Module ℂ V}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    (E : Representation.Equiv ρ (T.normalizedParabolicInduced D
      (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S C))) :
    Representation.Equiv ρ (T.normalizedParabolicInduced D
      (Langlands.AllFieldBZ.Parabolic.RefinedInductionTensor.externalRepresentation F T D S C')) := by
  subst C'
  exact E

private def _root_.Langlands.CuspidalSupport.sourceStages
    (A : letI := T.topology
      ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i)) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  stagesFactorsCast F T (B.adjacentMerge j hj) (B.adjacentRefinement j hj)
    (sourceTensorFactors_eq F T B j hj A) (adjacentTensorStagesEquiv F T B j hj A)

/-- The full two-block matching and cuspidal length inputs yield matching for
the actual canonical adjacent supercuspidal products. -/
theorem canonicalAdjacentProducts_of_twoBlock_and_length
    (hTwo : TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV})
    (hLength : ∀ (F : LocalFieldPackage.{uF})
      (T : F.TopologicalData) (n : ℕ),
        CuspidalInductionLengthTheorem.{uF,uV} F T n) :
    CanonicalAdjacentSupercuspidalProductMatchingStatement.{uF,uV} := by
  intro F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B j hj A
  let E := sourceStages F T B j hj A
  let E' := adjacentReverseTensorStagesEquiv F T B j hj A
  have hsrc := adjacentInnerExternalTensors_matching F T B j hj hn hTwo A
  have hfin := supercuspidalProductInduced_finiteLength F T B hn (hLength F T n) A
  have hfin' := supercuspidalProductInduced_finiteLength F T
    (B.permute (B.adjacentSwap j hj)) hn (hLength F T n)
    (fun i => A (B.adjacentSwap j hj i))
  have hm := matchingThroughStages F T (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (B.adjacentReverseRefinement j hj)
    (adjacentInnerTensor F T B j hj A) (adjacentReverseTensor F T B j hj A)
    E E' hsrc hfin hfin'
  exact hm

/-- Conditional reduction of the complete adjacent target to the exact full
two-block matching and full cuspidal induction length theorems. -/
theorem adjacentBlockSwap_of_twoBlock_and_length
    (hTwo : TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV})
    (hLength : ∀ (F : LocalFieldPackage.{uF})
      (T : F.TopologicalData) (n : ℕ),
        CuspidalInductionLengthTheorem.{uF,uV} F T n) :
    AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW} :=
  adjacentBlockSwap_of_canonicalProducts
    (canonicalAdjacentProducts_of_twoBlock_and_length hTwo hLength)

end Langlands.AllFieldBZ.CuspidalSupport

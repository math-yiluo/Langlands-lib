import Langlands.Representation.CuspidalSupport.AdjacentMergedTensor
import Langlands.Representation.CuspidalSupport.AdjacentTensorReduction
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FactorMatchingProof
import Langlands.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.Representation.Classification.FiniteLengthProof

/-! Conditional assembly of adjacent matching from the two-block and length inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.CuspidalSupport

open GeneralLinear Parabolic

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
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
  · exact hTwo p F T _ ((B.adjacentMerge j hj).positive m) _ _ _ _
      (by change (if m.val = j then 2 else 1) = 2; simp [hm])
      hc.1.1 hc.1.2 hc.2.1 hc.2.2 ha
  · exact associatedCuspidalInductionFactors_of_length_lt_two T _
      ((B.adjacentMerge j hj).positive m) _ _ _ _
      (by change (if m.val = j then 2 else 1) < 2; simp [hm])
      hc.1.1 hc.1.2 hc.2.1 hc.2.2 ha

/-- The actual smooth objects for normalized induction inside each refined
block of a common outer Levi. -/
def refinedInnerInductionObjects {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    (C : RefinedInductionTensor.Factors.{uF,uV} F T D S) :
    letI := T.topology
    ∀ m, SmoothRep.{0,uF,max uF uV} ℂ (GeneralLinear (D.size m) F.Carrier) :=
  letI := T.topology
  fun m => SmoothRep.of (RefinedInductionTensor.blockRepresentations F T D S C m)
    (T.isSmooth_normalizedParabolicInduced (S m) (C m).representation)

/-- The actual external tensors of the inner inductions match, with
admissibility established separately for both families. -/
theorem adjacentInnerExternalTensors_matching (hn : 0 < n)
    (hTwo : TwoBlockAssociatedCuspidalInductionFactorsTheorem.{uF,uV,uV}) :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      HaveSameJordanHolderFactors
        (Rep.of (RefinedInductionTensor.externalRepresentation F T
          (B.adjacentMerge j hj) (B.adjacentRefinement j hj)
          (adjacentInnerTensor F T B j hj A)))
        (Rep.of (RefinedInductionTensor.externalRepresentation F T
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
    exact normalizedInductionAdmissibility F T (B.adjacentRefinement j hj m) _
      (adjacentInnerTensor F T B j hj A m).representation
      (adjacentInnerTensors_cuspidal F T B j hj A m).1.2.1
  have hβ' : ∀ m, (β' m).IsAdmissible := by
    intro m
    exact normalizedInductionAdmissibility F T (B.adjacentReverseRefinement j hj m) _
      (adjacentReverseTensor F T B j hj A m).representation
      (adjacentInnerTensors_cuspidal F T B j hj A m).2.2.1
  exact FiniteTensor.padicExternalTensorFactors p F T n hn (B.adjacentMerge j hj)
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
  have hc := glCuspidalTensor p F T n hn B A
  exact (hLength B (FiniteTensor.externalSmoothObject (fun i => (A i).obj))
    hc.1 hc.2).1

private theorem finiteLength_throughEquiv {G : Type*} [Monoid G]
    {V W : Type*} {_ : AddCommGroup V} {_ : Module ℂ V}
    {_ : AddCommGroup W} {_ : Module ℂ W}
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (E : Representation.Equiv ρ τ)
    (h : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ G) τ.asModule :=
  FiniteLengthAssembly.finiteLength_of_surjective E.toIntertwiningMap E.surjective h


private theorem matchingThroughStages {r : ℕ} (D : BlockShape r)
    (S S' : Langlands.Geometric.BlockRefinement D)
    (C : RefinedInductionTensor.Factors.{uF,uV} F T D S)
    (C' : RefinedInductionTensor.Factors.{uF,uV} F T D S')
    {V W : Type*} {_ : AddCommGroup V} {_ : Module ℂ V}
    {_ : AddCommGroup W} {_ : Module ℂ W}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    {τ : Representation ℂ (GeneralLinear r F.Carrier) W}
    (E : Representation.Equiv ρ (T.normalizedParabolicInduced D
      (RefinedInductionTensor.externalRepresentation F T D S C)))
    (E' : Representation.Equiv τ (T.normalizedParabolicInduced D
      (RefinedInductionTensor.externalRepresentation F T D S' C')))
    (h : HaveSameJordanHolderFactors
      (Rep.of (RefinedInductionTensor.externalRepresentation F T D S C))
      (Rep.of (RefinedInductionTensor.externalRepresentation F T D S' C')))
    (hρ : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear r F.Carrier)) ρ.asModule)
    (hτ : IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear r F.Carrier)) τ.asModule) :
    HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of τ) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup r
  let σ := FiniteTensor.externalSmoothObject (refinedInnerInductionObjects F T D S C)
  let σ' := FiniteTensor.externalSmoothObject (refinedInnerInductionObjects F T D S' C')
  have houter := normalizedInductionFactorMatchingTheorem p F T r D σ σ' h
    (finiteLength_throughEquiv E hρ) (finiteLength_throughEquiv E' hτ)
  exact haveSameJordanHolderFactors_transport houter E.symm E'.symm

private theorem sourceTensorFactors_eq :
    letI := T.topology
    ∀ A : ∀ i, SupercuspidalRep.{uF,uV} (F := F.Carrier) (n := B.size i),
      orderedRefinementTensorFactors F T B (B.adjacentMerge j hj)
        (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
        (B.adjacentBlock_size j hj) (fun i => (A i).obj) =
      adjacentInnerTensor F T B j hj A := by
  let := T.topology
  intro A
  rfl

private def stagesFactorsCast {r : ℕ} (D : BlockShape r)
    (S : Langlands.Geometric.BlockRefinement D)
    {C C' : RefinedInductionTensor.Factors.{uF,uV} F T D S} (h : C = C')
    {V : Type*} {_ : AddCommMonoid V} {_ : Module ℂ V}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    (E : Representation.Equiv ρ (T.normalizedParabolicInduced D
      (RefinedInductionTensor.externalRepresentation F T D S C))) :
    Representation.Equiv ρ (T.normalizedParabolicInduced D
      (RefinedInductionTensor.externalRepresentation F T D S C')) := by
  subst C'
  exact E

private def sourceStages
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
    (hLength : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (T : F.TopologicalData) (n : ℕ),
        CuspidalInductionLengthTheorem.{uF,uV} F T n) :
    CanonicalAdjacentSupercuspidalProductMatchingStatement.{uF,uV} := by
  intro p _ F T n hn
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro B j hj A
  let E := sourceStages F T B j hj A
  let E' := adjacentReverseTensorStagesEquiv F T B j hj A
  have hsrc := adjacentInnerExternalTensors_matching F T B j hj hn hTwo A
  have hfin := supercuspidalProductInduced_finiteLength F T B hn (hLength p F T n) A
  have hfin' := supercuspidalProductInduced_finiteLength F T
    (B.permute (B.adjacentSwap j hj)) hn (hLength p F T n)
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
    (hLength : ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
      (T : F.TopologicalData) (n : ℕ),
        CuspidalInductionLengthTheorem.{uF,uV} F T n) :
    AdjacentBlockSwapCuspidalInductionFactorsTheorem.{uF,uV,uW} :=
  adjacentBlockSwap_of_canonicalProducts
    (canonicalAdjacentProducts_of_twoBlock_and_length hTwo hLength)

end Langlands.CuspidalSupport

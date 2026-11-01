import Langlands.Representation.Parabolic.RefinedInnerInductionObjects
import Langlands.Representation.Parabolic.WholeLeviConjugacyStatement
import Langlands.Representation.Parabolic.ProductReversalFactorsProof
import Langlands.Representation.Parabolic.FiniteLengthFunctorProof
import Langlands.Representation.Parabolic.InductionFactorMatchingProof
import Langlands.Representation.Parabolic.InductionFiltration
import Langlands.Representation.Parabolic.OrderedRefinementTensorInduction
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Classification.TwoFactorProductConstituentCommutativityProof
import Langlands.Representation.Classification.FiniteLengthProof
import Langlands.Representation.CuspidalSupport.AdjacentMergedTensor
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.CuspidalSupport.BlockPermutationTensor
import Langlands.Representation.CuspidalSupport.IrreducibleLeviAdmissibilityProof
import Langlands.Representation.CuspidalSupport.LeviAdmissibleFactorizationProof
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof
import Langlands.Representation.CuspidalSupport.TotalConjugatingCountProof
import Langlands.Representation.Tensor.FactorMatchingProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Filtration.FactorMatchingPullback
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.JordanHolderComparisonProof
import Langlands.Representation.Filtration.JordanHolderTransportProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Smooth.IrreducibleRealization
import Langlands.Representation.Smooth.Schur.Proof

/-!
# Weyl conjugacy invariance of finite-length normalized induction

Proof of `Langlands.Parabolic.WholeLeviInductionConjugacy`.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Parabolic.WholeLeviConjugacyProof

open GeneralLinear Geometric CuspidalSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-! ### At most one block -/

/-- A conjugating permutation from a shape with at most one block has that same
shape as target, and it preserves the blocks. -/
theorem eq_and_mem_blockWeyl_of_length_lt_two {n : ℕ} {B C : BlockShape n}
    {w : Equiv.Perm (Fin n)} (hw : ConjugatesLevi (F := F.Carrier) B C w)
    (hB : B.length < 2) :
    C = B ∧ w ∈ blockWeyl B := by
  have hlen : B.length = C.length := TotalConjugatingCount.length_eq hw
  refine ⟨?_, fun a => Fin.ext (by
    have h1 := (blockIndex B (w a)).isLt
    have h2 := (blockIndex B a).isLt
    omega)⟩
  rcases (by omega : B.length = 0 ∨ B.length = 1) with h0 | h1
  · exact BlockShape.ext_of_size (by omega) (fun i => absurd i.isLt (by omega))
  · exact eq_of_length_eq_one (by omega) h1

/-- For at most one block, a finite-length source and any representation
equivalent to its transport have induced representations with the same
composition factors. -/
theorem factors_of_length_lt_two {n : ℕ} (B C : BlockShape n) (w : Equiv.Perm (Fin n))
    (hw : ConjugatesLevi (F := F.Carrier) B C w) (hB : B.length < 2) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.HasFiniteLength →
      Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
      letI := T.generalLinearTopologicalGroup n
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  obtain ⟨rfl, hb⟩ := eq_and_mem_blockWeyl_of_length_lt_two F hw hB
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ τ hσ ⟨φ⟩
  have hfin := (normalizedParabolicFiniteLength.{uF, uV} F T).1 n C σ hσ
  obtain ⟨r, s, hs⟩ := exists_hasSimpleFactors_of_hasFiniteLength _ hfin
  exact FactorMatchingProof.haveSameJordanHolderFactors_of_equiv
    (T.normalizedParabolicInducedEquiv C
      ((transportWeylEquiv w hb hw σ.representation).symm.trans φ)) ⟨r, s, hs⟩

/-! ### Irreducible admissible families -/

/-- A finite external tensor of irreducible admissible factors is irreducible. -/
theorem isIrreducible_external_of_admissible {L : ℕ} {H : Fin L → Type uF}
    [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
    (A : ∀ i, SmoothRep.{0, uF, uV} ℂ (H i))
    (hi : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (ha : letI := T.topology; ∀ i, (A i).IsAdmissible) :
    (FiniteTensor.externalSmoothObject A).IsIrreducible := by
  have : ∀ i, (A i).representation.IsIrreducible := hi
  exact FiniteTensor.isIrreducible_external (fun i => (A i).representation)
    (fun i φ => (admissibleSchur_scalarEndomorphism _ (ha i) (hi i) φ).exists)

/-- The normalized product of irreducible admissible factors has finite length. -/
theorem productInduced_finiteLength {n : ℕ} (B : BlockShape n) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (A i).IsIrreducible) → (∀ i, (A i).IsAdmissible) →
      IsFiniteLength (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
        (T.normalizedProductInduced B (fun i => (A i).representation)).asModule := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro A hi ha
  exact (normalizedParabolicFiniteLength.{uF, uV} F T).1 n B
    (FiniteTensor.externalSmoothObject A)
    (SmoothRep.hasFiniteLength_of_isIrreducible (isIrreducible_external_of_admissible A hi ha))

/-! ### An adjacent swap of irreducible admissible factors -/

section Adjacent

variable {n : ℕ} (B : BlockShape n) (j : ℕ) (hj : j + 1 < B.length)

/-- The actual tensor of the original factors inside each merged block. -/
def innerTensor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) →
      RefinedInductionTensor.Factors.{uF, uV} F T (B.adjacentMerge j hj)
        (B.adjacentRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject (fun k => A (B.adjacentBlockEquiv j hj ⟨m, k⟩))

/-- The actual tensor of the original factors with each inner order reversed. -/
def reverseTensor :
    letI := T.topology
    (∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier)) →
      RefinedInductionTensor.Factors.{uF, uV} F T (B.adjacentMerge j hj)
        (B.adjacentReverseRefinement j hj) :=
  letI := T.topology
  fun A m => FiniteTensor.externalSmoothObject
    (fun k => A (B.adjacentBlockEquiv j hj ⟨m, Fin.rev k⟩))

private theorem family_rankCast_eq {ι : Sort*} (r : ι → ℕ) {X : ℕ → Sort*}
    (A : ∀ i, X (r i)) {a b : ι} (hab : a = b) (h : r a = r b) :
    (h.symm ▸ A b : X (r a)) = A a := by
  subst b
  rfl

/-- The regrouped factors of the swapped product are the reversed inner tensors. -/
theorem reverseTensorFactors_eq :
    letI := T.topology
    ∀ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      orderedRefinementTensorFactors F T (B.permute (B.adjacentSwap j hj))
        (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
        (B.adjacentBlockEquiv j hj) (B.adjacentReverse_size j hj)
        (fun i => A (B.adjacentSwap j hj i)) =
      reverseTensor F T B j hj A := by
  let := T.topology
  intro A
  funext m
  apply congrArg FiniteTensor.externalSmoothObject
  funext k
  exact family_rankCast_eq B.size
    (X := fun r => SmoothRep.{0, uF, uV} ℂ (GeneralLinear r F.Carrier)) A
    (B.adjacentBlockEquiv_rev j hj m k) (B.adjacentReverse_size j hj ⟨m, k⟩)

private def stagesFactorsCast {r : ℕ} (D : BlockShape r)
    (S : Geometric.BlockRefinement D)
    {A A' : RefinedInductionTensor.Factors.{uF, uV} F T D S} (h : A = A')
    {V : Type*} {_ : AddCommMonoid V} {_ : Module ℂ V}
    {ρ : Representation ℂ (GeneralLinear r F.Carrier) V}
    (E : Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (RefinedInductionTensor.externalRepresentation F T D S A))) :
    Representation.Equiv ρ
      (T.normalizedParabolicInduced D
        (RefinedInductionTensor.externalRepresentation F T D S A')) := by
  subst A'
  exact E

/-- Inside each merged block the inner products of the original and reversed
factors have the same composition factors. -/
theorem innerInductions_matching
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hi : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (ha : letI := T.topology; ∀ i, (A i).IsAdmissible)
    (m : Fin (B.adjacentMerge j hj).length) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup ((B.adjacentMerge j hj).size m)
    HaveSameJordanHolderFactors
      (Rep.of (T.normalizedParabolicInduced (B.adjacentRefinement j hj m)
        (innerTensor F T B j hj A m).representation))
      (Rep.of (T.normalizedParabolicInduced (B.adjacentReverseRefinement j hj m)
        (reverseTensor F T B j hj A m).representation)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup ((B.adjacentMerge j hj).size m)
  by_cases hm : m.val = j
  · have h2 : (B.adjacentRefinement j hj m).length = 2 := by
      change (if m.val = j then 2 else 1) = 2
      simp [hm]
    have h := Classification.twoFactorProductConstituentCommutativity F T _
      (B.adjacentRefinement j hj m) h2
      (fun k => A (B.adjacentBlockEquiv j hj ⟨m, k⟩)) (fun k => hi _)
    dsimp only at h
    rw [Classification.adjacentSwap_zero_eq_revPerm _ h2] at h
    exact h
  · have h1 : (B.adjacentRefinement j hj m).length < 2 := by
      change (if m.val = j then 2 else 1) < 2
      simp [hm]
    exact factors_of_length_lt_two F T (B.adjacentRefinement j hj m)
      (B.adjacentReverseRefinement j hj m)
      ((B.adjacentRefinement j hj m).blockPermutation Fin.revPerm)
      (conjugatesLevi_blockPermutation (B.adjacentRefinement j hj m) Fin.revPerm) h1
      (innerTensor F T B j hj A m) (reverseTensor F T B j hj A m)
      (SmoothRep.hasFiniteLength_of_isIrreducible
        (isIrreducible_external_of_admissible _ (fun k => hi _) (fun k => ha _)))
      ⟨blockPermutationTensorEquiv (B.adjacentRefinement j hj m) Fin.revPerm _
        (fun k => (A (B.adjacentBlockEquiv j hj ⟨m, k⟩)).representation)⟩

/-- The actual external tensors of the inner products match. -/
theorem innerExternalTensors_matching (hn : 0 < n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hi : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (ha : letI := T.topology; ∀ i, (A i).IsAdmissible) :
    letI := T.topology
    HaveSameJordanHolderFactors
      (Rep.of (RefinedInductionTensor.externalRepresentation F T
        (B.adjacentMerge j hj) (B.adjacentRefinement j hj) (innerTensor F T B j hj A)))
      (Rep.of (RefinedInductionTensor.externalRepresentation F T
        (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
        (reverseTensor F T B j hj A))) := by
  let := T.topology
  let β := refinedInnerInductionObjects F T (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (innerTensor F T B j hj A)
  let β' := refinedInnerInductionObjects F T (B.adjacentMerge j hj)
    (B.adjacentReverseRefinement j hj) (reverseTensor F T B j hj A)
  have hβ : ∀ m, (β m).IsAdmissible := fun m =>
    normalizedInductionAdmissibility F T (B.adjacentRefinement j hj m) _
      (innerTensor F T B j hj A m).representation
      (FiniteTensor.isAdmissible_external _ (fun k => ha _))
  have hβ' : ∀ m, (β' m).IsAdmissible := fun m =>
    normalizedInductionAdmissibility F T (B.adjacentReverseRefinement j hj m) _
      (reverseTensor F T B j hj A m).representation
      (FiniteTensor.isAdmissible_external _ (fun k => ha _))
  exact FiniteTensor.padicExternalTensorFactors p F T n hn (B.adjacentMerge j hj)
    β β' hβ hβ' (innerInductions_matching F T B j hj A hi ha)

private theorem finiteLength_throughEquiv {G : Type*} [Monoid G]
    {V W : Type*} {_ : AddCommGroup V} {_ : Module ℂ V}
    {_ : AddCommGroup W} {_ : Module ℂ W}
    {ρ : Representation ℂ G V} {τ : Representation ℂ G W}
    (E : Representation.Equiv ρ τ)
    (h : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) :
    IsFiniteLength (MonoidAlgebra ℂ G) τ.asModule :=
  FiniteLengthAssembly.finiteLength_of_surjective E.toIntertwiningMap E.surjective h

private theorem matchingThroughStages {r : ℕ} (D : BlockShape r)
    (S S' : Geometric.BlockRefinement D)
    (C : RefinedInductionTensor.Factors.{uF, uV} F T D S)
    (C' : RefinedInductionTensor.Factors.{uF, uV} F T D S')
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

/-- Swapping two adjacent irreducible admissible factors preserves the
composition factors of their normalized product. -/
theorem adjacentProduct_factors (hn : 0 < n)
    (A : letI := T.topology
      ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier))
    (hi : letI := T.topology; ∀ i, (A i).IsIrreducible)
    (ha : letI := T.topology; ∀ i, (A i).IsAdmissible) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    HaveSameJordanHolderFactors
      (Rep.of (T.normalizedProductInduced B (fun i => (A i).representation)))
      (Rep.of (T.normalizedProductInduced (B.permute (B.adjacentSwap j hj))
        (fun i => (A (B.adjacentSwap j hj i)).representation))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  let E := stagesFactorsCast F T (B.adjacentMerge j hj) (B.adjacentRefinement j hj)
    (A := orderedRefinementTensorFactors F T B (B.adjacentMerge j hj)
      (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentBlock_size j hj) A)
    (A' := innerTensor F T B j hj A) rfl
    (orderedRefinementTensorInductionEquiv F T B (B.adjacentMerge j hj)
      (B.adjacentRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentBlock_size j hj) (B.adjacent_index j hj) A)
  let E' := stagesFactorsCast F T (B.adjacentMerge j hj) (B.adjacentReverseRefinement j hj)
    (reverseTensorFactors_eq F T B j hj A)
    (orderedRefinementTensorInductionEquiv F T
      (B.permute (B.adjacentSwap j hj)) (B.adjacentMerge j hj)
      (B.adjacentReverseRefinement j hj) (B.adjacentBlockEquiv j hj)
      (B.adjacentReverse_size j hj) (B.adjacentReverse_index j hj)
      (fun i => A (B.adjacentSwap j hj i)))
  exact matchingThroughStages F T (B.adjacentMerge j hj)
    (B.adjacentRefinement j hj) (B.adjacentReverseRefinement j hj)
    (innerTensor F T B j hj A) (reverseTensor F T B j hj A) E E'
    (innerExternalTensors_matching F T B j hj hn A hi ha)
    (productInduced_finiteLength F T B A hi ha)
    (productInduced_finiteLength F T (B.permute (B.adjacentSwap j hj))
      (fun i => A (B.adjacentSwap j hj i)) (fun i => hi _) (fun i => ha _))

end Adjacent

/-! ### Arbitrary reorderings of irreducible admissible factors -/

private theorem haveSameJordanHolderFactors_self {G : Type*} [Monoid G]
    {V : Type*} [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : IsFiniteLength (MonoidAlgebra ℂ G) ρ.asModule) :
    HaveSameJordanHolderFactors (Rep.of ρ) (Rep.of ρ) := by
  obtain ⟨c, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact FactorMatchingProof.haveSameJordanHolderFactors_of_equiv (Representation.Equiv.refl _)
    ⟨_, LengthCriterionProof.hasCompositionSeriesLength_of_compositionSeries
      (A := Rep.of ρ) c h₀ h₁⟩

/-- Reordering irreducible admissible factors by any block permutation
preserves the composition factors of their normalized product. -/
theorem permutedProducts {n : ℕ} (hn : 0 < n) (B : BlockShape n)
    (e : Equiv.Perm (Fin B.length)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    ∀ A : ∀ i, SmoothRep.{0, uF, uV} ℂ (GeneralLinear (B.size i) F.Carrier),
      (∀ i, (A i).IsIrreducible) → (∀ i, (A i).IsAdmissible) →
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedProductInduced B (fun i => (A i).representation)))
        (Rep.of (T.normalizedProductInduced (B.permute e)
          (fun i => (A (e i)).representation))) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  refine Submonoid.induction_of_closure_eq_top_right (closure_adjacent_swaps B.length) e ?_ ?_
  · intro A hi ha
    exact haveSameJordanHolderFactors_self _ (productInduced_finiteLength F T B A hi ha)
  · rintro x _ ⟨j, hj, rfl⟩ ih A hi ha
    exact haveSameJordanHolderFactors_trans _ _ _ _ _ (ih A hi ha)
      (adjacentProduct_factors F T (B.permute x) j hj hn (fun i => A (x i))
        (fun i => hi _) (fun i => ha _))

/-! ### Irreducible Levi representations -/

/-- The conjugacy invariance for an irreducible source in positive rank. -/
theorem irreducible_factors {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F.Carrier) B C w) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.IsIrreducible →
      Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
      letI := T.generalLinearTopologicalGroup n
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup n
  intro σ τ hσ ⟨φ⟩
  obtain ⟨⟨⟨v, hvmin⟩, hv⟩, ⟨⟨b, hb⟩, hwvb⟩, -⟩ := minimalConjugatingCosets w hw
  have hbB : ConjugatesLevi (F := F.Carrier) B B b :=
    conjugatesLevi_of_blockIndex b (fun i => (i : ℕ)) Fin.val_injective
      (fun a => by rw [hb a])
  obtain ⟨e, he⟩ := exists_blockMap_of_conjugatesLevi hv
  have hiso : (transport B C v hv σ.representation).Equiv τ.representation := by
    refine (transportEquiv v hv (transportWeylEquiv b hb hbB σ.representation).symm).trans ?_
    rw [transport_transport hbB hv hw hwvb.symm]
    exact φ
  obtain ⟨rfl, rfl⟩ := eq_blockPermutation_of_blockIndex B e v hv hvmin he
  have hσa := irreducibleLeviAdmissibility F T n B σ hσ
  obtain ⟨A, hAi, hAa, ⟨Eσ⟩⟩ := padicLeviAdmissibleFactorization p F T n hn B σ hσ hσa
  let Eτ : τ.representation.Equiv
      ((B.permute e).blockTensor (fun i => (A (e i)).representation)) :=
    hiso.symm.trans ((transportEquiv (B.blockPermutation e) hv Eσ).trans
      (blockPermutationTensorEquiv B e hv (fun i => (A i).representation)))
  exact haveSameJordanHolderFactors_transport (permutedProducts F T hn B e A hAi hAa)
    (T.normalizedParabolicInducedEquiv B Eσ).symm
    (T.normalizedParabolicInducedEquiv (B.permute e) Eτ).symm

/-! ### Finite-length Levi representations -/

/-- The conjugacy invariance for a finite-length source in positive rank. -/
theorem finiteLength_factors {n : ℕ} (hn : 0 < n) (B C : BlockShape n)
    (w : Equiv.Perm (Fin n)) (hw : ConjugatesLevi (F := F.Carrier) B C w) :
    letI := T.topology
    ∀ (σ : SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier))
      (τ : SmoothRep.{0, uF, uW} ℂ (C.Levi F.Carrier)),
      σ.HasFiniteLength →
      Nonempty ((transport B C w hw σ.representation).Equiv τ.representation) →
      letI := T.generalLinearTopologicalGroup n
      HaveSameJordanHolderFactors
        (Rep.of (T.normalizedParabolicInduced B σ.representation))
        (Rep.of (T.normalizedParabolicInduced C τ.representation)) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup n
  intro σ τ hσ ⟨φ⟩
  obtain ⟨r, s, hs⟩ := exists_hasSimpleFactors_of_hasFiniteLength σ hσ
  let L := (leviConjugation B C w hw).symm.toMonoidHom
  have hL : Function.Surjective L := (leviConjugation B C w hw).symm.surjective
  let s' := FiniteTensor.FactorMatchingProof.filtrationComp s L hL
  let indF := normalizedInductionFiltration T B σ.representation s
  let indF' := normalizedInductionFiltration T C
    (transport B C w hw σ.representation) s'
  have hmatch : ∀ i : Fin r, HaveSameJordanHolderFactors (indF.gradedRepresentation i)
      (indF'.gradedRepresentation (Equiv.refl _ i)) := by
    intro i
    have hgi : IsSmooth (s.gradedRepresentation i).ρ :=
      isSmooth_of_surjective (s.gradedProjection i).hom (s.gradedProjection_surjective i)
        (isSmooth_of_injective (FactorMatchingProof.subrepInclusion _)
          Subtype.val_injective σ.isSmooth)
    have hti := isSmooth_transport B C w hw hgi
    have h₁ := normalizedInductionFiltrationGradedEquiv T B σ.representation s i σ.isSmooth
    have h₂ := nonempty_normalizedInductionFiltrationGradedEquiv T C
      (transport B C w hw σ.representation) s' i
      (transport B C w hw (s.gradedRepresentation i).ρ)
      (isSmooth_transport B C w hw σ.isSmooth) hti
      (FiniteTensor.FactorMatchingProof.gradedComp s L hL i)
    have h₃ := irreducible_factors F T hn B C w hw
      (SmoothRep.of (s.gradedRepresentation i).ρ hgi)
      (SmoothRep.of (transport B C w hw (s.gradedRepresentation i).ρ) hti)
      (hs i) ⟨Representation.Equiv.refl _⟩
    exact haveSameJordanHolderFactors_transport h₃ h₁.symm h₂.some.symm
  exact haveSameJordanHolderFactors_transport
    (gradedJordanHolderRefinement ℂ (GeneralLinear n F.Carrier) _ _ r indF indF'
      (Equiv.refl _) hmatch)
    (Representation.Equiv.refl _) (T.normalizedParabolicInducedEquiv C φ)

end Langlands.Parabolic.WholeLeviConjugacyProof

namespace Langlands.Parabolic

universe uF uV uW

/-- Weyl conjugacy invariance of finite-length normalized parabolic induction
for `GL_n`, in every rank. -/
theorem wholeLeviInductionConjugacy {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) : WholeLeviInductionConjugacy.{uF, uV, uW} F T := by
  let := T.topology
  intro n B C w hw σ τ hσ _ hφ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact WholeLeviConjugacyProof.factors_of_length_lt_two F T B C w hw
      (by have := B.length_le; omega) σ τ hσ hφ
  · exact WholeLeviConjugacyProof.finiteLength_factors F T hn B C w hw σ τ hσ hφ

end Langlands.Parabolic

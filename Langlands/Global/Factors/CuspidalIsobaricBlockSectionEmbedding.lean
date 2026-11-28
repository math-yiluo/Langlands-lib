import Langlands.Global.Factors.CuspidalBlockFiniteScalarCovariance
import Langlands.Global.Factors.CuspidalBlockOperatorTensorEmbedding
import Langlands.Global.Factors.CuspidalIsobaricBlockSectionReduction

/-! # The prescribed cuspidal induction tensor embeds into the block sections -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 420000
set_option synthInstance.maxHeartbeats 75000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic NumberField InfinitePlaceFamily LocalFactor.Archimedean
open AdelicBlockParabolic AdelicBlockDeterminantCharacter AdelicBlockScalarSections
open FiniteAdelicGL GeneralLinear
open CompletionPadic (padicField)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

private def precomposeFiniteEvaluation
    {G L P K Af Af' Vf : Type u} [Monoid G] [Monoid L]
    [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Af'] [Module ℂ Af']
    [AddCommGroup Vf] [Module ℂ Vf]
    {ρ : Representation ℂ G Af} {ρ' : Representation ℂ G Af'} {τ : Representation ℂ L Vf}
    {leftTranslate : P → G → G} {character : P → ℂ} {levi : P → L} {compact : K → G}
    (e : ρ'.Equiv ρ) (E : FiniteEvaluationData ρ τ leftTranslate character levi compact) :
    FiniteEvaluationData ρ' τ leftTranslate character levi compact where
  evaluate g := (E.evaluate g).comp e.toLinearEquiv.toLinearMap
  right d g a := by
    change E.evaluate g (e (ρ' d a)) = E.evaluate (g * d) (e a)
    exact (congrArg (E.evaluate g) (e.toIntertwiningMap.isIntertwining _ _ d a)).trans
      (E.right d g (e a))
  parabolic p g a := E.parabolic p g (e a)
  compact_injective := fun _ _ h => e.injective (E.compact_injective h)

private theorem isSmooth_of_equiv_to
    {G Af Af' : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Af'] [Module ℂ Af']
    {ρ : Representation ℂ G Af} {ρ' : Representation ℂ G Af'}
    (e : ρ'.Equiv ρ) (hρ : IsSmooth ρ) : IsSmooth ρ' := by
  intro a
  obtain ⟨K, hK⟩ := hρ (e a)
  refine ⟨K, fun g => e.injective ?_⟩
  exact (e.toIntertwiningMap.isIntertwining _ _ g.val a).trans (hK g)

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ} (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
variable (real : {v : InfinitePlace F // v.IsReal} → Fin k → List RealBlock)
variable (complex : {v : InfinitePlace F // v.IsComplex} → Fin k → List ComplexCharacterData)
variable (hr : ∀ v i, (T i).realization.HasRealPlaceParameter v (real v i))
variable (hc : ∀ v i, (T i).realization.HasComplexPlaceParameter v (complex v i))

attribute [local instance] LocalRealization.localRealizationSpaceAddCommGroup

local notation "n" => r + 1
local notation "B" => blockShape hm
local notation "S" => (fun i : Fin k => CuspidalOperatorRealization.realization (T i))
local notation "D" => finiteReferences hm P
local notation "Gf" => FiniteAdelicGL F n
local notation "Pf" => AdelicBlockParabolic.Finite F B
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "FiniteCoeff" => (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients D i)

private local instance (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (AutomorphicForms F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) := Submodule.addCommGroup _
private local instance {j : ℕ} (V : OperatorRealization F j) : AddCommGroup V.Space := Submodule.addCommGroup _
private local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
private local instance : AddCommGroup (smoothCompactFiniteSections F B S) := Submodule.addCommGroup _
private local instance (i : Fin k) : AddCommGroup (BlockInducedReferences.BlockCoefficients D i) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass
private local instance (i : Fin k) : Module ℂ (BlockInducedReferences.BlockCoefficients D i) :=
  inferInstance
private local instance : AddCommGroup FiniteCoeff := groupedFiniteCoefficientGroup D
private local instance : Module ℂ FiniteCoeff := PiTensorProduct.instModule

include hr hc in
private theorem exists_blockOperatorTensorEmbedding_of_evaluations
    {Af : Type u} [AddCommGroup Af] [Module ℂ Af] (ρ : Representation ℂ Gf Af)
    (ef : Gf → Af →ₗ[ℂ] FiniteCoeff) (hρ : IsSmooth ρ)
    (hfr : ∀ d g a, ef g (ρ d a) = ef (g * d) a)
    (hleft : HasFiniteScalarCovariance hm P h ef)
    (hs : Function.Injective (fun a : Af => fun l : Kf => ef l.val a)) :
    ∃ j : Representation.IntertwiningMap
      (originalOrderTensorOperatorAction real complex ρ).toMonoidHom
      (blockSectionOperatorAction F r B S 0).toMonoidHom, Function.Injective j := by
  have hsep (a : Af) (ha : ∀ l : Kf, ef l.val a = 0) : a = 0 :=
    hs (funext fun l => (ha l).trans (map_zero (ef l.val)).symm)
  let j := @cuspidalBlockOperatorTensorEmbedding F _ _ _ r k m hm T P h real complex hr hc
    Af _ _ ρ ef hρ hfr hleft hsep
  exact ⟨j.val, j.property⟩

private def EvaluationBlockEmbeddingStatement : Prop :=
  ∀ {Af : Type u} [AddCommGroup Af] [Module ℂ Af] (ρ : Representation ℂ Gf Af)
    (_ : IsSmooth ρ)
    (_ : @FiniteEvaluationData Gf (FiniteLevi F B) Pf ↥Kf Af FiniteCoeff
      _ _ _ _ (groupedFiniteCoefficientGroup D) _ ρ (groupedFiniteLeviAction D)
      (fun p g => p.val * g) (fun p => parabolicHalfCharacter F B (ofFinite F B p))
      (BlockShape.leviProjection B (FiniteAdeles F)) Subtype.val),
    ∃ j : Representation.IntertwiningMap
      (originalOrderTensorOperatorAction real complex ρ).toMonoidHom
      (blockSectionOperatorAction F r B S 0).toMonoidHom, Function.Injective j

include h hr hc in
set_option linter.all false in
private theorem exists_blockOperatorTensorEmbedding_of_evaluation :
    EvaluationBlockEmbeddingStatement hm P real complex := by
  intro Af _ _ ρ hρ ev
  refine @exists_blockOperatorTensorEmbedding_of_evaluations F _ _ _ r k m hm T P h
    real complex hr hc Af _ _ ρ ev.evaluate hρ ?_ ?_ ?_
  · exact ev.right
  · let translate (z : FullLevi F B) (d : FiniteLevi F B) := z * leviPair F B 1 d
    let pairing := @groupedCoefficientEvaluation F _ _ _ r k m hm T P h
    let shift := @groupedFiniteLevi_scalar F _ _ _ r k m hm T P h
    exact finiteEvaluation_scalarParabolic ev pairing translate shift
  · exact ev.compact_injective

set_option linter.all false in
private theorem referenceEmbedding_of_equiv
    {Af Af' : Type u} [AddCommGroup Af] [Module ℂ Af] [AddCommGroup Af'] [Module ℂ Af']
    (ρ : Representation ℂ Gf Af) (ρ' : Representation ℂ Gf Af')
    (e : ρ.Equiv ρ') (hρ : IsSmooth ρ)
    (ev : @FiniteEvaluationData Gf (FiniteLevi F B) Pf ↥Kf Af FiniteCoeff
      _ _ _ _ (groupedFiniteCoefficientGroup D) _ ρ (groupedFiniteLeviAction D)
      (fun p g => p.val * g) (fun p => parabolicHalfCharacter F B (ofFinite F B p))
      (BlockShape.leviProjection B (FiniteAdeles F)) Subtype.val)
    (H : EvaluationBlockEmbeddingStatement hm P real complex) :
    ∃ j : Representation.IntertwiningMap
      (originalOrderTensorOperatorAction real complex ρ').toMonoidHom
      (blockSectionOperatorAction F r B S 0).toMonoidHom, Function.Injective j := by
  let ev' := precomposeFiniteEvaluation e.symm ev
  let hs := isSmooth_of_equiv_to e.symm hρ
  exact H ρ' hs ev'

local instance referenceEmbeddingTopology (v : FinitePlace F) (j : ℕ) :
    TopologicalSpace (GeneralLinear j (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology j

private abbrev referenceLocalSpace (v : FinitePlace F) :=
  LocalBlockInduced F B v (finiteBlockAction P v)

private abbrev referenceLocalAction (v : FinitePlace F) :
    Representation ℂ (FiniteLocalGL F n v) (referenceLocalSpace hm P v) :=
  (padicField v).canonicalNormalizedProductInduced B (finiteBlockAction P v)

private local instance (v : FinitePlace F) : AddCommGroup (referenceLocalSpace hm P v) :=
  inferInstance
private local instance (v : FinitePlace F) : Module ℂ (referenceLocalSpace hm P v) :=
  inferInstance

set_option synthInstance.maxHeartbeats 150000 in
private local instance : AddCommGroup (D).Source := inferInstance
set_option synthInstance.maxHeartbeats 150000 in
private local instance : Module ℂ (D).Source := inferInstance

private abbrev ReferenceFixed (E : Finset (FinitePlace F)) (a : ∀ v, referenceLocalSpace hm P v) :=
  ∀ (v : FinitePlace F), v ∉ E → ∀ g ∈ localIntegral F n v, referenceLocalAction hm P v g (a v) = a v

set_option maxHeartbeats 1000000 in
private def prescribedFiniteReferencesEquiv
    (E : Finset (FinitePlace F)) (a : ∀ v, referenceLocalSpace hm P v)
    (ha : ReferenceFixed hm P E a) (hne : ∀ v ∉ E, a v ≠ 0) :
    (BlockInducedReferences.sourceRepresentation D).Equiv
      (tensorRepresentation F n (referenceLocalAction hm P) E a ha) :=
  finiteReferencesEquiv hm P h E a ha hne

/-- An embedding for the full operator action on the original-order induction
tensor with a specified family of integral-fixed finite reference vectors. -/
def HasCuspidalReferenceTensorSectionEmbedding
    (E : Finset (FinitePlace F)) (a : ∀ v, referenceLocalSpace hm P v)
    (ha : ReferenceFixed hm P E a) : Prop :=
  ∃ j : Representation.IntertwiningMap
    (originalOrderTensorOperatorAction real complex
      (tensorRepresentation F n (referenceLocalAction hm P) E a ha)).toMonoidHom
    (blockSectionOperatorAction F r B S 0).toMonoidHom, Function.Injective j

include h hr hc in
set_option linter.all false in
set_option maxHeartbeats 850000 in
/-- Transport the grouped finite evaluation to any nonzero integral-fixed
references outside the prescribed finite exceptional set. -/
theorem cuspidalReferenceTensorSectionEmbedding
    (E : Finset (FinitePlace F)) (a : ∀ v, referenceLocalSpace hm P v)
    (ha : ReferenceFixed hm P E a) (hne : ∀ v ∉ E, a v ≠ 0) :
    HasCuspidalReferenceTensorSectionEmbedding hm P real complex E a ha := by
  let ρ' := tensorRepresentation F n (referenceLocalAction hm P) E a ha
  let ρ := BlockInducedReferences.sourceRepresentation D
  let transport := @referenceEmbedding_of_equiv F _ _ _ r k m hm T P real complex
    _ _ _ _ _ _ ρ ρ'
  refine transport ?_ ?_ ?_ ?_
  · exact prescribedFiniteReferencesEquiv hm P h E a ha hne
  · exact BlockInducedReferences.sourceRepresentation_isSmooth D
  · exact cuspidalGroupedFiniteEvaluation hm P
  · exact exists_blockOperatorTensorEmbedding_of_evaluation hm P h real complex hr hc

end Langlands.Global.CuspidalBlockInduction

namespace Langlands.Global

open Automorphic CuspidalBlockInduction

/-- The prescribed original-order source embeds for the full common operator action. -/
theorem cuspidalIsobaricBlockSectionEmbedding :
    CuspidalIsobaricBlockSectionEmbeddingStatement.{u, uQ} := by
  intro F _ _ _ r k m hm T P h A E hsub hfixed real complex
  let D := CuspidalInducedFiniteTensor.assemble hm P h A E hsub hfixed
  let hr := fun v i => ((real v).parameters i).1
  let hc := fun v i => ((complex v).parameters i).1
  let transport := @cuspidalReferenceTensorSectionEmbedding F _ _ _ r k m hm T P h
    (fun v => (real v).blocks) (fun v => (complex v).blocks) hr hc E
  have H := transport D.sourceReference D.source_fixed D.source_nonzero
  exact H

/-- Eisenstein continuation suffices for the all-places isobaric automorphy
conclusion with the block section comparison established. -/
theorem cuspidalIsobaricAutomorphy_of_eisensteinContinuation
    (hcont : EisensteinMeromorphicContinuationStatement.{u}) :
    CuspidalIsobaricAutomorphyStatement.{u, uQ} :=
  cuspidalIsobaricAutomorphy_of_blockSections hcont cuspidalIsobaricBlockSectionEmbedding

end Langlands.Global

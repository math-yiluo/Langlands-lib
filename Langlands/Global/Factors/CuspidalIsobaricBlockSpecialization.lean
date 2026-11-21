import Langlands.Global.AdelicBlockCompactSpecialization
import Langlands.Global.AdelicOperatorTensorCompactFinite
import Langlands.Global.Factors.CuspidalIsobaricTensorCoefficients
import Langlands.Global.Factors.CuspidalIsobaricTensorSimplicity
import Langlands.Representation.Classification.JuxtaposedJacquetImage

/-! # Prescribed isobaric specialization in the smooth block sections -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

universe u

namespace Langlands.Global.CuspidalInducedFiniteTensor

open NumberField Langlands.Archimedean Langlands.Automorphic AdelicOperatorTensor
open AdelicBlockScalarSections EisensteinJet FiniteAdelicGL
open CompletionPadic (padicField)
open Correspondence (AutomorphicObject)
open Langlands.GeneralLinear (BlockShape)
open Langlands.Classification.JuxtaposedShuffle (rangeEquivOfInjective)

attribute [local instance 100] LieRing.ofAssociativeRing

private theorem subquotient_of_embedding {M V W Y : Type*} [Monoid M]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]
    {a : Representation ℂ M V} {b : Representation ℂ M W} {c : Representation ℂ M Y}
    (i : a.IntertwiningMap b) (hi : Function.Injective i)
    (h : ∃ (U : Subrepresentation a) (q : U.toRepresentation.IntertwiningMap c),
      Function.Surjective q) :
    ∃ (U : Subrepresentation b) (q : U.toRepresentation.IntertwiningMap c),
      Function.Surjective q := by
  obtain ⟨U, q, hq⟩ := h
  let inc : U.toRepresentation.IntertwiningMap a := ⟨U.toSubmodule.subtype, fun _ => rfl⟩
  let j := i.comp inc
  let e := rangeEquivOfInjective j (hi.comp Subtype.val_injective)
  exact ⟨j.range, q.comp e.symm.toIntertwiningMap, hq.comp e.symm.surjective⟩

variable {F : Type u} [Field F] [NumberField F] {r : ℕ}

local notation "n" => r + 1
local notation "FiniteGroup" => FiniteAdelicGL F n
local notation "CompactGroup" => standardInfiniteCompact F n
local notation "Operators" => FreeOperatorAlgebra F n
local notation "finOp" => fun g : FiniteGroup => FreeAlgebra.ι ℂ (Sum.inl (Sum.inl g))
local notation "cmpOp" => fun k : CompactGroup => FreeAlgebra.ι ℂ (Sum.inl (Sum.inr k))

variable (B : BlockShape (r + 1)) (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "Sections" => smoothCompactFiniteSections F B S
local notation "sectionAction" => blockSectionOperatorAction F r B S 0
local notation "Stable" => StableAutomorphicFunctions F n

local instance isobaricFiniteSmoothSectionGroup :
    AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance isobaricSectionsGroup : AddCommGroup Sections := Submodule.addCommGroup _
local instance isobaricSpecializationRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance isobaricSpecializationContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance isobaricSpecializationSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance isobaricSpecializationStableGroup : AddCommGroup Stable := Submodule.addCommGroup _

set_option maxHeartbeats 750000 in
private theorem exists_formIntertwiner_of_blockSubquotient
    (hS : ∀ i, (S i).IsJointlyAdmissible)
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : BlockEisensteinInjectiveOnFiniteRanges F r B S)
    {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
    (aY : Operators →ₐ[ℂ] Module.End ℂ Y)
    (hY : Representation.IsIrreducible aY.toMonoidHom)
    (σ : Representation ℂ FiniteGroup Y) (ν : Representation ℂ CompactGroup Y)
    (hσ : ∀ g, aY (finOp g) = σ g) (hν : ∀ k, aY (cmpOp k) = ν k)
    (U : Subrepresentation (sectionAction).toMonoidHom)
    (q : U.toRepresentation.IntertwiningMap aY.toMonoidHom) (hq : Function.Surjective q) :
    ∃ (N : Subrepresentation ((stableAutomorphicAction F n).comp (freeOperatorProjection F n).toMonoidHom))
      (p : N.toRepresentation.IntertwiningMap aY.toMonoidHom), Function.Surjective p := by
  let : Module Operators Y := moduleOfAlgebraAction aY
  let : Module Operators Stable := moduleOfAlgebraAction (stableFreeOperatorAction F n)
  have hrealization : ∃ N : Submodule Operators Stable, ∃ f : N →ₗ[Operators] Y,
      Function.Surjective f :=
    exists_freeOperatorQuotient_of_block_subquotient F r B S hS hcont hinj
      (Y := Y) aY hY σ ν hσ hν U q hq
  obtain ⟨U', q', hq'⟩ := hrealization
  exact exists_freeIntertwiner_of_operatorModuleSurjection F r aY U' q' hq'

private theorem blockSubquotient_of_embedding
    {V Y : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup Y] [Module ℂ Y]
    {a : Operators →ₐ[ℂ] Module.End ℂ V} (aY : Operators →ₐ[ℂ] Module.End ℂ Y)
    (i : Representation.IntertwiningMap a.toMonoidHom (sectionAction).toMonoidHom)
    (hi : Function.Injective i)
    (hsub : ∃ (U : Subrepresentation a.toMonoidHom)
      (q : U.toRepresentation.IntertwiningMap aY.toMonoidHom), Function.Surjective q) :
    ∃ (U : Subrepresentation (sectionAction).toMonoidHom)
      (q : U.toRepresentation.IntertwiningMap aY.toMonoidHom), Function.Surjective q :=
  subquotient_of_embedding (M := Operators) (V := V) (W := ↥Sections) (Y := Y)
    (a := a.toMonoidHom) (b := (sectionAction).toMonoidHom) (c := aY.toMonoidHom) i hi hsub

section ConstituentTensor

variable [CompactSpace (AdeleQuotient F)]
  {k : ℕ} {m : Fin k → ℕ} {T : ∀ i, CuspidalOperatorRealization F (m i)}
  {V : FinitePlace F → Type u} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]
  {ρ : ∀ v, Representation ℂ (FiniteLocalGL F (r + 1) v) (V v)} {E : Finset (FinitePlace F)}

local instance blockSpecializationMatrixTopology (v : FinitePlace F) (p : ℕ) :
    TopologicalSpace (GeneralLinear p (padicField v).Carrier) :=
  (padicField v).canonicalGeneralLinearTopology p

variable (A : ∀ v : FinitePlace F, AutomorphicObject.{u, u} (padicField v) r.succPNat)
  (D : TensorSubquotient F (r + 1) ρ (fun v => (A v).obj.representation) E)
  (real : ∀ v : {v : InfinitePlace F // InfinitePlace.IsReal v}, RealIsobaricPlaceData (r := r) T v)
  (complex : ∀ v : {v : InfinitePlace F // InfinitePlace.IsComplex v}, ComplexIsobaricPlaceData (r := r) T v)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
private abbrev targetReal (v : RP) : Type := realStandardKFinite n (real v).orderedBlocks ⧸ (real v).kernel
private abbrev targetComplex (v : CP) : Type := complexStandardKFinite n (complex v).orderedBlocks ⧸ (complex v).kernel
private abbrev TargetSpace := Space F (RestrictedTensor.Space ℂ _ E D.targetReference)
  (targetReal real) (targetComplex complex)

private abbrev targetFinite : Representation ℂ FiniteGroup (TargetSpace A D real complex) :=
  tensorFiniteAction F n (Vr := targetReal real) (Vc := targetComplex complex)
    (tensorRepresentation F n _ E D.targetReference D.target_fixed)

private abbrev targetCompact : Representation ℂ CompactGroup (TargetSpace A D real complex) :=
  tensorCompactAction F n (Vr := targetReal real) (Vc := targetComplex complex)
    (fun v => (realStandardRep n (real v).orderedBlocks).quotient (real v).kernel (real v).stable.1)
    (fun v => (complexStandardRep n (complex v).orderedBlocks).quotient (complex v).kernel (complex v).stable.1)

set_option maxHeartbeats 180000 in
private theorem target_finiteGenerator (g : FiniteGroup) :
    targetTensorAction A D real complex (finOp g) = targetFinite A D real complex g := by
  simp only [tensorFreeAction, FreeAlgebra.lift_ι_apply]
  rfl

set_option maxHeartbeats 180000 in
private theorem target_compactGenerator (k : CompactGroup) :
    targetTensorAction A D real complex (cmpOp k) = targetCompact A D real complex k := by
  simp only [tensorFreeAction, FreeAlgebra.lift_ι_apply]
  rfl

/-- The original-order induction embeds into the actual block scalar action at zero. -/
def HasBlockSectionEmbedding : Prop :=
  ∃ i : Representation.IntertwiningMap (sourceTensorAction A D real complex).toMonoidHom
      (sectionAction).toMonoidHom,
    Function.Injective i

set_option maxHeartbeats 1100000 in
/-- An exact embedding into the smooth block sections realizes the prescribed quotient
under Eisenstein continuation and convergence-region injectivity. -/
theorem hasTensorRealization_of_blockSectionEmbedding
    (hS : ∀ i, (S i).IsJointlyAdmissible)
    (hcont : EisensteinMeromorphicContinuationStatement.{u})
    (hinj : BlockEisensteinInjectiveOnFiniteRanges F r B S)
    (hcomparison : HasBlockSectionEmbedding B S A D real complex) :
    HasTensorRealization A D
      (fun v => (real v).orderedBlocks) (fun v => (complex v).orderedBlocks)
      (fun v => (real v).kernel) (fun v => (complex v).kernel)
      (fun v => (real v).stable) (fun v => (complex v).stable) := by
  obtain ⟨i, hi⟩ := hcomparison
  apply hasTensorRealization_of_targetSurjection
  obtain ⟨U, q, hq⟩ := blockSubquotient_of_embedding B S (targetTensorAction A D real complex)
    i hi (targetTensorAction_subquotient A D real complex)
  exact exists_formIntertwiner_of_blockSubquotient B S hS hcont hinj
    (targetTensorAction A D real complex) (targetTensorAction_isIrreducible A D real complex)
    (targetFinite A D real complex) (targetCompact A D real complex)
    (target_finiteGenerator A D real complex) (target_compactGenerator A D real complex)
    U q hq

end ConstituentTensor

end Langlands.Global.CuspidalInducedFiniteTensor

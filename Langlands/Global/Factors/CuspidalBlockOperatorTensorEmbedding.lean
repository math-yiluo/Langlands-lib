import Langlands.Automorphic.FreeOperatorPlaceIntertwining
import Langlands.Global.AdelicBlockProjectedSpecialization
import Langlands.Global.AdelicOperatorTensorAction
import Langlands.Global.AdelicOperatorTensorFiniteFactor
import Langlands.Global.Factors.CuspidalBlockSmoothTensorLie
import Langlands.Global.Factors.CuspidalBlockSmoothTensorSection

/-! # The original-order standard tensor as an operator module of block sections -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option Elab.async false
set_option maxHeartbeats 430000
set_option synthInstance.maxHeartbeats 70000

universe u uQ

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic NumberField InfinitePlaceFamily LocalFactor.Archimedean ArchimedeanGL
open AdelicBlockParabolic AdelicBlockScalarSections AdelicOperatorTensor FiniteAdelicGL GeneralLinear
open FiniteTensor (slotAlgebraHom)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)

attribute [local instance 100] LieRing.ofAssociativeRing

section OperatorIntertwining

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]
variable (V : Index F → Type) [∀ p, AddCommGroup (V p)] [∀ p, Module ℂ (V p)]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

local notation "RealSpace" => (fun v => V (Sum.inl v))
local notation "ComplexSpace" => (fun v => V (Sum.inr v))
local notation "Source" => Space F Af RealSpace ComplexSpace
local notation "Slots" => SlotSpace F Af RealSpace ComplexSpace
local notation "InfiniteTensor" => (⨂[ℂ] p, V p)

private theorem intertwines_tensorFreeAction_of_split
    (ρ : Representation ℂ (FiniteAdelicGL F n) Af)
    (κ : ∀ p, Representation ℂ (Compact n p) (V p))
    (δ : ∀ p, Lie n p →ₗ⁅ℂ⁆ Module.End ℂ (V p))
    (ρ' : Representation ℂ (FiniteAdelicGL F n) W)
    (κ' : Representation ℂ (standardInfiniteCompact F n) W)
    (D' : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ W)
    (J : Af ⊗[ℂ] InfiniteTensor →ₗ[ℂ] W)
    (hf : ∀ d x, J ((ρ d).rTensor InfiniteTensor x) = ρ' d (J x))
    (hk : ∀ p q x, J ((slotAlgebraHom p (κ p q)).lTensor Af x) =
      κ' (compactInclusion n p q) (J x))
    (hδ : ∀ p X x, J ((slotAlgebraHom p (δ p X)).lTensor Af x) =
      D' (envelopingGenerator F n (lieInclusion n p X)) (J x))
    (a : FreeOperatorAlgebra F n) (x : Source) :
    J (splitFiniteTensor F V
      (tensorFreeAction F n (Vr := RealSpace) (Vc := ComplexSpace) ρ
        (fun v => κ (.inl v)) (fun v => δ (.inl v)) (fun v => κ (.inr v)) (fun v => δ (.inr v)) a x)) =
      freeActionOfOperators F n ρ' κ' D' a (J (splitFiniteTensor F V x)) := by
  let E := splitFiniteTensor F (Af := Af) V
  let L := J.comp E.toLinearMap
  let κr (v : {v : InfinitePlace F // v.IsReal}) := κ (.inl v)
  let κc (v : {v : InfinitePlace F // v.IsComplex}) := κ (.inr v)
  let δr (v : {v : InfinitePlace F // v.IsReal}) := δ (.inl v)
  let δc (v : {v : InfinitePlace F // v.IsComplex}) := δ (.inr v)
  let f (d : FiniteAdelicGL F n) : Module.End ℂ Source :=
    slotAlgebraHom (.inl ()) (V := Slots) (ρ d)
  let C := tensorCompactAction F n (Vf := Af) κr κc
  let D := UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Af) δr δc)
  change L (freeActionOfOperators F n f C D a x) = freeActionOfOperators F n ρ' κ' D' a (L x)
  refine intertwines_freeActionOfOperators_of_places F n L f ρ' C κ' D D' ?_ ?_ ?_ ?_ ?_ a x
  · intro d y
    exact (congrArg J (splitFiniteTensor_finite F V (ρ d) y)).trans (hf d (E y))
  · intro v q y
    have h := tensorCompactAction_realPlace F n (Vf := Af) κr κc v q
    have h' := congrArg (fun A : Module.End ℂ Source => E (A y)) h
    have hs := splitFiniteTensor_infinite F V (.inl v) (κr v q) y
    exact (congrArg J (h'.trans hs)).trans (hk (.inl v) q (E y))
  · intro v q y
    have h := tensorCompactAction_complexPlace F n (Vf := Af) κr κc v q
    have h' := congrArg (fun A : Module.End ℂ Source => E (A y)) h
    have hs := splitFiniteTensor_infinite F V (.inr v) (κc v q) y
    exact (congrArg J (h'.trans hs)).trans (hk (.inr v) q (E y))
  · intro v X y
    have h : D (envelopingGenerator F n (realPlaceComplexLieInclusion F n v X)) =
        slotAlgebraHom (.inr (.inl v)) (V := Slots) (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (δr v X)) := by
      change UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Af) δr δc)
        (UniversalEnvelopingAlgebra.ι ℂ (realPlaceComplexLieInclusion F n v X)) = _
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact tensorLieAction_realPlace F n (Vf := Af) δr δc v X
    have h' := congrArg (fun A : Module.End ℂ Source => E (A y)) h
    have hs := splitFiniteTensor_infinite F V (.inl v) (δr v X) y
    exact (congrArg J (h'.trans hs)).trans (hδ (.inl v) X (E y))
  · intro v X y
    have h : D (envelopingGenerator F n (complexPlaceComplexLieInclusion F n v X)) =
        slotAlgebraHom (.inr (.inr v)) (V := Slots) (ULift.moduleEquiv.symm.conjAlgEquiv ℂ (δc v X)) := by
      change UniversalEnvelopingAlgebra.lift ℂ (tensorLieAction F n (Vf := Af) δr δc)
        (UniversalEnvelopingAlgebra.ι ℂ (complexPlaceComplexLieInclusion F n v X)) = _
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      exact tensorLieAction_complexPlace F n (Vf := Af) δr δc v X
    have h' := congrArg (fun A : Module.End ℂ Source => E (A y)) h
    have hs := splitFiniteTensor_infinite F V (.inr v) (δc v X) y
    exact (congrArg J (h'.trans hs)).trans (hδ (.inr v) X (E y))

end OperatorIntertwining

section ZeroParameter

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
variable (B : BlockShape (r + 1)) (S : ∀ i, OperatorRealization F (B.size i))

local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
local instance : AddCommGroup (smoothCompactFiniteSections F B S) := Submodule.addCommGroup _

private theorem blockSectionOperatorAction_zero_eq_freeActionOfOperators :
    blockSectionOperatorAction F r B S 0 =
      freeActionOfOperators F (r + 1) (smoothCompactFiniteAction F B S)
        (smoothCompactAction F B S) (sectionEnvelopingAction F B S) := by
  apply FreeAlgebra.hom_ext
  funext i
  simp only [Function.comp_apply, freeActionOfOperators, FreeAlgebra.lift_ι_apply]
  rcases i with (d | k) | a
  · exact blockSectionOperatorAction_finite_at_zero F r B S d
  · exact blockSectionOperatorAction_compact F r B S 0 k
  · exact blockSectionOperatorAction_enveloping_at_zero F r B S a

end ZeroParameter

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
local notation "Sections" => smoothCompactFiniteSections F B S
local notation "D" => finiteReferences hm P
local notation "Ki" => standardInfiniteCompact F n
local notation "Kf" => FiniteAdelicGL.standardIntegral F n
local notation "Gf" => FiniteAdelicGL F n
local notation "A" => infiniteStandardSpace r real complex
local notation "Ai" => (⨂[ℂ] p, A p)
local notation "FiniteCoeff" => (⨂[ℂ] i, BlockInducedReferences.BlockCoefficients D i)
local notation "CI" => (fun (p : Index F) (i : Fin k) => InfiniteBlockCoefficient T i p)

private local instance (j : ℕ) : AddCommGroup (RationalInvariantFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (ContinuousRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (AutomorphicForms F j) := Submodule.addCommGroup _
private local instance (j : ℕ) : AddCommGroup (StableAutomorphicFunctions F j) := Submodule.addCommGroup _
private local instance {j : ℕ} (V : OperatorRealization F j) : AddCommGroup V.Space := Submodule.addCommGroup _
private local instance (p : Index F) (i : Fin k) : AddCommGroup (CI p i) := Submodule.addCommGroup _
private local instance (p : Index F) : AddCommGroup (InfinitePlaceCoefficients T p) :=
  PiTensorProduct.instAddCommGroup
private local instance (i : Fin k) : AddCommGroup (BlockInducedReferences.BlockCoefficients D i) :=
  DirectLimit.instAddCommGroupOfAddMonoidHomClass
private local instance (i : Fin k) : Module ℂ (BlockInducedReferences.BlockCoefficients D i) :=
  inferInstance
private local instance : AddCommGroup FiniteCoeff := groupedFiniteCoefficientGroup D
private local instance : Module ℂ FiniteCoeff := PiTensorProduct.instModule
private local instance : AddCommGroup Ai := PiTensorProduct.instAddCommGroup
private local instance : Module ℂ Ai := PiTensorProduct.instModule
private local instance : AddCommGroup (FiniteSmoothRealizedSections F B S) := Submodule.addCommGroup _
private local instance : AddCommGroup Sections := Submodule.addCommGroup _

variable {Af : Type u} [AddCommGroup Af] [Module ℂ Af]

local notation "κloc" => infiniteStandardLocalAction r real complex
local notation "δloc" => infiniteStandardLocalLie r real complex
local notation "κ∞" => infiniteStandardAction r real complex
local notation "κtensor" => Representation.tprod (Representation.trivial ℂ Ki Af) κ∞
local notation "Source" => Space F Af (fun v => A (.inl v)) (fun v => A (.inr v))

/-- The common free action for the chosen finite source and the original-order
archimedean standard modules. -/
abbrev originalOrderTensorOperatorAction (ρ : Representation ℂ Gf Af) :
    FreeOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ Source :=
  tensorFreeAction F n (Vr := fun v => A (.inl v)) (Vc := fun v => A (.inr v)) ρ
    (fun v => κloc (.inl v)) (fun v => δloc (.inl v))
    (fun v => κloc (.inr v)) (fun v => δloc (.inr v))

omit [CompactSpace (AdeleQuotient F)] in
private theorem originalOrderCompact_slot (p : Index F) (q : Compact n p) :
    κtensor (compactInclusion n p q) = (slotAlgebraHom p (κloc p q)).lTensor Af := by
  rw [Representation.tprod_apply, infiniteStandardAction_inclusion]
  rfl

set_option linter.all false in
/-- A smooth finite source with the cuspidal coefficient evaluation gives an
injective intertwiner for the common free operators on the entire tensor. -/
def cuspidalBlockOperatorTensorEmbedding (ρ : Representation ℂ Gf Af)
    (ef : Gf → Af →ₗ[ℂ] FiniteCoeff) (hρ : IsSmooth ρ)
    (hfr : ∀ d g a, ef g (ρ d a) = ef (g * d) a)
    (hfl : HasFiniteScalarCovariance hm P h ef)
    (hf : ∀ (a : Af), (∀ l : Kf, ef l.val a = 0) → a = 0) :
    {j : Representation.IntertwiningMap
      (originalOrderTensorOperatorAction real complex ρ).toMonoidHom
      (blockSectionOperatorAction F r B S 0).toMonoidHom // Function.Injective j} := by
  let I := cuspidalSmoothTensorSection hm P h real complex hr hc ρ ef hρ hfr hfl hf
  let J : Representation.IntertwiningMap (V := Af ⊗[ℂ] Ai) (W := ↥Sections)
      κtensor (smoothCompactAction F B S) :=
    ⟨I.toLinearMap, fun q => LinearMap.ext (I.compact_intertwines q)⟩
  let E := splitFiniteTensor F (Af := Af) A
  let L := J.toLinearMap.comp E.toLinearMap
  let ei := infiniteEvaluation real complex hm T hr hc
  let e := @groupedCoefficientEquiv F _ _ _ r k m hm T P h
  have hcoef (l : Kf) (a : Af) (b : Ai) :
      normalizedCoefficientMap F B S (compactPair F 1 l) (J (a ⊗ₜ[ℂ] b)) =
        e (ef l.val a ⊗ₜ[ℂ] ei 1 b) := by
    have hI := I.coefficient 1 l (a ⊗ₜ[ℂ] b)
    exact hI.trans (congrArg e (TensorProduct.map_tmul (ef l.val) (ei 1) a b))
  let hLie := @cuspidalSmoothTensorSection_intertwines_placeLie F _ _ _ r k m hm T P h
    real complex hr hc Af _ _ (fun l : Kf => ef l.val) J hcoef
  refine ⟨⟨L, fun a => LinearMap.ext fun x => ?_⟩, I.map_injective.comp E.injective⟩
  let f := smoothCompactFiniteAction F B S
  let c := smoothCompactAction F B S
  let d := sectionEnvelopingAction F B S
  have hOp := blockSectionOperatorAction_zero_eq_freeActionOfOperators F r B S
  have hOp' := congrArg (fun R : FreeOperatorAlgebra F n →ₐ[ℂ] Module.End ℂ Sections => R a (L x)) hOp
  refine Eq.trans ?_ hOp'.symm
  refine intertwines_tensorFreeAction_of_split F n A ρ κloc δloc f c d J.toLinearMap ?_ ?_ ?_ a x
  · intro g y
    exact I.finite_intertwines g y
  · intro p q y
    have hc := J.isIntertwining _ _ (compactInclusion n p q) y
    rw [originalOrderCompact_slot real complex] at hc
    exact hc
  · intro p X y
    exact hLie p X y

end Langlands.Global.CuspidalBlockInduction

import Langlands.Global.Factors.CuspidalPairFactorData
import Langlands.Global.FiniteAdelicGL.BlockParabolicCoefficientAction
import Langlands.Global.FiniteAdelicGL.TensorEquiv
import Langlands.Representation.Unramified.SphericalFixedLineProof

/-! # Finite block induction references from cuspidal spectral presentations -/

noncomputable section

open scoped BigOperators Classical TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option synthInstance.maxHeartbeats 120000

universe u uQ

namespace Langlands.Global.FiniteAdelicGL.BlockInducedReferences

open CompletionPadic

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}
variable {B : GeneralLinear.BlockShape n}
variable {V : FinitePlace F → Fin B.length → Type u}
variable [∀ v i, AddCommGroup (V v i)] [∀ v i, Module ℂ (V v i)]
variable {σ : ∀ v i, Representation ℂ (FiniteLocalGL F (B.size i) v) (V v i)}
variable (D : BlockInducedReferences F B σ)

local notation "A" => (fun v => LocalBlockInduced F B v (σ v))
local notation "ρ" => (fun v : FinitePlace F =>
  PadicField.canonicalNormalizedProductInduced (padicField v) B (σ v))

private abbrev localInducedSubmodule (v : FinitePlace F) :=
  letI : TopologicalSpace (FiniteLocalGL F n v) := (padicField v).canonicalGeneralLinearTopology n
  smoothVectors (Induction.equivariantAction (B.parabolic (FiniteCompletion F v))
    (localBlockInducing F B v (σ v)))

local instance localInducedGroup (v : FinitePlace F) : AddCommGroup (A v) :=
  Submodule.addCommGroup (localInducedSubmodule v (σ := σ))

local instance localInducedModule (v : FinitePlace F) : Module ℂ (A v) :=
  Submodule.module (localInducedSubmodule v (σ := σ))

private def blockReferenceTensorEquiv (i : Fin B.length)
    {W : FinitePlace F → Type uQ} [∀ v, AddCommGroup (W v)] [∀ v, Module ℂ (W v)]
    (τ : ∀ v, Representation ℂ (FiniteLocalGL F (B.size i) v) (W v))
    (E : Finset (FinitePlace F)) (e : ∀ v, W v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (B.size i) v, τ v g (e v) = e v)
    (f : ∀ v, (σ v i).Equiv (τ v))
    (hf : ∀ᶠ v in Filter.cofinite, f v (D.blockReference v i) = e v) :
    (D.blockRepresentation i).Equiv (tensorRepresentation F (B.size i) τ E e he) :=
  tensorEquivOver F (B.size i) (fun v => σ v i) τ D.exceptional E
    (fun v => D.blockReference v i) e (fun v hv g hg => D.blockReference_fixed v hv i ⟨g, hg⟩)
    he f hf

private def sectionReferenceTensorEquiv
    (E : Finset (FinitePlace F)) (e : ∀ v, A v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F n v, ρ v g (e v) = e v)
    (h : ∀ᶠ v in Filter.cofinite, ∃ c : ℂˣ, (c : ℂ) • D.sectionReference v = e v) :
    D.sourceRepresentation.Equiv (tensorRepresentation F n ρ E e he) :=
  tensorEquiv_of_eventually_unit_smul F n ρ D.exceptional E D.sectionReference e
    (fun v hv g hg => D.sectionReference_fixed v hv ⟨g, hg⟩) he h

end Langlands.Global.FiniteAdelicGL.BlockInducedReferences

namespace Langlands.Global.CuspidalBlockInduction

open Automorphic CompletionPadic FiniteAdelicGL
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents)
open Langlands.Unramified

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
variable {r k : ℕ} {m : Fin k → ℕ}

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance {n : ℕ} {v : FinitePlace F} (S : LocalRealization F n v) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable (hm : ∑ i, (m i + 1) = r + 1)
variable {T : ∀ i, CuspidalOperatorRealization F (m i)}
variable (P : ∀ i, CuspidalSpectralPresentation.{u, uQ} (T i))
variable (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))

/-- The standard block shape in the order of the supplied cuspidal realizations. -/
abbrev blockShape : GeneralLinear.BlockShape (r + 1) :=
  ⟨k, fun i => m i + 1, fun _ => Nat.succ_pos _, hm⟩

local notation "B" => blockShape hm

/-- The actual local components taken from the given spectral presentations. -/
abbrev finiteBlockAction (v : FinitePlace F) (i : Fin k) :
    Representation ℂ (FiniteLocalGL F (m i + 1) v) ((P i).localComponent v).Space :=
  ((P i).localComponent v).representation

local notation "σ" => finiteBlockAction P
local notation "A" => (fun v => LocalBlockInduced F B v (σ v))
local notation "ρ" => (fun v : FinitePlace F =>
  PadicField.canonicalNormalizedProductInduced (padicField v) B (σ v))

private abbrev localEquiv (v : FinitePlace F) (i : Fin k) :=
  (P i).presentation.localComponentEquiv (P i).finiteSlice.nonzero v

private def exceptional : Finset (FinitePlace F) :=
  Finset.univ.biUnion fun i => (P i).tensorExceptional

private theorem notMem_tensorExceptional (v : FinitePlace F) (hv : v ∉ exceptional P)
    (i : Fin k) : v ∉ (P i).tensorExceptional := by
  intro hi
  exact hv (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hi⟩)

private abbrev blockReference (v : FinitePlace F) (i : Fin k) :=
  localEquiv P v i ((P i).reference v)

private theorem blockReference_fixed (v : FinitePlace F) (hv : v ∉ exceptional P)
    (i : Fin k) (g : localIntegral F (m i + 1) v) :
    σ v i g.val (blockReference P v i) = blockReference P v i := by
  change ((P i).presentation.localComponent (P i).finiteSlice.nonzero v).representation
    g.val (localEquiv P v i ((P i).reference v)) = blockReference P v i
  have hg := Representation.IntertwiningMap.isIntertwining _ _
    (localEquiv P v i).toIntertwiningMap g.val ((P i).reference v)
  exact hg.symm.trans (congrArg (localEquiv P v i)
    ((P i).reference_fixed v (notMem_tensorExceptional P v hv i) g.val g.property))

private def sectionReferenceAt (v : FinitePlace F) (hv : v ∉ exceptional P) :
    { f : A v //
      (∀ g, localBlockCompactEvaluation F B v (σ v) g f =
        PiTensorProduct.tprod ℂ (blockReference P v)) ∧
      (∀ g : localIntegral F (r + 1) v, ρ v g.val f = f) } :=
  let q := exists_localBlockReference F B v (σ v) (blockReference P v)
    (blockReference_fixed P v hv)
  ⟨Classical.choose q, Classical.choose_spec q⟩

/-- The normalized local induced sections use the pure tensors of the transported
presentation references as their compact values at all unexceptional places. -/
def finiteReferences : BlockInducedReferences F B σ where
  exceptional := exceptional P
  blockReference := blockReference P
  sectionReference v := if hv : v ∉ exceptional P then (sectionReferenceAt hm P v hv).val else 0
  blockReference_fixed v hv := blockReference_fixed P v hv
  sectionReference_fixed v hv g := by
    simp only [dite_eq_left hv]
    exact (sectionReferenceAt hm P v hv).property.2 g
  sectionReference_evaluation v hv g := by
    simp only [dite_eq_left hv]
    exact (sectionReferenceAt hm P v hv).property.1 g

theorem finiteReferences_blockReference_ne_zero
    (v : FinitePlace F) (hv : v ∉ (finiteReferences hm P).exceptional) (i : Fin k) :
    (finiteReferences hm P).blockReference v i ≠ 0 := by
  intro hz
  apply (P i).presentation.reference_nonzero v (notMem_tensorExceptional P v hv i)
  exact (localEquiv P v i).injective (hz.trans (map_zero (localEquiv P v i).toLinearEquiv).symm)

/-- Each block coefficient tensor is equivariantly the exact tensor of the
original spectral presentation, including when its factor universe differs. -/
def blockTensorPresentationEquiv (i : Fin k) :=
  (finiteReferences hm P).blockReferenceTensorEquiv i
    (W := fun v => (P i).localFactor v) (fun v => ((P i).localFactor v).representation)
    (P i).tensorExceptional (P i).reference (P i).reference_fixed
    (fun v => (localEquiv P v i).symm)
    (Filter.Eventually.of_forall fun v => (localEquiv P v i).symm_apply_apply _)

include h in
private theorem finrank_blockIntegral_fixed (v : FinitePlace F)
    (hv : v ∉ (finiteReferences hm P).exceptional) (i : Fin k) :
    Module.finrank ℂ (fixedVectors (σ v i) (localIntegralSubgroup F v (m i + 1))) = 1 := by
  let D := finiteReferences hm P
  have hnz : fixedVectors (σ v i) (localIntegralSubgroup F v (m i + 1)) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).mpr ⟨D.blockReference v i, fun g => D.blockReference_fixed v hv i g,
      finiteReferences_blockReference_ne_zero hm P v hv i⟩
  rw [localIntegralSubgroup, localIntegral_eq_sphericalSubgroup F v (m i)] at hnz ⊢
  exact sphericalFixedLine _ (padicField v) (m i)
    (((P i).localComponent v).padicObject (h i v).1 (h i v).2) hnz

include h in
private theorem eventually_unit_smul_sectionReference (E : Finset (FinitePlace F)) (e : ∀ v, A v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) :
    ∀ᶠ v in Filter.cofinite, ∃ c : ℂˣ, (c : ℂ) • (finiteReferences hm P).sectionReference v = e v := by
  let D := finiteReferences hm P
  apply Filter.eventually_cofinite.mpr
  apply (D.exceptional ∪ E).finite_toSet.subset
  intro v hv
  by_contra hv'
  have hD : v ∉ D.exceptional := fun ha => hv' (Finset.mem_union_left _ ha)
  have hE : v ∉ E := fun ha => hv' (Finset.mem_union_right _ ha)
  let x (i : Fin k) : fixedVectors (σ v i) (localIntegralSubgroup F v (m i + 1)) :=
    ⟨D.blockReference v i, fun g => D.blockReference_fixed v hD i g⟩
  obtain ⟨c, hc⟩ := exists_smul_localBlockReference_eq F B v (σ v) x
    (fun i hi => finiteReferences_blockReference_ne_zero hm P v hD i
      (congrArg Subtype.val hi))
    (finrank_blockIntegral_fixed hm P h v hD)
    (D.sectionReference v) (e v) (D.sectionReference_evaluation v hD)
    (fun g => he v hE g.val g.property)
  have hc0 : c ≠ 0 := fun hz => hne v hE (by simpa only [hz, zero_smul] using hc.symm)
  exact hv ⟨Units.mk0 c hc0, hc⟩

/-- The restricted tensor obtained from any nonzero spherical references is
equivalent to the tensor with the presentation-normalized references. -/
def finiteReferencesEquiv (h : ∀ i, HasIrreducibleAdmissibleComponents (P i))
    (E : Finset (FinitePlace F)) (e : ∀ v, A v)
    (he : ∀ v ∉ E, ∀ g ∈ localIntegral F (r + 1) v, ρ v g (e v) = e v)
    (hne : ∀ v ∉ E, e v ≠ 0) :=
  (finiteReferences hm P).sectionReferenceTensorEquiv E e he
    (eventually_unit_smul_sectionReference hm P h E e he hne)

end Langlands.Global.CuspidalBlockInduction

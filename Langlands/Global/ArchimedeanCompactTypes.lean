import Langlands.Global.ArchimedeanSmoothTopology
import Langlands.Global.ArchimedeanSmoothActionContinuityProof
import Langlands.Global.ArchimedeanCompact
import Langlands.Representation.CompactCoefficient.AdmissibleComplement
import Mathlib.RepresentationTheory.Irreducible

/-!
# Compact-type subspaces of the actual derivative smooth functions

The published right regular representation is transported to the derivative
compact-open topology, bundled as continuous operators and restricted to the
actual standard compact subgroup. Isotypic spans of finite-dimensional
continuous compact representations specialize the generic algebraic
`Langlands.CompactSplitting.isotypicPart`. No projector, decomposition,
semisimplicity or finiteness statement is made.
-/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

open Representation

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

/-- A finite-dimensional continuous complex representation of the actual compact
subgroup, on the canonical model `Fin dim → ℂ` with its product (norm) topology. -/
structure ContinuousCompactRep where
  /-- The complex dimension of the canonical model. -/
  dim : ℕ
  /-- The algebraic representation of the actual compact subgroup. -/
  toRepresentation : Representation ℂ (standardInfiniteCompact K n) (Fin dim → ℂ)
  /-- Joint continuity of the action map. -/
  continuous_action : Continuous fun p : standardInfiniteCompact K n × (Fin dim → ℂ) =>
    toRepresentation p.1 p.2

/-- A compact type: a continuous finite-dimensional representation of the actual
compact subgroup which is algebraically irreducible. -/
structure CompactType extends ContinuousCompactRep K n where
  /-- Algebraic irreducibility, in Mathlib's sense. -/
  isIrreducible : toRepresentation.IsIrreducible

namespace ContinuousCompactRep

variable {K n}

omit [NumberField K] in
/-- Each orbit map of a source representation is continuous. -/
theorem continuous_orbit (τ : ContinuousCompactRep K n) (v : Fin τ.dim → ℂ) :
    Continuous fun k : standardInfiniteCompact K n => τ.toRepresentation k v :=
  τ.continuous_action.comp (Continuous.prodMk continuous_id continuous_const)

omit [NumberField K] in
/-- The matrix of a source representation depends continuously on the group element. -/
theorem continuous_toMatrix' (τ : ContinuousCompactRep K n) :
    Continuous fun k : standardInfiniteCompact K n =>
      LinearMap.toMatrix' (τ.toRepresentation k) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [LinearMap.toMatrix'_apply]
  exact (continuous_apply i).comp (τ.continuous_orbit (Pi.single j 1))

end ContinuousCompactRep

namespace DerivativeSmoothFunctions

/-- The published right regular representation, transported along `toSmooth`. -/
def rightAction : Representation ℂ
    (Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (DerivativeSmoothFunctions K n) where
  toFun g := (toSmooth K n).symm.toLinearMap ∘ₗ
    (smoothRightAction K n g ∘ₗ (toSmooth K n).toLinearMap)
  map_one' := by
    ext f : 1
    simp
  map_mul' g h := by
    ext f : 1
    simp

theorem rightAction_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    rightAction K n g f = (toSmooth K n).symm (smoothRightAction K n g (toSmooth K n f)) :=
  rfl

/-- `toSmooth` intertwines the transported and the published right actions. -/
@[simp]
theorem toSmooth_rightAction
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    toSmooth K n (rightAction K n g f) = smoothRightAction K n g (toSmooth K n f) := by
  rw [rightAction_apply, LinearEquiv.apply_symm_apply]

/-- The pointwise convention `(g • f)(x) = f(x * g)`. -/
theorem toSmooth_rightAction_val
    (g x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    (toSmooth K n (rightAction K n g f)).val x = (toSmooth K n f).val (x * g) := by
  rw [toSmooth_rightAction, smoothRightAction_apply]

/-- Point evaluation of a translate is evaluation at the translated point. -/
@[simp]
theorem evalCLM_rightAction
    (g x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    evalCLM K n x (rightAction K n g f) = evalCLM K n (x * g) f := by
  rw [evalCLM_apply, evalCLM_apply, toSmooth_rightAction_val]

/-- Joint continuity in the derivative topology, by the published continuity theorem. -/
theorem continuous_rightAction :
    Continuous (fun p : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K) ×
      DerivativeSmoothFunctions K n => rightAction K n p.1 p.2) := by
  have h := smoothRightActionContinuity K n
  unfold SmoothRightActionContinuityStatement at h
  simp only [rightAction_apply]
  exact h

/-- Each single right translation is continuous in the derivative topology. -/
theorem continuous_rightAction_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    Continuous (rightAction K n g) := by
  have h := (continuous_rightAction K n).comp
    (Continuous.prodMk_right (Y := DerivativeSmoothFunctions K n) g)
  exact h

/-- Each right translation as a continuous complex linear operator. -/
def rightActionCLM (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n where
  toLinearMap := rightAction K n g
  cont := continuous_rightAction_apply K n g

@[simp]
theorem rightActionCLM_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    rightActionCLM K n g f = rightAction K n g f :=
  rfl

/-- The continuous right translations form a monoid homomorphism. -/
def rightRepresentationCLM :
    Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K) →*
      (DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n) where
  toFun := rightActionCLM K n
  map_one' := by
    ext f
    simp
  map_mul' g h := by
    ext f
    simp

@[simp]
theorem rightRepresentationCLM_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : DerivativeSmoothFunctions K n) :
    rightRepresentationCLM K n g f = rightAction K n g f :=
  rfl

/-- The algebraic representation of the actual compact subgroup. -/
def compactAction :
    Representation ℂ (standardInfiniteCompact K n) (DerivativeSmoothFunctions K n) :=
  (rightAction K n).comp (standardInfiniteCompact K n).subtype

@[simp]
theorem compactAction_apply (k : standardInfiniteCompact K n)
    (f : DerivativeSmoothFunctions K n) :
    compactAction K n k f = rightAction K n k.val f :=
  rfl

/-- The continuous operators of the actual compact subgroup. -/
def compactActionCLM : standardInfiniteCompact K n →*
    (DerivativeSmoothFunctions K n →L[ℂ] DerivativeSmoothFunctions K n) :=
  (rightRepresentationCLM K n).comp (standardInfiniteCompact K n).subtype

/-- The algebraic compact representation is the continuous compact action. -/
@[simp]
theorem compactActionCLM_apply (k : standardInfiniteCompact K n)
    (f : DerivativeSmoothFunctions K n) :
    compactActionCLM K n k f = compactAction K n k f :=
  rfl

/-- Joint continuity of the compact action in the derivative topology. -/
theorem continuous_compactAction :
    Continuous (fun p : standardInfiniteCompact K n × DerivativeSmoothFunctions K n =>
      compactAction K n p.1 p.2) := by
  have h := (continuous_rightAction K n).comp
    ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_snd (X := standardInfiniteCompact K n) (Y := DerivativeSmoothFunctions K n)))
  simp only [compactAction_apply]
  exact h

/-- `toSmooth` intertwines the compact action with the published compact restriction. -/
theorem toSmooth_compactAction (k : standardInfiniteCompact K n)
    (f : DerivativeSmoothFunctions K n) :
    toSmooth K n (compactAction K n k f) =
      (smoothRightAction K n).comp (standardInfiniteCompact K n).subtype k (toSmooth K n f) :=
  toSmooth_rightAction K n k.val f

/-- `toSmooth` as an equivalence of compact representations. -/
def compactActionEquiv : (compactAction K n).Equiv
    ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) :=
  Representation.Equiv.mk (toSmooth K n) fun k => by
    ext f : 1
    exact toSmooth_compactAction K n k f

@[simp]
theorem compactActionEquiv_apply (f : DerivativeSmoothFunctions K n) :
    compactActionEquiv K n f = toSmooth K n f :=
  rfl

/-- The compact representation transported back to `SmoothFunctions` by conjugation. -/
def transportedCompactAction :
    Representation ℂ (standardInfiniteCompact K n) (SmoothFunctions K n) :=
  ((toSmooth K n).conjAlgEquiv ℂ : Module.End ℂ (DerivativeSmoothFunctions K n) →*
    Module.End ℂ (SmoothFunctions K n)).comp (compactAction K n)

/-- The transported representation is exactly the published compact restriction. -/
theorem transportedCompactAction_eq :
    transportedCompactAction K n =
      (smoothRightAction K n).comp (standardInfiniteCompact K n).subtype := by
  ext k f : 2
  change toSmooth K n (compactAction K n k ((toSmooth K n).symm f)) = _
  rw [toSmooth_compactAction, LinearEquiv.apply_symm_apply]

section Isotypic

variable {K n}

/-- The isotypic span of `τ`: the published supremum of all ranges of algebraic
intertwiners from `τ` into the actual compact action. -/
def isotypicSpan (τ : ContinuousCompactRep K n) : Submodule ℂ (DerivativeSmoothFunctions K n) :=
  CompactSplitting.isotypicPart τ.toRepresentation (compactAction K n)

/-- The same supremum in the complete lattice of subrepresentations. -/
def isotypicSubrep (τ : ContinuousCompactRep K n) : Subrepresentation (compactAction K n) :=
  ⨆ f : τ.toRepresentation.IntertwiningMap (compactAction K n), f.range

theorem toSubmodule_isotypicSubrep (τ : ContinuousCompactRep K n) :
    (isotypicSubrep τ).toSubmodule = isotypicSpan τ := by
  rw [isotypicSubrep, Langlands.Subrepresentation.toSubmodule_iSup]
  rfl

/-- Every intertwiner range lies in the isotypic span. -/
theorem range_le_isotypicSpan (τ : ContinuousCompactRep K n)
    (f : τ.toRepresentation.IntertwiningMap (compactAction K n)) :
    LinearMap.range f.toLinearMap ≤ isotypicSpan τ :=
  CompactSplitting.range_le_isotypicPart τ.toRepresentation (compactAction K n) f

/-- The isotypic span is the least submodule containing all intertwiner ranges. -/
theorem isotypicSpan_le_iff (τ : ContinuousCompactRep K n)
    (S : Submodule ℂ (DerivativeSmoothFunctions K n)) :
    isotypicSpan τ ≤ S ↔
      ∀ f : τ.toRepresentation.IntertwiningMap (compactAction K n),
        LinearMap.range f.toLinearMap ≤ S :=
  iSup_le_iff

/-- Membership: finite sums of values of intertwiners. -/
theorem mem_isotypicSpan_iff (τ : ContinuousCompactRep K n)
    (v : DerivativeSmoothFunctions K n) :
    v ∈ isotypicSpan τ ↔
      ∃ (s : Finset (τ.toRepresentation.IntertwiningMap (compactAction K n)))
        (x : τ.toRepresentation.IntertwiningMap (compactAction K n) → Fin τ.dim → ℂ),
        ∑ f ∈ s, f (x f) = v := by
  constructor
  · intro hv
    obtain ⟨s, hs⟩ := Submodule.mem_iSup_iff_exists_finset.mp hv
    obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ v).mp hs
    refine ⟨s, fun f => (LinearMap.mem_range.mp (μ f).2).choose, ?_⟩
    rw [← hμ]
    exact Finset.sum_congr rfl fun f _ => (LinearMap.mem_range.mp (μ f).2).choose_spec
  · rintro ⟨s, x, rfl⟩
    exact Submodule.sum_mem _ fun f _ => range_le_isotypicSpan τ f ⟨x f, rfl⟩

/-- Invariance under the actual compact right action. -/
theorem compactAction_mem_isotypicSpan (τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) {v : DerivativeSmoothFunctions K n}
    (hv : v ∈ isotypicSpan τ) : compactAction K n k v ∈ isotypicSpan τ := by
  rw [← toSubmodule_isotypicSubrep] at hv ⊢
  exact (isotypicSubrep τ).apply_mem_toSubmodule k hv

/-- Isomorphic source representations have the same isotypic span. -/
theorem isotypicSpan_eq_of_equiv {τ τ' : ContinuousCompactRep K n}
    (e : τ.toRepresentation.Equiv τ'.toRepresentation) :
    isotypicSpan τ = isotypicSpan τ' := by
  have key : ∀ {σ σ' : ContinuousCompactRep K n},
      σ.toRepresentation.Equiv σ'.toRepresentation → isotypicSpan σ ≤ isotypicSpan σ' := by
    intro σ σ' e
    refine (isotypicSpan_le_iff σ _).2 fun f => ?_
    rintro _ ⟨x, rfl⟩
    refine range_le_isotypicSpan σ' (f.comp e.symm.toIntertwiningMap) ⟨e x, ?_⟩
    change f (e.symm (e x)) = f x
    rw [e.symm_apply_apply]
  exact le_antisymm (key e) (key e.symm)

/-- The compact-type submodule of an irreducible compact type. -/
abbrev compactTypeSubmodule (σ : CompactType K n) :
    Submodule ℂ (DerivativeSmoothFunctions K n) :=
  isotypicSpan σ.toContinuousCompactRep

end Isotypic

section Selected

variable {K n} {ι : Type*}

/-- The sum of the isotypic spans of a finite selected family of source
representations. No finite-multiplicity hypothesis is made. -/
def selectedIsotypicSum (s : Finset ι) (τ : ι → ContinuousCompactRep K n) :
    Submodule ℂ (DerivativeSmoothFunctions K n) :=
  ⨆ i ∈ s, isotypicSpan (τ i)

/-- The same finite sum in the complete lattice of subrepresentations. -/
def selectedIsotypicSubrep (s : Finset ι) (τ : ι → ContinuousCompactRep K n) :
    Subrepresentation (compactAction K n) :=
  ⨆ i ∈ s, isotypicSubrep (τ i)

theorem toSubmodule_selectedIsotypicSubrep (s : Finset ι) (τ : ι → ContinuousCompactRep K n) :
    (selectedIsotypicSubrep s τ).toSubmodule = selectedIsotypicSum s τ := by
  simp only [selectedIsotypicSubrep, Langlands.Subrepresentation.toSubmodule_iSup,
    toSubmodule_isotypicSubrep, selectedIsotypicSum]

/-- Each selected isotypic span lies in the selected sum. -/
theorem isotypicSpan_le_selectedIsotypicSum {s : Finset ι} (τ : ι → ContinuousCompactRep K n)
    {i : ι} (hi : i ∈ s) : isotypicSpan (τ i) ≤ selectedIsotypicSum s τ :=
  le_iSup₂_of_le (f := fun j (_ : j ∈ s) => isotypicSpan (τ j)) i hi le_rfl

/-- Every intertwiner range from a selected source lies in the selected sum. -/
theorem range_le_selectedIsotypicSum {s : Finset ι} (τ : ι → ContinuousCompactRep K n)
    {i : ι} (hi : i ∈ s) (f : (τ i).toRepresentation.IntertwiningMap (compactAction K n)) :
    LinearMap.range f.toLinearMap ≤ selectedIsotypicSum s τ :=
  (range_le_isotypicSpan (τ i) f).trans (isotypicSpan_le_selectedIsotypicSum τ hi)

/-- Membership: finite sums of one vector from each selected isotypic span. -/
theorem mem_selectedIsotypicSum_iff (s : Finset ι) (τ : ι → ContinuousCompactRep K n)
    (v : DerivativeSmoothFunctions K n) :
    v ∈ selectedIsotypicSum s τ ↔
      ∃ w : ∀ i, isotypicSpan (τ i), ∑ i ∈ s, (w i : DerivativeSmoothFunctions K n) = v :=
  Submodule.mem_iSup_finset_iff_exists_sum _ v

/-- Invariance of the selected sum under the actual compact right action. -/
theorem compactAction_mem_selectedIsotypicSum (s : Finset ι) (τ : ι → ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) {v : DerivativeSmoothFunctions K n}
    (hv : v ∈ selectedIsotypicSum s τ) : compactAction K n k v ∈ selectedIsotypicSum s τ := by
  rw [← toSubmodule_selectedIsotypicSubrep] at hv ⊢
  exact (selectedIsotypicSubrep s τ).apply_mem_toSubmodule k hv

/-- The selected sum of a finite family of irreducible compact types. -/
abbrev selectedTypeSum (s : Finset ι) (σ : ι → CompactType K n) :
    Submodule ℂ (DerivativeSmoothFunctions K n) :=
  selectedIsotypicSum s fun i => (σ i).toContinuousCompactRep

end Selected

section Transfer

variable {K n} {ι : Type*}

/-- The isotypic span transferred to the published `SmoothFunctions`. -/
def smoothIsotypicSpan (τ : ContinuousCompactRep K n) : Submodule ℂ (SmoothFunctions K n) :=
  (isotypicSpan τ).map (toSmooth K n).toLinearMap

theorem mem_smoothIsotypicSpan_iff (τ : ContinuousCompactRep K n) (f : SmoothFunctions K n) :
    f ∈ smoothIsotypicSpan τ ↔ (toSmooth K n).symm f ∈ isotypicSpan τ :=
  Submodule.mem_map_equiv (isotypicSpan τ)

/-- The transferred span is the published isotypic part for the published compact
restriction on `SmoothFunctions`. -/
theorem smoothIsotypicSpan_eq (τ : ContinuousCompactRep K n) :
    smoothIsotypicSpan τ = CompactSplitting.isotypicPart τ.toRepresentation
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) := by
  apply le_antisymm
  · rw [smoothIsotypicSpan, Submodule.map_le_iff_le_comap, isotypicSpan_le_iff]
    rintro f _ ⟨x, rfl⟩
    rw [Submodule.mem_comap]
    exact CompactSplitting.range_le_isotypicPart _ _
      ((compactActionEquiv K n).toIntertwiningMap.comp f) ⟨x, rfl⟩
  · refine iSup_le fun f => ?_
    rintro _ ⟨x, rfl⟩
    rw [mem_smoothIsotypicSpan_iff]
    exact range_le_isotypicSpan τ ((compactActionEquiv K n).symm.toIntertwiningMap.comp f)
      ⟨x, rfl⟩

/-- Invariance of the transferred span under the published compact restriction. -/
theorem smoothRightAction_mem_smoothIsotypicSpan (τ : ContinuousCompactRep K n)
    (k : standardInfiniteCompact K n) {f : SmoothFunctions K n}
    (hf : f ∈ smoothIsotypicSpan τ) : smoothRightAction K n k.val f ∈ smoothIsotypicSpan τ := by
  rw [mem_smoothIsotypicSpan_iff] at hf ⊢
  have h := compactAction_mem_isotypicSpan τ k hf
  rwa [compactAction_apply, rightAction_apply, LinearEquiv.apply_symm_apply] at h

/-- The selected sum transferred to the published `SmoothFunctions`. -/
def smoothSelectedIsotypicSum (s : Finset ι) (τ : ι → ContinuousCompactRep K n) :
    Submodule ℂ (SmoothFunctions K n) :=
  (selectedIsotypicSum s τ).map (toSmooth K n).toLinearMap

/-- The transferred selected sum is the selected sum of the published isotypic parts. -/
theorem smoothSelectedIsotypicSum_eq (s : Finset ι) (τ : ι → ContinuousCompactRep K n) :
    smoothSelectedIsotypicSum s τ = ⨆ i ∈ s, CompactSplitting.isotypicPart (τ i).toRepresentation
      ((smoothRightAction K n).comp (standardInfiniteCompact K n).subtype) := by
  simp only [smoothSelectedIsotypicSum, selectedIsotypicSum, Submodule.map_iSup]
  exact iSup_congr fun i => iSup_congr fun _ => smoothIsotypicSpan_eq (τ i)

end Transfer

end DerivativeSmoothFunctions

end Langlands.Global.ArchimedeanGL

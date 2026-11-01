import Langlands.Automorphic.FullOperatorAction
import Langlands.Automorphic.OperatorEquivalence
import Langlands.Representation.SubrepresentationConjugation

/-! # Actual operator realizations inside the full form space -/

noncomputable section
universe uF
set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global NumberField ContinuousRationalFunctions

variable (F : Type uF) [Field F] [NumberField F] (n : ℕ)

local instance fullRealizationRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance fullRealizationContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullRealizationSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance fullRealizationFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance fullRealizationStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _

/-- Existing actual realizations correspond to every invariant subspace of all forms. -/
def operatorRealizationFullFormOrderIso :
    OperatorRealization F n ≃o Subrepresentation (fullAutomorphicAction F n) :=
  Langlands.conjugatedSubrepresentationOrderIso
    (stableAutomorphicAction F n) (fullAutomorphicAction F n)
    (MulEquiv.refl _) (stableAutomorphicEquiv F n).toLinearEquiv
    (fun a f => (stableAutomorphicEquiv_operatorAction F n a f).symm)

namespace OperatorRealization

variable {F n} (S : OperatorRealization F n)

local instance fullRealizationSpaceGroup : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The image is an actual invariant subspace of the original full form carrier. -/
def fullFormImage : Subrepresentation (fullAutomorphicAction F n) :=
  operatorRealizationFullFormOrderIso F n S

@[simp] theorem fullFormImage_toSubmodule :
    S.fullFormImage.toSubmodule =
      S.toSubmodule.map (stableAutomorphicEquiv F n).toLinearMap := rfl

/-- Membership is precisely membership of the same function in the original realization. -/
theorem mem_fullFormImage_iff (f : AutomorphicForms F n) :
    f ∈ S.fullFormImage ↔ (stableAutomorphicEquiv F n).symm f ∈ S := by
  change f ∈ S.toSubmodule.map (stableAutomorphicEquiv F n).toLinearMap ↔ _
  constructor
  · rintro ⟨g, hg, rfl⟩
    change (stableAutomorphicEquiv F n).symm (stableAutomorphicEquiv F n g) ∈ S.toSubmodule
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hg
  · intro hf
    exact ⟨_, hf, (stableAutomorphicEquiv F n).apply_symm_apply f⟩

/-- The original realization and its actual all-form image have the same subspace topology. -/
def fullFormEquiv : S.Space ≃L[ℂ] S.fullFormImage.toSubmodule :=
  (stableAutomorphicEquiv F n).ofSubmodules _ _ rfl

@[simp] theorem fullFormEquiv_val (f : S.Space) :
    (S.fullFormEquiv f).val = S.formInclusion f := rfl

@[simp] theorem fullFormEquiv_symm_val (f : S.fullFormImage.toSubmodule) :
    (S.fullFormEquiv.symm f).val = (stableAutomorphicEquiv F n).symm f.val := rfl

/-- Every concrete operator is retained by the same continuous identification. -/
theorem fullFormEquiv_operatorAction (a : automorphicOperatorAlgebra F n) (f : S.Space) :
    S.fullFormEquiv (S.representation a f) =
      S.fullFormImage.toRepresentation a (S.fullFormEquiv f) := by
  apply Subtype.ext
  rfl

/-- The subspace comparison is a genuine equivalence of whole operator representations. -/
def fullFormRepresentationEquiv :
    S.representation.Equiv S.fullFormImage.toRepresentation :=
  Representation.Equiv.mk S.fullFormEquiv.toLinearEquiv (by
    intro a
    apply LinearMap.ext
    exact S.fullFormEquiv_operatorAction a)

@[simp] theorem evaluate_fullFormEquiv (f : S.Space) (x : AdelicGL F n) :
    evaluate F n (automorphicToContinuous F n (S.fullFormEquiv f).val) x =
      evaluate F n (S.toContinuous f) x := rfl

/-- Forgetting to finite translation retains exactly the same embedded full-form subspace. -/
def fullFormFiniteImage : FiniteRealization F n where
  toSubmodule := S.fullFormImage.toSubmodule
  apply_mem_toSubmodule d _f hf :=
    S.fullFormImage.apply_mem_toSubmodule (finiteOperator F n d) hf

/-- This finite image is equal as an embedded space to the existing finite realization image. -/
@[simp] theorem fullFormFiniteImage_eq :
    S.fullFormFiniteImage = S.toFiniteRealization := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro f
  constructor
  · rintro ⟨g, hg, hgf⟩
    exact ⟨⟨g, hg⟩, hgf⟩
  · rintro ⟨g, hgf⟩
    exact ⟨g.val, g.property, hgf⟩

/-- The comparison identifies every invariant subspace of the restricted operator actions. -/
def fullFormSubrepresentationOrderIso :
    Subrepresentation S.representation ≃o Subrepresentation S.fullFormImage.toRepresentation :=
  Langlands.conjugatedSubrepresentationOrderIso S.representation
    S.fullFormImage.toRepresentation (MulEquiv.refl _) S.fullFormEquiv.toLinearEquiv
    (fun a f => (S.fullFormEquiv_operatorAction a f).symm)

/-- Irreducibility concerns the full operator action on both sides. -/
theorem fullFormImage_isIrreducible_iff :
    S.fullFormImage.toRepresentation.IsIrreducible ↔ S.IsIrreducible :=
  S.fullFormSubrepresentationOrderIso.isSimpleOrder_iff.symm

/-- The embedded character condition is unchanged, including its idele normalization. -/
theorem fullFormFiniteImage_hasCentralCharacter_iff
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ) :
    S.fullFormFiniteImage.HasCentralCharacter χ ↔ S.HasCentralCharacter χ := by
  rw [fullFormFiniteImage_eq]
  rfl

/-- The actual normalized constant-term condition is unchanged. -/
theorem fullFormFiniteImage_isCuspidal_iff [CompactSpace (AdeleQuotient F)] :
    S.fullFormFiniteImage.IsCuspidal ↔ S.IsCuspidal := by
  rw [fullFormFiniteImage_eq]
  rfl

end OperatorRealization

/-- Generate an existing whole-operator realization from any actual automorphic form. -/
def generatedFormOperatorRealization (f : AutomorphicForms F n) : OperatorRealization F n :=
  generatedOperatorRealization F n ((stableAutomorphicEquiv F n).symm f)

/-- The image contains the original form itself. -/
theorem mem_generatedFormOperatorRealization (f : AutomorphicForms F n) :
    f ∈ (generatedFormOperatorRealization F n f).fullFormImage :=
  ((generatedFormOperatorRealization F n f).mem_fullFormImage_iff f).mpr
    (mem_generatedOperatorRealization F n _)

/-- The generated realization is minimal among all whole-operator invariant form images. -/
theorem generatedFormOperatorRealization_le_iff (f : AutomorphicForms F n)
    (S : OperatorRealization F n) :
    generatedFormOperatorRealization F n f ≤ S ↔ f ∈ S.fullFormImage := by
  rw [generatedFormOperatorRealization, generatedOperatorRealization_le_iff,
    S.mem_fullFormImage_iff]

/-- A supplied nonzero form yields a nonzero actual whole-operator realization. -/
theorem generatedFormOperatorRealization_ne_bot {f : AutomorphicForms F n} (hf : f ≠ 0) :
    generatedFormOperatorRealization F n f ≠ ⊥ := by
  apply generatedOperatorRealization_ne_bot F n
  intro h
  apply hf
  have he := congrArg (stableAutomorphicEquiv F n) h
  simpa only [ContinuousLinearEquiv.apply_symm_apply, map_zero] using he

end Langlands.Automorphic

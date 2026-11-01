import Langlands.Automorphic.OperatorSubquotient

/-! # Actual presentations for invariant subspaces of operator quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance subspaceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance subspaceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance subspaceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance subspaceFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance subspaceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance subspaceRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n) (P : Subrepresentation Q.representation)

/-- The preimage of the supplied quotient subspace, as an actual subspace of forms. -/
def subspaceUpper : OperatorRealization F n where
  toSubmodule :=
    (P.toSubmodule.comap Q.projection.toLinearMap).map Q.upper.inclusion.toLinearMap
  apply_mem_toSubmodule a f hf := by
    obtain ⟨v, hv, hvf⟩ := hf
    refine ⟨Q.upper.representation a v, ?_, ?_⟩
    · change Q.projection (Q.upper.representation a v) ∈ P
      rw [← Q.representation_projection]
      exact P.apply_mem_toSubmodule a hv
    · exact (Representation.IntertwiningMap.isIntertwining _ _ Q.upper.inclusion a v).trans
        (congrArg (stableAutomorphicAction F n a) hvf)

theorem subspaceUpper_le_upper : Q.subspaceUpper P ≤ Q.upper := by
  rintro f ⟨v, _, hvf⟩
  exact hvf ▸ v.property

@[simp] theorem inclusion_mem_subspaceUpper (f : Q.upper.Space) :
    Q.upper.inclusion f ∈ Q.subspaceUpper P ↔ Q.projection f ∈ P := by
  constructor
  · rintro ⟨v, hv, hvf⟩
    exact Q.upper.inclusion_injective hvf ▸ hv
  · intro hf
    exact ⟨f, hf, rfl⟩

/-- The actual numerator inclusion into the original numerator. -/
def subspaceUpperInclusion :
    (Q.subspaceUpper P).representation.IntertwiningMap Q.upper.representation where
  toLinearMap := Submodule.inclusion (Q.subspaceUpper_le_upper P)
  isIntertwining' _ := by ext; rfl

@[simp] theorem subspaceUpperInclusion_val (f : (Q.subspaceUpper P).Space) :
    (Q.subspaceUpperInclusion P f).val = f.val := rfl

theorem subspaceUpperInclusion_injective :
    Function.Injective (Q.subspaceUpperInclusion P) := by
  intro f g h
  apply Subtype.ext
  exact congrArg (fun v : Q.upper.Space => v.val) h

theorem projection_subspaceUpperInclusion_mem (f : (Q.subspaceUpper P).Space) :
    Q.projection (Q.subspaceUpperInclusion P f) ∈ P := by
  apply (Q.inclusion_mem_subspaceUpper P (Q.subspaceUpperInclusion P f)).mp
  exact f.property

/-- The restricted canonical projection onto the supplied invariant subspace. -/
def subspaceNumeratorMap :
    (Q.subspaceUpper P).representation.IntertwiningMap P.toRepresentation where
  toLinearMap := (Q.projection.comp (Q.subspaceUpperInclusion P)).toLinearMap.codRestrict
    P.toSubmodule (Q.projection_subspaceUpperInclusion_mem P)
  isIntertwining' a := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact Representation.IntertwiningMap.isIntertwining _ _
      (Q.projection.comp (Q.subspaceUpperInclusion P)) a f

@[simp] theorem subspaceNumeratorMap_val (f : (Q.subspaceUpper P).Space) :
    (Q.subspaceNumeratorMap P f).val =
      Q.projection (Q.subspaceUpperInclusion P f) := rfl

set_option maxHeartbeats 800000 in
theorem subspaceNumeratorMap_surjective :
    Function.Surjective (Q.subspaceNumeratorMap P) := by
  intro v
  obtain ⟨f, hfv⟩ := Q.projection_surjective v.val
  have hf : Q.upper.inclusion f ∈ Q.subspaceUpper P :=
    (Q.inclusion_mem_subspaceUpper P f).mpr (hfv.symm ▸ v.property)
  refine ⟨⟨Q.upper.inclusion f, hf⟩, Subtype.ext ?_⟩
  exact hfv

/-- An invariant subspace has a concrete numerator and the restricted original denominator. -/
def subspacePresentation : OperatorSubquotient F n :=
  ⟨Q.subspaceUpper P, (Q.subspaceNumeratorMap P).ker⟩

@[simp] theorem mem_subspacePresentation_lower (f : (Q.subspaceUpper P).Space) :
    f ∈ (Q.subspacePresentation P).lower ↔
      Q.subspaceUpperInclusion P f ∈ Q.lower := by
  change Q.subspaceNumeratorMap P f = 0 ↔ _
  exact Subtype.ext_iff.trans (Q.projection_eq_zero_iff (Q.subspaceUpperInclusion P f))

/-- Descend the restricted projection through its exact kernel. -/
def subspaceMap :
    (Q.subspacePresentation P).representation.IntertwiningMap P.toRepresentation :=
  (Q.subspacePresentation P).lift (Q.subspaceNumeratorMap P) le_rfl

@[simp] theorem subspaceMap_projection (f : (Q.subspaceUpper P).Space) :
    Q.subspaceMap P ((Q.subspacePresentation P).projection f) =
      Q.subspaceNumeratorMap P f := rfl

theorem subspaceMap_injective : Function.Injective (Q.subspaceMap P) := by
  apply LinearMap.ker_eq_bot.mp
  exact Submodule.ker_liftQ_eq_bot _ _ _ le_rfl

set_option maxHeartbeats 800000 in
theorem subspaceMap_surjective : Function.Surjective (Q.subspaceMap P) := by
  intro v
  obtain ⟨f, hfv⟩ := Q.subspaceNumeratorMap_surjective P v
  exact ⟨(Q.subspacePresentation P).projection f, hfv⟩

/-- The actual quotient represents precisely the supplied whole-operator subspace. -/
def subspaceEquiv :
    (Q.subspacePresentation P).representation.Equiv P.toRepresentation :=
  (Q.subspaceMap P).ofBijective
    ⟨Q.subspaceMap_injective P, Q.subspaceMap_surjective P⟩

@[simp] theorem subspaceEquiv_projection_val (f : (Q.subspaceUpper P).Space) :
    (Q.subspaceEquiv P ((Q.subspacePresentation P).projection f)).val =
      Q.projection (Q.subspaceUpperInclusion P f) := rfl

/-- Include the constructed quotient into the original quotient through the given subspace. -/
def subspaceInclusion :
    (Q.subspacePresentation P).representation.IntertwiningMap Q.representation where
  toLinearMap := P.toSubmodule.subtype.comp (Q.subspaceMap P).toLinearMap
  isIntertwining' a := by
    apply LinearMap.ext
    intro v
    exact congrArg (fun w : P.toSubmodule => w.val)
      (Representation.IntertwiningMap.isIntertwining _ _ (Q.subspaceMap P) a v)

@[simp] theorem subspaceInclusion_projection (f : (Q.subspaceUpper P).Space) :
    Q.subspaceInclusion P ((Q.subspacePresentation P).projection f) =
      Q.projection (Q.subspaceUpperInclusion P f) := rfl

theorem subspaceInclusion_injective : Function.Injective (Q.subspaceInclusion P) :=
  Subtype.val_injective.comp (Q.subspaceMap_injective P)

@[simp] theorem subspaceInclusion_range : (Q.subspaceInclusion P).range = P := by
  apply Subrepresentation.toSubmodule_injective
  apply Submodule.ext
  intro v
  constructor
  · rintro ⟨w, hw⟩
    exact hw ▸ (Q.subspaceMap P w).property
  · intro hv
    obtain ⟨w, hw⟩ := Q.subspaceMap_surjective P ⟨v, hv⟩
    exact ⟨w, congrArg (fun x : P.toSubmodule => x.val) hw⟩

end OperatorSubquotient
end Langlands.Automorphic

import Langlands.Automorphic.OperatorSubquotient

/-! # Invariant subspaces of actual operator quotients -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic

open Langlands.Global

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientSubspaceRationalGroup : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientSubspaceContinuousGroup : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientSubspaceSmoothGroup : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientSubspaceFormGroup : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance quotientSubspaceStableGroup : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance quotientSubspaceRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

/-- Pull an invariant quotient subspace back through the actual canonical projection. -/
def subrepresentationPreimage (P : Subrepresentation Q.representation) :
    Subrepresentation Q.upper.representation where
  toSubmodule := P.toSubmodule.comap Q.projection.toLinearMap
  apply_mem_toSubmodule a f hf := by
    change Q.projection (Q.upper.representation a f) ∈ P
    rw [← Q.representation_projection]
    exact P.apply_mem_toSubmodule a hf

/-- The image of an invariant numerator subspace under the actual quotient projection. -/
def subrepresentationImage (P : Subrepresentation Q.upper.representation) :
    Subrepresentation Q.representation where
  toSubmodule := P.toSubmodule.map Q.projection.toLinearMap
  apply_mem_toSubmodule a v hv := by
    obtain ⟨f, hf, hfv⟩ := hv
    refine ⟨Q.upper.representation a f, P.apply_mem_toSubmodule a hf, ?_⟩
    exact (Q.representation_projection a f).symm.trans
      (congrArg (Q.representation a) hfv)

@[simp] theorem mem_subrepresentationPreimage
    (P : Subrepresentation Q.representation) (f : Q.upper.Space) :
    f ∈ Q.subrepresentationPreimage P ↔ Q.projection f ∈ P := Iff.rfl

@[simp] theorem mem_subrepresentationImage
    (P : Subrepresentation Q.upper.representation) (v : Q.Space) :
    v ∈ Q.subrepresentationImage P ↔
      ∃ f : Q.upper.Space, f ∈ P ∧ Q.projection f = v := Iff.rfl

theorem lower_le_subrepresentationPreimage (P : Subrepresentation Q.representation) :
    Q.lower ≤ Q.subrepresentationPreimage P :=
  Submodule.le_comap_mkQ Q.lower.toSubmodule P.toSubmodule

@[simp] theorem subrepresentationImage_preimage (P : Subrepresentation Q.representation) :
    Q.subrepresentationImage (Q.subrepresentationPreimage P) = P :=
  Subrepresentation.toSubmodule_injective
    ((Submodule.comapMkQRelIso Q.lower.toSubmodule).left_inv P.toSubmodule)

theorem subrepresentationPreimage_image
    (P : Subrepresentation Q.upper.representation) (hP : Q.lower ≤ P) :
    Q.subrepresentationPreimage (Q.subrepresentationImage P) = P :=
  Subrepresentation.toSubmodule_injective
    (congrArg Subtype.val
      ((Submodule.comapMkQRelIso Q.lower.toSubmodule).right_inv
        ⟨P.toSubmodule, hP⟩))

/-- All quotient invariant subspaces correspond exactly to numerator invariant subspaces
containing the specified denominator. -/
def quotientSubrepresentationOrderIso :
    Subrepresentation Q.representation ≃o Set.Ici Q.lower where
  toFun P := ⟨Q.subrepresentationPreimage P, Q.lower_le_subrepresentationPreimage P⟩
  invFun P := Q.subrepresentationImage P.val
  left_inv := Q.subrepresentationImage_preimage
  right_inv P := Subtype.ext (Q.subrepresentationPreimage_image P.val P.property)
  map_rel_iff' := (Submodule.comapMkQRelIso Q.lower.toSubmodule).map_rel_iff

@[simp] theorem quotientSubrepresentationOrderIso_apply
    (P : Subrepresentation Q.representation) :
    (Q.quotientSubrepresentationOrderIso P).val = Q.subrepresentationPreimage P := rfl

@[simp] theorem quotientSubrepresentationOrderIso_symm_apply
    (P : Set.Ici Q.lower) :
    Q.quotientSubrepresentationOrderIso.symm P = Q.subrepresentationImage P.val := rfl

theorem subrepresentationPreimage_le_iff
    (P T : Subrepresentation Q.representation) :
    Q.subrepresentationPreimage P ≤ Q.subrepresentationPreimage T ↔ P ≤ T :=
  Q.quotientSubrepresentationOrderIso.map_rel_iff

@[simp] theorem subrepresentationPreimage_bot :
    Q.subrepresentationPreimage ⊥ = Q.lower := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.ker_mkQ Q.lower.toSubmodule

@[simp] theorem subrepresentationPreimage_top :
    Q.subrepresentationPreimage ⊤ = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.comap_top Q.projection.toLinearMap

@[simp] theorem subrepresentationImage_lower :
    Q.subrepresentationImage Q.lower = ⊥ := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.mkQ_map_self Q.lower.toSubmodule

@[simp] theorem subrepresentationImage_top :
    Q.subrepresentationImage ⊤ = ⊤ := by
  simpa only [Q.subrepresentationPreimage_top] using
    Q.subrepresentationImage_preimage ⊤

/-- The quotient has no invariant subspaces beyond zero and itself, and is nontrivial,
exactly when its actual denominator is maximal proper among numerator invariant subspaces. -/
theorem isIrreducible_iff_isCoatom :
    Q.IsIrreducible ↔ IsCoatom Q.lower :=
  Q.quotientSubrepresentationOrderIso.isSimpleOrder_iff.trans
    Set.isSimpleOrder_Ici_iff_isCoatom

end OperatorSubquotient
end Langlands.Automorphic

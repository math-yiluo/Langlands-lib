/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-! # Evaluation as a morphism of ringed topoi

Source: Zheng, Construction 4.1; Stacks 00XO and 03D2.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w}) (n : ℕ)
namespace SheafOfModules
/-- Vertical evaluation lifts sequence-site covering sieves.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance systemSequenceEvaluationCocontinuous :
    (Prod.sectR n C).IsCocontinuous J (coefficientSequenceTopology J) where
  cover_lift h := h
private local instance (X : (ℕ × C)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow X (Prod.sectR n C).op) (Type w) :=
  hasLimitsOfShape_of_essentiallySmall _ _
/-- Right Kan extension along a slice exists in the coefficient universe.
Source: Stacks 00XO (blueprint: lem-pur-system-evaluation-topos). -/
instance systemSequenceEvaluationRightKan (F : Cᵒᵖ ⥤ Type w) :
    (Prod.sectR n C).op.HasPointwiseRightKanExtension F := by
  infer_instance

/-- Vertical restriction is additive on module sheaves.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance systemSequenceEvaluationAdditive : (systemSequenceEvaluation B n).Additive where
  map_add := by
    intro X Y f g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    ext x
    rfl

/-- Reassembly is additive because its maps are the original component maps.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance strictSystemToSequenceAdditive : (strictSystemToSequenceFunctor B).Additive where
  map_add := by
    intro M N f g
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro X
    exact congrArg (fun t ↦ t.val.app (op X.unop.2))
      ((systemEvaluation B X.unop.1).map_add (f := f) (g := g))

/-- Restriction to slices is additive componentwise.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance sequenceToStrictSystemAdditive : (sequenceToStrictSystemFunctor B).Additive where
  map_add := by
    intro M N f g
    apply strictRingSystem_hom_ext B
    intro n
    exact ((systemSequenceEvaluation B n).map_add (f := f) (g := g)).trans
      ((systemEvaluation B n).map_add
        (f := (sequenceToStrictSystemFunctor B).map f)
        (g := (sequenceToStrictSystemFunctor B).map g)).symm

/-- Vertical module evaluation is exact.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance systemSequenceEvaluationLimits : PreservesFiniteLimits (systemSequenceEvaluation B n) := by
  change PreservesFiniteLimits
    ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n)
  infer_instance

/-- Vertical module evaluation preserves finite colimits.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
instance systemSequenceEvaluationColimits :
    PreservesFiniteColimits (systemSequenceEvaluation B n) := by
  change PreservesFiniteColimits
    ((strictSystemSequenceEquivalence B).inverse ⋙ systemEvaluation B n)
  infer_instance

/-- Vertical restriction is the algebraic inverse image of the evaluation morphism of topoi.
Source: Zheng 4.1; Stacks 00XO and 03D2
(blueprint: lem-pur-system-evaluation-topos).
All operations are unchanged on sections; the ring identification removes the identity
coefficient transition using functoriality. -/
def systemSequenceEvaluationInverseImage : AlgebraicInverseImage
    ((Prod.sectR n C).sheafPushforwardContinuous (Type w) J
      (coefficientSequenceTopology J)) (systemSequenceRing B) (B.obj (op n)) where
  ringUnderlying := ObjectProperty.isoMk _ (NatIso.ofComponents (fun V ↦ Iso.refl _) (by
    intro U V f
    ext x
    change (B.obj (op n)).obj.map f ((B.map (𝟙 (op n))).hom.app U x) =
      (B.obj (op n)).obj.map f x
    rw [B.map_id]
    rfl))
  ringAdd := by intro T a b t h V x; exact h (op (n, V.unop)) x
  ringMul := by intro T a b t h V x; exact h (op (n, V.unop)) x
  ringZero := by intro T a h V x; exact h (op (n, V.unop)) x
  ringOne := by intro T a h V x; exact h (op (n, V.unop)) x
  modules := systemSequenceEvaluation B n
  moduleUnderlying := NatIso.ofComponents (fun M ↦ Iso.refl _) (by intros; rfl)
  moduleAdd := by intro M T a b t h V x; exact h (op (n, V.unop)) x
  moduleZero := by intro M T a h V x; exact h (op (n, V.unop)) x
  moduleSMul := by intro M T a b t h V x; exact h (op (n, V.unop)) x
/-- Evaluation is the inverse image of a geometric morphism.
Source: Zheng 4.1 (blueprint: lem-pur-system-evaluation-topos). -/
def systemSequenceEvaluationToposAdjunction :
    (Prod.sectR n C).sheafPushforwardContinuous (Type w) J (coefficientSequenceTopology J) ⊣
      (Prod.sectR n C).sheafPushforwardCocontinuous (Type w) J
        (coefficientSequenceTopology J) :=
  (Prod.sectR n C).sheafAdjunctionCocontinuous (Type w) J (coefficientSequenceTopology J)

end SheafOfModules

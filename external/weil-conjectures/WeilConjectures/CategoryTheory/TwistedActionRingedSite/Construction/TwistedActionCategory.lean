/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.SixFunctors.IntegerActionSliceEquivalence
public import Mathlib.CategoryTheory.InducedCategory

/-! # The category of integer-labelled arrows of an autoequivalence

Source: the first step of the agent-formulated twisted variant of Stacks 00W0.
Coherence is supplied by the source library's integer tensor powers, applied to
endofunctors, rather than by an additional coherence assumption.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite
namespace Construction

variable {C : Type u} [SmallCategory C] (s : C ≌ C)

attribute [local instance] endofunctorMonoidalCategory

/-- The two functors of the equivalence are tensor inverses for composition.
Source: the unit and counit of an equivalence
(blueprint: lem-sf-twisted-action-category). -/
def functorInverse : TensorInverse s.functor where
  obj := s.inverse
  rightIso := s.unitIso.symm
  leftIso := s.counitIso

/-- Natural powers have the tensor-power functors.
Source: the recursive definitions (blueprint: lem-sf-twisted-action-category). -/
theorem powNat_functor (e : C ≌ C) (n : ℕ) :
    (e.powNat n).functor = tensorPowNat e.functor n := by
  cases n with
  | zero => rfl
  | succ n =>
    induction n with
    | zero => rfl
    | succ n ih =>
      exact congrArg (fun F : C ⥤ C ↦ e.functor ⋙ F) ih

/-- Integer powers have the tensor-power functors.
Source: the recursive definitions (blueprint: lem-sf-twisted-action-category). -/
theorem pow_functor (n : ℤ) : (s ^ n).functor = (functorInverse s).zpow n := by
  cases n with
  | ofNat n => exact powNat_functor s n
  | negSucc n => exact powNat_functor s.symm (n + 1)

/-- Coherent powers on the exact functors used by the Site interface.
Source: the source library's `TensorInverse.intTensorFamily`
(blueprint: lem-sf-twisted-action-category). -/
noncomputable def powers : IntTensorFamily (C ⥤ C) :=
  (functorInverse s).intTensorFamily.copy (fun n ↦ (s ^ n).functor)
    (funext (pow_functor s))

/-- These powers define an integer shift, with no global shift instance on C.
Source: coherent integer tensor families
(blueprint: lem-sf-twisted-action-category). -/
@[instance_reducible] noncomputable def shift : HasShift C ℤ where
  shift := (powers s).toFunctor
  shiftMonoidal := (powers s).coreMonoidal.toMonoidal

/-- The zero comparison is the identity on the specified degree-zero functor.
Source: normalization of the transported integer family
(blueprint: lem-sf-twisted-action-category). -/
theorem shift_zero :
    letI := shift s
    shiftFunctorZero C ℤ = Iso.refl (𝟭 C) := by
  let := shift s
  apply Iso.ext
  change (powers s).zeroIso.hom = 𝟙 _
  simp [powers, IntTensorFamily.copy, TensorInverse.intTensorFamily]

/-- The multiplication comparison in the order used for labelled arrows.
Source: composition of shifted morphisms
(blueprint: lem-sf-twisted-action-category). -/
noncomputable def powerComp (n m : ℤ) :
    (s ^ m).functor ⋙ (s ^ n).functor ≅ (s ^ (n + m)).functor :=
  letI := shift s
  (shiftFunctorAdd' C m n (n + m) (add_comm m n)).symm

/-- The existing integer action category, transported to the specified object copy.
Source: `integerActionCategory` and Mathlib's induced-category construction
(blueprint: lem-sf-twisted-action-category). -/
@[instance_reducible] noncomputable def category : SmallCategory (Object C) :=
  letI := shift s
  inferInstanceAs (SmallCategory (InducedCategory (IntegerActionSite C)
    (fun X : Object C ↦ IntegerActionSite.mk X.base)))

/-- The degree-zero inclusion, using the same copied objects.
Source: step 1 of the twisted-site construction
(blueprint: lem-sf-twisted-action-category). -/
noncomputable def inclusion : letI := category s; C ⥤ Object C := by
  let := shift s
  let := category s
  exact {
    obj X := ⟨X⟩
    map f := InducedCategory.homMk ((integerActionInclusion (C := C)).map f)
    map_id X := rfl
    map_comp f g := by
      apply InducedCategory.hom_ext
      exact (integerActionInclusion (C := C)).map_comp f g }

/-- No quotient of the integer-labelled arrow type is taken.
Source: step 1 of the twisted-site construction
(blueprint: lem-sf-twisted-action-category). -/
noncomputable def arrows (X Y : C) :
    letI := category s
    ((inclusion s).obj X ⟶ (inclusion s).obj Y) ≃
      Σ n : ℤ, X ⟶ (s ^ n).functor.obj Y :=
  letI := shift s
  InducedCategory.homEquiv

/-- The specified identities really are the degree-zero identities.
Source: the normalized zero comparison
(blueprint: lem-sf-twisted-action-category). -/
theorem arrows_id (X : C) :
    letI := category s
    arrows s X X (𝟙 _) = ⟨0, 𝟙 X⟩ := by
  let := shift s
  let := category s
  change (⟨0, 𝟙 X ≫ (shiftFunctorZero' C (0 : ℤ) rfl).inv.app X⟩ :
    Σ n : ℤ, X ⟶ (s ^ n).functor.obj X) = _
  simp [shiftFunctorZero', shift_zero]

/-- Inclusion keeps every degree-zero arrow verbatim.
Source: the normalized zero comparison
(blueprint: lem-sf-twisted-action-category). -/
theorem arrows_inclusion {X Y : C} (f : X ⟶ Y) :
    letI := category s
    arrows s X Y ((inclusion s).map f) = ⟨0, f⟩ := by
  let := shift s
  let := category s
  change (⟨0, f ≫ (shiftFunctorZero' C (0 : ℤ) rfl).inv.app Y⟩ :
    Σ n : ℤ, X ⟶ (s ^ n).functor.obj Y) = _
  simp [shiftFunctorZero', shift_zero]

/-- Composition is precisely the normalization required by Site.
Source: Mathlib's composition of shifted morphisms
(blueprint: lem-sf-twisted-action-category). -/
theorem arrows_comp (X Y Z : C) (n m : ℤ)
    (f : X ⟶ (s ^ n).functor.obj Y) (g : Y ⟶ (s ^ m).functor.obj Z) :
    letI := category s
    arrows s X Z ((arrows s X Y).symm ⟨n, f⟩ ≫ (arrows s Y Z).symm ⟨m, g⟩) =
      ⟨n + m, f ≫ (s ^ n).functor.map g ≫ (powerComp s n m).hom.app Z⟩ := rfl

end Construction
end CategoryTheory.TwistedActionRingedSite

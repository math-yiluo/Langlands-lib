/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Thick isomorphism loci of exact contravariant transformations

Source: Stacks Project, Tags 0144 and 08JC; the categorical last two steps of
lem-sf-site-hom-comparison-thick.
-/

@[expose] public section
set_option autoImplicit false
open scoped ZeroObject

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace CategoryTheory

variable {C D : Type*} [Category C] [Category D]
  [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
  {B E : Cᵒᵖ ⥤ D} [B.CommShift ℤ] [E.CommShift ℤ]
  [B.IsTriangulated] [E.IsTriangulated]
  (β : B ⟶ E) [NatTrans.CommShift β ℤ]

/-- The components of an exact contravariant transformation have a thick isomorphism locus.
Source: Stacks 0144 and 08JC (blueprint: lem-sf-contravariant-comparison-iso-locus).

Proof: the component at zero is an isomorphism between zero objects. Naturality along
isomorphisms and the shift square transport invertibility. Apply the triangle morphism
induced by beta to the reversed distinguished triangle and use two-of-three on its
first and third components to obtain closure under extensions. For a retract, naturality
makes the smaller component a retract in the arrow category of the larger component;
isomorphisms are stable under retracts. -/
theorem contravariantComparison_isoLocus :
    let P : ObjectProperty C := fun K ↦ IsIso (β.app (op K))
    P.IsTriangulated ∧ P.IsStableUnderRetracts := by
  let P : ObjectProperty C := fun K ↦ IsIso (β.app (op K))
  have hret : P.IsStableUnderRetracts := ⟨fun h hK ↦
    MorphismProperty.of_retract (P := MorphismProperty.isomorphisms D)
      (β.retractArrowApp h.op) hK⟩
  let := hret
  have hzero : P.ContainsZero := ⟨0, isZero_zero C,
    (B.map_isZero (isZero_zero C).op).isIso
      (E.map_isZero (isZero_zero C).op) (β.app (op 0))⟩
  let := hzero
  have hshift : P.IsStableUnderShift ℤ := by
    constructor
    intro n
    constructor
    intro K hK
    have : IsIso (β.app (op K)) := hK
    have h : IsIso (β.app ((op K)⟦-n⟧)) := by
      rw [NatTrans.app_shift β (-n) (op K)]
      infer_instance
    change IsIso (β.app (op (K⟦n⟧)))
    exact (NatTrans.isIso_app_iff_of_iso β
      ((shiftFunctorOpIso C (-n) n (neg_add_cancel n)).app (op K))).mp h
  let := hshift
  have hext : P.IsTriangulatedClosed₂ := .mk' (fun T hT h₁ h₃ ↦ by
    have hTo := op_distinguished T hT
    exact NatTrans.isIso_app_obj₂_of_isIso_app_obj₁₃ β hTo h₃ h₁)
  let := hext
  exact ⟨{}, hret⟩

end CategoryTheory

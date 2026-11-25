/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Ring.Int.Defs

/-! # Shifting universal units
(blueprint: lem-sp-universal-unit-shift).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe uC uB vC vB
open CategoryTheory
namespace CategoryTheory.Functor
variable {C : Type uC} {B : Type uB} [Category.{vC} C] [Category.{vB} B]
  [HasShift C ℤ] [HasShift B ℤ] (U : C ⥤ B) [U.CommShift ℤ]
/-- Let U:C→D commute with integer shifts. If p:F→U(H) induces bijections Hom(H,K)→Hom(F,U(K)) for
every K, then for every integer n its shifted map p[n] followed by the inverse commutation with
shift induces bijections Hom(H[n],K)→Hom(F[n],U(K)) [def-weil-abstract-derived-category].
Source: blueprint Cartier derived reduction and comparison paragraphs; Stacks 0152,
06YY and 0GLZ (blueprint: lem-sp-universal-unit-shift).
Proof: First test on shifted objects K[n]. The shift functors are fully faithful, so the original
Hom bijection transfers to these tests; commutation with shift gives the specified formula. Every
object is isomorphic to a shifted object by shifting back and forward. Naturality transports the
bijection to an arbitrary test object. -/
theorem universal_unit_shift {F : B} {H : C} (p : F ⟶ U.obj H)
    (h : ∀ K : C, Function.Bijective (fun f : H ⟶ K ↦ p ≫ U.map f)) (n : ℤ) :
    ∀ K : C, Function.Bijective (fun f : H⟦n⟧ ⟶ K ↦
      p⟦n⟧' ≫ (U.commShiftIso n).inv.app H ≫ U.map f) := by
  have hshift (L : C) : Function.Bijective (fun f : H⟦n⟧ ⟶ L⟦n⟧ ↦
      p⟦n⟧' ≫ (U.commShiftIso n).inv.app H ≫ U.map f) := by
    let hC := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor C n)).homEquiv
      (X := H) (Y := L)
    let hB := (Functor.FullyFaithful.ofFullyFaithful (shiftFunctor B n)).homEquiv
      (X := F) (Y := U.obj L)
    have hb := ((U.commShiftIso n).symm.app L).homToEquiv.bijective.comp
      (hB.bijective.comp (h L))
    apply (Function.Bijective.of_comp_iff _ hC.bijective).mp
    simp only [hC, hB, Function.comp_def, Functor.FullyFaithful.homEquiv_apply,
      Iso.homToEquiv_apply, Iso.app_hom, Iso.symm_hom, Functor.map_comp,
      Category.assoc] at hb ⊢
    simpa only [U.commShiftIso_inv_naturality] using hb
  intro K
  let L := (shiftEquiv C n).inverse.obj K
  let e : L⟦n⟧ ≅ K := (shiftEquiv C n).counitIso.app K
  have hb := (U.mapIso e).homToEquiv.bijective.comp
    ((hshift L).comp e.symm.homToEquiv.bijective)
  simp only [Function.comp_def, Iso.homToEquiv_apply, Iso.symm_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc] at hb
  simpa only [← U.map_comp, Iso.inv_hom_id, U.map_id, Category.comp_id] using hb
end CategoryTheory.Functor

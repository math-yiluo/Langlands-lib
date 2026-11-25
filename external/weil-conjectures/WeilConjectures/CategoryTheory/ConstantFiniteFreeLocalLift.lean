/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.FiniteTypeLocallyConstantModuleSheaf
import WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import WeilConjectures.CategoryTheory.FiniteTypeRestrictionExact

/-!
# Local lifting of morphisms from constant finite free module sheaves

Source: Stacks Project, Modules on Sites, Tag 093U (3), finite-generator lifting step.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
universe u
open CategoryTheory Opposite CategoryTheory.Limits
attribute [local instance] Abelian.hasFiniteBiproducts
namespace SheafOfModules
variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
 {B : Type u} [CommRing B]

private def sectionOnSlice {R : Sheaf J RingCat.{u}} (F : SheafOfModules.{u} R)
    (U : C) (t : F.val.obj (op U)) : (F.over U).sections :=
  PresheafOfModules.sectionsMk (fun W ↦ F.val.map W.unop.hom.op t) (by
    intro W Z f
    change F.val.map f.unop.left.op (F.val.map W.unop.hom.op t) =
      F.val.map Z.unop.hom.op t
    rw [← PresheafOfModules.map_comp_apply]
    apply F.val.congr_map_apply
    rw [← op_comp, Over.w])

private theorem unitSection_at_identity {R : Sheaf J RingCat.{u}} (F : SheafOfModules.{u} R)
    (U : C) (t : F.val.obj (op U)) :
    ((F.over U).unitHomEquiv.symm (sectionOnSlice F U t)).val.app
      (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) = t := by
  change ((F.over U).unitHomEquiv
    ((F.over U).unitHomEquiv.symm (sectionOnSlice F U t))).val
      (op (Over.mk (𝟙 U))) = t
  rw [Equiv.apply_symm_apply]
  change F.val.map (𝟙 U).op t = t
  simp only [op_id, PresheafOfModules.map_id]
  rfl

private theorem unitOverHom_ext {R : Sheaf J RingCat.{u}}
    (G : SheafOfModules.{u} R) (U : C)
    (a b : (unit R).over U ⟶ G.over U)
    (h : a.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U)) =
      b.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) : a = b := by
  apply (G.over U).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro W
  change a.val.app W (1 : R.obj.obj (op W.unop.left)) =
    b.val.app W (1 : R.obj.obj (op W.unop.left))
  have ha := PresheafOfModules.naturality_apply a.val
    (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op (1 : R.obj.obj (op U))
  have hb := PresheafOfModules.naturality_apply b.val
    (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op (1 : R.obj.obj (op U))
  change a.val.app W (R.obj.map W.unop.hom.op (1 : R.obj.obj (op U))) =
    G.val.map W.unop.hom.op (a.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) at ha
  change b.val.app W (R.obj.map W.unop.hom.op (1 : R.obj.obj (op U))) =
    G.val.map W.unop.hom.op (b.val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))) at hb
  rw [map_one] at ha hb
  exact ha.trans ((congrArg (G.val.map W.unop.hom.op) h).trans hb.symm)

private theorem biproduct_lift_local {R : Sheaf J RingCat.{u}}
    (F G : SheafOfModules.{u} R) (p : F ⟶ G) [Epi p] (n : ℕ) (U : C)
    (a : (⨁ fun _ : Fin n ↦ unit R).over U ⟶ G.over U) :
    ∃ S ∈ J U, ∀ (V : C) (f : V ⟶ U), S f →
      ∃ l : (⨁ fun _ : Fin n ↦ unit R).over V ⟶ F.over V,
        l ≫ p.over V =
          (overFunctorMap _ f).inv.app _ ≫ (overMap _ f).map a ≫
            (overFunctorMap _ f).hom.app G := by
  classical
  let T : Fin n → SheafOfModules.{u} R := fun _ ↦ unit R
  let b (i : Fin n) := (biproduct.ι T i).over U ≫ a
  let s (i : Fin n) := (b i).val.app (op (Over.mk (𝟙 U))) (1 : R.obj.obj (op U))
  obtain ⟨S, hS, h⟩ := exists_cover_lift_finite_sections p U s
  refine ⟨S, hS, ?_⟩
  intro V f hf
  choose t ht using h V f hf
  have : PreservesFiniteColimits (overFunctor.{u} R V) := (overFunctor_exact R V).2
  let hc := isColimitOfPreserves (overFunctor.{u} R V) (biproduct.isColimit T)
  let c : Cocone (Discrete.functor T ⋙ overFunctor.{u} R V) :=
    { pt := F.over V
      ι := Discrete.natTrans (fun i ↦
        (F.over V).unitHomEquiv.symm (sectionOnSlice F V (t i.as))) }
  refine ⟨hc.desc c, ?_⟩
  apply hc.hom_ext
  intro j
  let i : Fin n := j.as
  rw [← Category.assoc, hc.fac c j]
  apply unitOverHom_ext G V
  change p.val.app (op V)
    (((F.over V).unitHomEquiv.symm (sectionOnSlice F V (t i))).val.app
      (op (Over.mk (𝟙 V))) (1 : R.obj.obj (op V))) =
    a.val.app (op (Over.mk (𝟙 V ≫ f)))
      ((biproduct.ι T i).val.app (op V) (1 : R.obj.obj (op V)))
  rw [unitSection_at_identity, ht i]
  have hn := PresheafOfModules.naturality_apply (b i).val
    (Over.homMk (𝟙 V ≫ f) : Over.mk (𝟙 V ≫ f) ⟶ Over.mk (𝟙 U)).op
      (1 : R.obj.obj (op U))
  change a.val.app (op (Over.mk (𝟙 V ≫ f)))
      ((biproduct.ι T i).val.app (op V)
        (R.obj.map (𝟙 V ≫ f).op (1 : R.obj.obj (op U)))) =
    G.val.map (𝟙 V ≫ f).op (s i) at hn
  rw [map_one] at hn
  exact (G.val.congr_map_apply
    (congrArg Quiver.Hom.op (Category.id_comp f)) (s i)).symm.trans hn.symm

/-- A morphism from a constant finite free module sheaf lifts locally through an epi.
Source: Stacks Project, Modules on Sites, Tag 093U (3), extension paragraph.
(auxiliary; not a blueprint node).

Proof: First treat the finite biproduct of copies of the rank-one free sheaf. A morphism
from each summand is determined by its value at one on the terminal object of the slice.
Lift these finitely many sections on one covering sieve. On each member, the lifts define
maps from the rank-one summands. Restriction preserves the finite coproduct, so they
assemble to the desired morphism. Naturality and determination by one verify its
composite with the epi. Finally the canonical finite-free comparison identifies the
constant finite free sheaf with the finite biproduct. This includes rank zero. -/
theorem exists_cover_lift_constant_finite_free
    (F G : ringedSiteModules.{u}
      ((constantSheaf J RingCat.{u}).obj (RingCat.of B)))
    (p : F ⟶ G) [Epi p] (n : ℕ) (U : C)
    (a : ((strictPerfectConstantSheaf J B).obj
      (ModuleCat.of B (Fin n → B))).over U ⟶ G.over U) :
    ∃ S ∈ J U, ∀ (V : C) (f : V ⟶ U), S f →
      ∃ l : ((strictPerfectConstantSheaf J B).obj
        (ModuleCat.of B (Fin n → B))).over V ⟶ F.over V,
        l ≫ p.over V =
          (overFunctorMap _ f).inv.app _ ≫ (overMap _ f).map a ≫
            (overFunctorMap _ f).hom.app G := by
  let R := (constantSheaf J RingCat.{u}).obj (RingCat.of B)
  let T : Fin n → SheafOfModules.{u} R := fun _ ↦ unit R
  let e := asIso (strictPerfectConstantFiniteFreeComparison J B n) ≪≫
    (biproduct.isoProduct T).symm
  obtain ⟨S, hS, h⟩ := biproduct_lift_local F G p n U (e.inv.over U ≫ a)
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, hl⟩ := h V f hf
  refine ⟨e.hom.over V ≫ l, ?_⟩
  rw [Category.assoc, hl]
  ext W x
  change a.val.app ((Over.map f).op.obj W)
      (e.inv.val.app (op W.unop.left) (e.hom.val.app (op W.unop.left) x)) =
    a.val.app ((Over.map f).op.obj W) x
  have he := ConcreteCategory.congr_hom
    (congrArg (fun k ↦ k.val.app (op W.unop.left)) e.hom_inv_id) x
  change e.inv.val.app (op W.unop.left) (e.hom.val.app (op W.unop.left) x) = x at he
  rw [he]

end SheafOfModules

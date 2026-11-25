/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClassModels
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.LerayDegenerateSections

import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareLocalClasses
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LerayEdgeRestrictedResolution
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import WeilConjectures.AlgebraicGeometry.RestrictedResolutionSectionsExist
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap

/-! # The global cocycle square for an ordinary coefficient map

## References

* Stacks Project, Tag 0096
* Stacks Project, Tag 01F2
* Stacks Project, Tags 01FB and 08HY
* Stacks Project, Tag 01E4, and Tag 01FB
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
noncomputable section
attribute [local instance_reducible] TopCat.Sheaf
set_option allowUnsafeReducibility true in
attribute [local reducible] AlgebraicGeometry.Scheme.Modules
  AlgebraicGeometry.Scheme.Modules.Hom AlgebraicGeometry.Scheme.Modules.instCategory
  AlgebraicGeometry.Scheme.Modules.instAbelian
attribute [local instance 2000] SheafOfModules.instCategory SheafOfModules.instPreadditive
  SheafOfModules.instAbelian
private theorem square_pasting {C : Type*} [Category C]
    {A B D E F G : C} (r : A ⟶ B) (c : B ⟶ D) (b : D ⟶ G)
    (v : B ⟶ F) (t : E ⟶ F) (d : F ⟶ G) (m : A ⟶ E)
    (ef : A ⟶ D) (eq : E ⟶ G)
    (hf : r ≫ c = ef) (hb : c ≫ b = v ≫ d)
    (hr : r ≫ v = m ≫ t) (hq : t ≫ d = eq) : ef ≫ b = m ≫ eq := by
  calc
    _ = (r ≫ c) ≫ b := congrArg (fun z ↦ z ≫ b) hf.symm
    _ = r ≫ (v ≫ d) := by rw [Category.assoc, hb]
    _ = (m ≫ t) ≫ d := by rw [← Category.assoc, hr]
    _ = m ≫ eq := by rw [Category.assoc, hq]

private theorem naturality_cancel {C : Type*} [Category C]
    {A B D E : C} (r : A ⟶ B) (t : B ⟶ A) (a : A ⟶ D)
    (b : B ⟶ E) (p : E ⟶ D) (hn : t ≫ a = b ≫ p) (hi : r ≫ t = 𝟙 A) :
    r ≫ b ≫ p = a := by
  rw [← hn, ← Category.assoc, hi, Category.id_comp]

private theorem insert_iso_inverse {C : Type*} [Category C] {A B D : C}
    (f : A ⟶ D) (e : B ≅ D) : f = f ≫ e.inv ≫ e.hom := by
  rw [e.inv_hom_id, Category.comp_id]

private theorem group_eval_eq {A B C D E F : AddCommGrpCat.{u}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ F) (d : A ⟶ D) (e : D ⟶ E)
    (k : E ⟶ F) (x : A) (h : (b ≫ c) (a x) = (d ≫ e ≫ k) x) :
    c (b (a x)) = k (e (d x)) := h

private theorem group_iso_apply {A B : AddCommGrpCat.{u}} (e : A ≅ B) (x : A) :
    e.inv (e.hom x) = x := ConcreteCategory.congr_hom e.hom_inv_id x

namespace AlgebraicGeometry

open Scheme.Modules
attribute [local instance] Scheme.Modules.enoughInjectives

/-- The native abelian structure, cached once for the shared Leray constructions. -/
@[reducible] local instance (priority := 3000) globalLerayModuleAbelian (S : Scheme.{u}) :
    Abelian (SheafOfModules.{u} (moduleRings S.toRingedSpace)) := inferInstance

private theorem restrictedMap_cohomology {Y X : Scheme.{u}} (p : Y ⟶ X)
    (F : X.Modules) (M : Y.Modules) (φ : F ⟶ (pushforward p).obj M)
    (U : X.Opens) (n : ℕ) :
    moduleCohomologyRestriction U F n ≫
      moduleCohomologyFMap (p.resLE U (p ⁻¹ᵁ U) le_rfl)
        (restrictedDirectImageMap p φ U) n =
      moduleCohomologyFMap p φ n ≫ moduleCohomologyRestriction (p ⁻¹ᵁ U) M n := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  obtain ⟨ψ, hψ, hc⟩ := moduleCohomologyFMap_restriction p φ U
  have heq : ψ = restrictedDirectImageMap p φ U := by
    apply ((restrictAdjunction U.ι).homEquiv _ _).injective
    unfold restrictedDirectImageMap
    rw [Equiv.apply_symm_apply]
    let B := (restrictFunctor (p ⁻¹ᵁ U).ι).obj M
    let c := (pushforwardComp (p.resLE U (p ⁻¹ᵁ U) le_rfl) U.ι ≪≫
      pushforwardCongr (p.resLE_comp_ι le_rfl)).hom.app B
    apply (cancel_mono c).1
    rw [Adjunction.homEquiv_unit]
    have hh : (restrictAdjunction U.ι).unit.app F ≫ (pushforward U.ι).map ψ ≫ c =
        φ ≫ (pushforward p).map ((restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app M) ≫
          (pushforwardComp (p ⁻¹ᵁ U).ι p).hom.app B := by
      simpa only [c, Iso.trans_hom, NatTrans.comp_app, Category.assoc] using hψ
    simp only [Category.assoc]
    rw [hh]
    let i := pushforwardComp (p.resLE U (p ⁻¹ᵁ U) le_rfl) U.ι ≪≫
      pushforwardCongr (p.resLE_comp_ι le_rfl)
    simpa only [i, c, B, Iso.app_hom, Iso.app_inv, Category.assoc] using insert_iso_inverse
      (φ ≫ (pushforward p).map ((restrictAdjunction (p ⁻¹ᵁ U).ι).unit.app M) ≫
        (pushforwardComp (p ⁻¹ᵁ U).ι p).hom.app B) (i.app B)
  rw [heq] at hc
  exact (hc n).symm

private theorem section_top_naturality {S T : Scheme.{u}} (g : T ⟶ S)
    (N P : T.Modules) (b : N ⟶ P) :
    N.val.presheaf.map (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op ≫
      Hom.app b (g ⁻¹ᵁ (⊤ : S.Opens)) ≫
      P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top g.base).symm) :
        op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens)) =
        Hom.app b ⊤ := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let r := (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op
  let t : op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens) :=
    eqToHom (congrArg op (Opens.map_top g.base).symm)
  have hn := ((PresheafOfModules.toPresheaf _).map b.val).naturality t
  change N.val.presheaf.map t ≫ Hom.app b ⊤ =
    Hom.app b (g ⁻¹ᵁ (⊤ : S.Opens)) ≫ P.val.presheaf.map t at hn
  change N.val.presheaf.map r ≫ Hom.app b _ ≫ P.val.presheaf.map t = _
  have ht : r ≫ t = 𝟙 (op (⊤ : T.Opens)) := Subsingleton.elim _ _
  have hi := (N.val.presheaf.map_comp r t).symm.trans
    ((congrArg N.val.presheaf.map ht).trans (N.val.presheaf.map_id (op ⊤)))
  exact naturality_cancel _ _ _ _ _ hn hi

private theorem section_top_naturality_apply {S T : Scheme.{u}} (g : T ⟶ S)
    (N P : T.Modules) (b : N ⟶ P)
    (y : (RingedSpace.globalSectionsFunctor T.toRingedSpace).obj N) :
    P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top g.base).symm) :
        op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens))
      ((RingedSpace.openModuleSections T.toRingedSpace (g ⁻¹ᵁ (⊤ : S.Opens))).map b
        (N.val.presheaf.map
          (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op y)) =
      (RingedSpace.globalSectionsFunctor T.toRingedSpace).map b y := by
  have h := ConcreteCategory.congr_hom (section_top_naturality g N P b) y
  convert h using 1
  rfl

private theorem section_map {S : Scheme.{u}} (N P : S.Modules)
    (b : N ⟶ P) (U : S.Opens) :
    Hom.app b U = (RingedSpace.openModuleSections S.toRingedSpace U).map b := by
  with_unfolding_all rfl

private theorem pushforward_sections_map {S T : Scheme.{u}} (g : T ⟶ S)
    (N P : T.Modules) (b : N ⟶ P) (U : S.Opens) :
    (RingedSpace.openModuleSections S.toRingedSpace U).map ((pushforward g).map b) =
      (RingedSpace.openModuleSections T.toRingedSpace (g ⁻¹ᵁ U)).map b := by
  with_unfolding_all rfl

private theorem section_composite_apply {S T : Scheme.{u}} (g : T ⟶ S)
    (N N' : S.Modules) (P : T.Modules) (i : N ⟶ N')
    (m : N' ⟶ (pushforward g).obj P)
    (x : (RingedSpace.globalSectionsFunctor S.toRingedSpace).obj N) :
    (RingedSpace.openModuleSections S.toRingedSpace ⊤).map (i ≫ m) x =
      Hom.app m ⊤ ((RingedSpace.globalSectionsFunctor S.toRingedSpace).map i x) := by
  with_unfolding_all rfl

private theorem section_iso_square_evaluate {S T : Scheme.{u}} (g : T ⟶ S)
    (N N' : S.Modules) (P B : T.Modules) (A D : AddCommGrpCat.{u})
    (a : A ⟶ (forget₂ _ AddCommGrpCat).obj
      ((RingedSpace.globalSectionsFunctor S.toRingedSpace).obj N))
    (c : D ⟶ (forget₂ _ AddCommGrpCat).obj
      ((RingedSpace.globalSectionsFunctor T.toRingedSpace).obj B))
    (v : A ⟶ D) (i : N ⟶ N') (m : N' ⟶ (pushforward g).obj P) (j : P ≅ B)
    (hs : a ≫ Hom.app (i ≫ m ≫ (pushforward g).map j.hom) ⊤ =
      v ≫ c ≫ B.val.presheaf.map
        (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op)
    (x : A) :
    (RingedSpace.globalSectionsFunctor T.toRingedSpace).map j.inv (c (v x)) =
      P.val.presheaf.map (eqToHom (congrArg op (Opens.map_top g.base).symm) :
          op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens))
        (Hom.app m ⊤ ((RingedSpace.globalSectionsFunctor S.toRingedSpace).map i (a x))) := by
  let ES := RingedSpace.openModuleSections S.toRingedSpace ⊤
  let ET := RingedSpace.openModuleSections T.toRingedSpace (g ⁻¹ᵁ (⊤ : S.Opens))
  let b := i ≫ m ≫ (pushforward g).map j.hom
  let b' := i ≫ m
  have hbmap : Hom.app b ⊤ = ES.map b' ≫ ET.map j.hom := by
    have h₀ : Hom.app b ⊤ = ES.map b := section_map _ _ b ⊤
    have h₁ : ES.map b = ES.map b' ≫ ES.map ((pushforward g).map j.hom) := by
      have h := ES.map_comp b' ((pushforward g).map j.hom)
      simpa only [b, b', Category.assoc] using h
    have h₂ := congrArg (fun z ↦ ES.map b' ≫ z)
      (pushforward_sections_map g _ _ j.hom ⊤)
    exact h₀.trans (h₁.trans h₂)
  let z := ES.map b' (a x)
  let y := c (v x)
  let r := B.val.presheaf.map
    (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op
  let t := P.val.presheaf.map
    (eqToHom (congrArg op (Opens.map_top g.base).symm) :
      op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens))
  have hs₀ := (congrArg (fun h ↦ h (a x)) hbmap).symm.trans
    (ConcreteCategory.congr_hom hs x)
  have hs' : ET.map j.hom z = r y := group_eval_eq a (ES.map b')
    (ET.map j.hom) v c r x hs₀
  have hi : ET.map j.inv (ET.map j.hom z) = z := group_iso_apply (ET.mapIso j) z
  have hn : t (ET.map j.inv (r y)) =
      (RingedSpace.globalSectionsFunctor T.toRingedSpace).map j.inv y :=
    section_top_naturality_apply g B P j.inv y
  have hp := (congrArg t hi.symm).trans
    ((congrArg (fun a ↦ t (ET.map j.inv a)) hs').trans hn)
  have hc := section_composite_apply g N N' P i m (a x)
  exact hp.symm.trans (congrArg t hc)

attribute [local irreducible] moduleCohomologyFMap moduleCohomologyRestriction
  restrictedDirectImageMap resolutionSectionClass schemeSingleCohomologyComparison
  derivedSquareUnitMap RingedSpace.topEdgeLocalClass RingedSpace.topEdgeLocalLeray
  RingedSpace.topEdgeInverseLocalClass

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The common derived image of a module, kept as a shared object in the global square. -/
def globalLerayImage {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) :
    schemeDerivedCategory.{u, w} S :=
  (schemeDerivedDirectImage f).obj ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj F)

/-- The ordinary coefficient unit map with its shared image objects fixed in the type. -/
def globalLerayUnitMap {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (φ : F ⟶ (pushforward p).obj M) :
    globalLerayImage.{u, w} f F ⟶ (schemeDerivedDirectImage g).obj
      (globalLerayImage.{u, w} q M) := by
  with_unfolding_all exact derivedSquareUnitMap f q g p hs F M φ

section
set_option allowUnsafeReducibility true in
attribute [local reducible] globalLerayImage globalLerayUnitMap

/-- The canonical total/classical comparison with native module categories and the
supplied derived-category family fixed in its type. -/
def globalLerayComparison {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (n : ℕ) :
    (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)).obj
        (globalLerayImage.{u, w} f F) ≅
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived n).obj F := by
  with_unfolding_all exact schemeSingleCohomologyComparison.{u, w} f F n

attribute [local irreducible] globalLerayComparison

/-- Specialization of the local cocycle square to the whole open, expressed using
classical Leray edges and their canonical total-derived comparisons. The coefficient
is an arbitrary ordinary h-map. There is no derived pullback or cohomological bound.
-/
theorem globalLeray_unitSquare
    {X S Y T : Scheme.{u}} (f : X ⟶ S) (q : Y ⟶ T) (g : T ⟶ S) (p : Y ⟶ X)
    (hs : p ≫ f = q ≫ g) (F : X.Modules) (M : Y.Modules)
    (φ : F ⟶ (Scheme.Modules.pushforward p).obj M) (n : ℕ)
    (e : (DerivedCategory.homologyFunctor.{w, u, u + 1}
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)).obj
        ((schemeDerivedDirectImage g).obj (globalLerayImage.{u, w} q M)) ⟶
      (Scheme.Modules.pushforward g).obj ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (n : ℤ)).obj
          (globalLerayImage.{u, w} q M)))
    (he : ∀ V : S.Opensᵒᵖ,
      (RingedSpace.topEdgeLocalClass S.toRingedSpace (n : ℤ)
        ((schemeDerivedDirectImage g).obj (globalLerayImage.{u, w} q M))).app V ≫
        ((SheafOfModules.toSheaf (moduleRings S.toRingedSpace)).map e).hom.app V =
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (n : ℤ)
        (globalLerayImage.{u, w} q M)).hom.app V ≫
      (RingedSpace.topEdgeInverseLocalClass g.toLRSHom.toShHom (n : ℤ)
        (globalLerayImage.{u, w} q M)).app V)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace n).obj F) :
    (RingedSpace.globalSectionsFunctor T.toRingedSpace).map
        (globalLerayComparison.{u, w} q M n).inv
          (((Classical.choose (exists_lerayEdge_isIso_of_vanishing q)) n).app M
            (Scheme.Modules.moduleCohomologyFMap p φ n x)) =
      (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings T.toRingedSpace)) (n : ℤ)).obj
          (globalLerayImage.{u, w} q M)).val.presheaf.map
        (eqToHom (congrArg op (Opens.map_top g.base).symm) :
        op (g ⁻¹ᵁ (⊤ : S.Opens)) ⟶ op (⊤ : T.Opens)))
          (Hom.app ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)).map
              (globalLerayUnitMap f q g p hs F M φ) ≫ e) ⊤
            ((RingedSpace.globalSectionsFunctor S.toRingedSpace).map
              (globalLerayComparison.{u, w} f F n).inv
                (((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F x))) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let I := injectiveResolution F
  let J := injectiveResolution M
  clear_value I J
  let U := f ⁻¹ᵁ (⊤ : S.Opens)
  let W := p ⁻¹ᵁ U
  let R := Classical.choice (restrictedResolutionSections_exists I U)
  let R' := Classical.choice (restrictedResolutionSections_exists J W)
  clear_value R R'
  have hW : W = q ⁻¹ᵁ (g ⁻¹ᵁ (⊤ : S.Opens)) := by
    dsimp only [W, U]
    rw [← Scheme.Hom.comp_preimage, hs, Scheme.Hom.comp_preimage]
  have hl := derivedSquareUnit_localClasses f q g p hs F M φ n e he ⊤ I J R R'
  have hf := lerayEdge_restrictedResolution f F I n ⊤ U rfl R
  have hq := lerayEdge_restrictedResolution q M J n (g ⁻¹ᵁ (⊤ : S.Opens)) W hW R'
  have hr := restrictedMap_cohomology p F M φ U n
  let B := ((RingedSpace.moduleDirectImage q.toLRSHom.toShHom).rightDerived n).obj M
  let b := (schemeSingleCohomologyComparison.{u, w} f F n).inv ≫
    (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)).map
        (derivedSquareUnitMap f q g p hs F M φ) ≫ e ≫
    (pushforward g).map (schemeSingleCohomologyComparison.{u, w} q M n).hom
  simp only [homOfLE_refl, op_id, CategoryTheory.Functor.map_id] at hf
  have hpaste :
      ((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F ≫
          Hom.app b ⊤ =
        moduleCohomologyFMap p φ n ≫
          ((Classical.choose (exists_lerayEdge_isIso_of_vanishing q)) n).app M ≫
          B.val.presheaf.map (homOfLE (show g ⁻¹ᵁ (⊤ : S.Opens) ≤ ⊤ from le_top)).op := by
    exact square_pasting _ _ _ _ _ _ _ _ _ hf hl hr hq
  have hv := section_iso_square_evaluate g _ _ _ _ _ _
    (((Classical.choose (exists_lerayEdge_isIso_of_vanishing f)) n).app F)
    (((Classical.choose (exists_lerayEdge_isIso_of_vanishing q)) n).app M)
    (moduleCohomologyFMap p φ n)
    (schemeSingleCohomologyComparison.{u, w} f F n).inv
    ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (n : ℤ)).map
        (derivedSquareUnitMap f q g p hs F M φ) ≫ e)
    (schemeSingleCohomologyComparison.{u, w} q M n) hpaste x
  with_unfolding_all exact hv

end

attribute [irreducible] globalLerayImage globalLerayUnitMap globalLerayComparison

end AlgebraicGeometry

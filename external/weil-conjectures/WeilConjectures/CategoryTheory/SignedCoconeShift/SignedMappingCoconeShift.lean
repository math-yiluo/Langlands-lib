/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
/-! # Coherent signed shifts of mapping cocones

Source: Stacks Project, Tags 011G and 014E.
(blueprint: lem-weil-signed-mapping-cocone-shift)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open CochainComplex CochainComplex.HomComplex
namespace CategoryTheory.SignedCoconeShift

universe a b
variable {A : Type a} [Category.{b} A] [Abelian A]
  {K L : CochainComplex A ℤ} (φ : K ⟶ L)
noncomputable def signedCoconeShiftIso (m : ℤ) :
    mappingCocone (φ⟦m⟧') ≅ (mappingCocone φ)⟦m⟧ :=
  m.negOnePow •
    ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).mapIso
        (mappingCone.shiftIso φ m).symm ≪≫
      (shiftFunctorComm (CochainComplex A ℤ) m (-1 : ℤ)).app (mappingCone φ))

@[reassoc]
lemma signedCoconeShiftIso_inl (m j : ℤ) :
    (mappingCocone.inl (φ⟦m⟧')).v j j (by omega) ≫
        ((signedCoconeShiftIso φ m).hom).f j =
      (mappingCocone.inl φ).v (j + m) (j + m) (by omega) ≫
        (shiftFunctorObjXIso (mappingCocone φ) m j (j + m) rfl).inv := by
  simp only [signedCoconeShiftIso, Preadditive.smul_iso_hom,
    HomologicalComplex.units_smul_f_apply, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  simp only [mappingCocone.inl, Cochain.rightShift_v (n := -1) _ _ _ _ j _ _
    (j + -1) (by omega), Cochain.rightShift_v (n := -1) _ _ _ _ (j + m) _ _
    (j + m + -1) (by omega)]
  simp only [mappingCone.shiftIso]
  simp only [shiftFunctor_map_f',
    Linear.comp_units_smul,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq,
    eqToIso.inv, eqToHom_refl, Category.comp_id]
  simp only [Iso.app_hom, shiftFunctorComm_hom_app_f,
    mappingCone.inl_v_desc_f_assoc, Cochain.units_smul_v,
    Cochain.shift_v', Linear.units_smul_comp, smul_smul,
    Int.units_mul_self, one_smul, HomologicalComplex.XIsoOfEq,
    eqToIso.hom]
  change (mappingCone.inl φ).v (j + m) (j + -1 + m) _ ≫
    ((mappingCone φ).XIsoOfEq (by omega : j + -1 + m = j + m + -1)).hom = _
  exact Cochain.v_comp_XIsoOfEq_hom _ _ _ _ _ _

@[reassoc]
lemma signedCoconeShiftIso_inr (m i j : ℤ) (h : i + 1 = j) :
    (mappingCocone.inr (φ⟦m⟧')).1.v i j h ≫
        ((signedCoconeShiftIso φ m).hom).f j =
      m.negOnePow • ((mappingCocone.inr φ).1.v (i + m) (j + m) (by omega) ≫
        (shiftFunctorObjXIso (mappingCocone φ) m j (j + m) rfl).inv) := by
  subst j
  simp only [signedCoconeShiftIso, Preadditive.smul_iso_hom,
    HomologicalComplex.units_smul_f_apply, Iso.trans_hom,
    Functor.mapIso_hom, Iso.symm_hom, HomologicalComplex.comp_f]
  simp only [mappingCocone.inr, Cocycle.rightShift_coe, Cocycle.ofHom_coe]
  simp only [Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero i),
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero (i + m))]
  simp only [mappingCone.shiftIso, shiftFunctor_map_f',
    Linear.comp_units_smul, Category.assoc, shiftFunctorObjXIso]
  simp only [Iso.app_hom, shiftFunctorComm_hom_app_f]
  simp only [
    Cochain.ofHom_v]
  erw [← HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
  · simp only [mappingCone.inr_f_desc_f_assoc, shiftFunctor_map_f',
      HomologicalComplex.XIsoOfEq, eqToIso.hom]
    simp only [eqToIso.inv, eqToHom_trans]
  · omega

variable {K' L' : CochainComplex A ℤ} (ψ : K' ⟶ L')
  (a : Arrow.mk φ ⟶ Arrow.mk ψ)
noncomputable def coneMap : mappingCone φ ⟶ mappingCone ψ :=
  HomologicalComplex.homotopyCofiber.mapArrowHom φ ψ
    (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) a
@[reassoc]
lemma coneMap_inl (i j : ℤ) (h : i + -1 = j) :
    (mappingCone.inl φ).v i j h ≫ (coneMap φ ψ a).f j =
      a.left.f i ≫ (mappingCone.inl ψ).v i j h := by
  simp only [Int.reduceNeg, mappingCone.inl, Cochain.mk_v, coneMap,
    HomologicalComplex.homotopyCofiber.mapArrowHom, Arrow.mk_right, Arrow.mk_left,
    HomologicalComplex.homotopyCofiber.inlX_desc_f, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.compLeft_hom, add_zero, zero_add]
  rw [HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom ψ _ i j (by
    change j + 1 = i
    omega)]
@[reassoc]
lemma coneMap_inr (j : ℤ) :
    (mappingCone.inr φ).f j ≫ (coneMap φ ψ a).f j =
      a.right.f j ≫ (mappingCone.inr ψ).f j := by
  simp [coneMap, mappingCone.inr, HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.inr_f]

noncomputable def coconeMap : mappingCocone φ ⟶ mappingCocone ψ :=
  (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map (coneMap φ ψ a)
@[reassoc]
lemma coconeMap_inl (j : ℤ) :
    (mappingCocone.inl φ).v j j (add_zero j) ≫ (coconeMap φ ψ a).f j =
      a.left.f j ≫ (mappingCocone.inl ψ).v j j (add_zero j) := by
  simp only [coconeMap, shiftFunctor_map_f', mappingCocone.inl,
    Cochain.rightShift_v (n := -1) _ _ _ _ j _ _ (j + -1) rfl,
    shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_inv, Category.comp_id]
  exact coneMap_inl φ ψ a j (j + -1) rfl
@[reassoc]
lemma coconeMap_inr (i j : ℤ) (h : i + 1 = j) :
    (mappingCocone.inr φ).1.v i j h ≫ (coconeMap φ ψ a).f j =
      a.right.f i ≫ (mappingCocone.inr ψ).1.v i j h := by
  subst j
  simp only [coconeMap, shiftFunctor_map_f', mappingCocone.inr,
    Cocycle.rightShift_coe, Cocycle.ofHom_coe,
    Cochain.rightShift_v _ _ _ _ _ _ _ _ (add_zero i),
    Cochain.ofHom_v, shiftFunctorObjXIso]
  simp only [Category.assoc]
  erw [← HomologicalComplex.XIsoOfEq_inv_naturality (coneMap φ ψ a)
    (by omega : i + 1 + -1 = i)]
  rw [← Category.assoc, coneMap_inr]
  simp only [Category.assoc]
lemma cocone_ext_from (j : ℤ) {T : A} {f g : (mappingCocone φ).X j ⟶ T}
    (h₁ : (mappingCocone.inl φ).v j j (add_zero j) ≫ f =
      (mappingCocone.inl φ).v j j (add_zero j) ≫ g)
    (h₂ : (mappingCocone.inr φ).1.v (j - 1) j (by omega) ≫ f =
      (mappingCocone.inr φ).1.v (j - 1) j (by omega) ≫ g) : f = g := by
  calc
    f = ((mappingCocone.fst φ).f j ≫ (mappingCocone.inl φ).v j j (add_zero j) +
        (mappingCocone.snd φ).v j (j - 1) (by omega) ≫
          (mappingCocone.inr φ).1.v (j - 1) j (by omega)) ≫ f := by
      rw [mappingCocone.id_X, Category.id_comp]
    _ = ((mappingCocone.fst φ).f j ≫ (mappingCocone.inl φ).v j j (add_zero j) +
        (mappingCocone.snd φ).v j (j - 1) (by omega) ≫
          (mappingCocone.inr φ).1.v (j - 1) j (by omega)) ≫ g := by
      simp only [Preadditive.add_comp, Category.assoc, h₁, h₂]
    _ = g := by rw [mappingCocone.id_X, Category.id_comp]

universe s v
variable {S : Type s} [Category.{v} S]
  (F G : S ⥤ CochainComplex A ℤ) (τ : F ⟶ G)
noncomputable def coconeFunctor : S ⥤ CochainComplex A ℤ where
  obj X := mappingCocone (τ.app X)
  map f := coconeMap (τ.app _) (τ.app _)
    (Arrow.homMk (F.map f) (G.map f) (τ.naturality f))
  map_id X := by
    have ha : Arrow.homMk (F.map (𝟙 X)) (G.map (𝟙 X)) (τ.naturality (𝟙 X)) =
        𝟙 (Arrow.mk (τ.app X)) := by
      apply Arrow.hom_ext <;> simp
    unfold coconeMap coneMap
    rw [ha, HomologicalComplex.homotopyCofiber.mapArrowHom_id]
    exact (CategoryTheory.shiftFunctor _ (-1 : ℤ)).map_id _
  map_comp f g := by
    unfold coconeMap coneMap
    rw [← CategoryTheory.Functor.map_comp,
      ← HomologicalComplex.homotopyCofiber.mapArrowHom_comp]
    congr 2
    apply Arrow.hom_ext <;> simp

variable [HasShift S ℤ] [F.CommShift ℤ] [G.CommShift ℤ] [NatTrans.CommShift τ ℤ]
noncomputable def coconeFunctorShiftIso (X : S) (m : ℤ) :
    (coconeFunctor F G τ).obj (X⟦m⟧) ≅ ((coconeFunctor F G τ).obj X)⟦m⟧ :=
  (CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso (τ.app (X⟦m⟧)) ((τ.app X)⟦m⟧')
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩)
      (Arrow.isoMk' _ _ ((F.commShiftIso m).app X) ((G.commShiftIso m).app X)
        (NatTrans.shift_app_comm τ m X))) ≪≫
    signedCoconeShiftIso (τ.app X) m
@[reassoc]
lemma coconeFunctorShiftIso_inl (X : S) (m j : ℤ) :
    (mappingCocone.inl (τ.app (X⟦m⟧))).v j j (add_zero j) ≫
        (coconeFunctorShiftIso F G τ X m).hom.f j =
      ((F.commShiftIso m).hom.app X).f j ≫
        (mappingCocone.inl (τ.app X)).v (j + m) (j + m) (add_zero _) ≫
          (shiftFunctorObjXIso (mappingCocone (τ.app X)) m j (j + m) rfl).inv := by
  simp only [coconeFunctorShiftIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, HomologicalComplex.homotopyCofiber.mapArrowIso_hom]
  change (mappingCocone.inl (τ.app (X⟦m⟧))).v j j _ ≫
    (coconeMap _ _ _).f j ≫ (signedCoconeShiftIso _ m).hom.f j = _
  rw [coconeMap_inl_assoc, signedCoconeShiftIso_inl]
  simp only [Arrow.isoMk_hom_left, Iso.app_hom]
@[reassoc]
lemma coconeFunctorShiftIso_inr (X : S) (m i j : ℤ) (h : i + 1 = j) :
    (mappingCocone.inr (τ.app (X⟦m⟧))).1.v i j h ≫
        (coconeFunctorShiftIso F G τ X m).hom.f j =
      m.negOnePow • (((G.commShiftIso m).hom.app X).f i ≫
        (mappingCocone.inr (τ.app X)).1.v (i + m) (j + m) (by omega) ≫
          (shiftFunctorObjXIso (mappingCocone (τ.app X)) m j (j + m) rfl).inv) := by
  simp only [coconeFunctorShiftIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Functor.mapIso_hom, HomologicalComplex.homotopyCofiber.mapArrowIso_hom]
  change (mappingCocone.inr (τ.app (X⟦m⟧))).1.v i j h ≫
    (coconeMap _ _ _).f j ≫ (signedCoconeShiftIso _ m).hom.f j = _
  rw [coconeMap_inr_assoc, signedCoconeShiftIso_inr]
  simp only [Arrow.isoMk_hom_right, Iso.app_hom, Linear.comp_units_smul]
lemma coconeFunctorShiftIso_naturality {X Y : S} (f : X ⟶ Y) (m : ℤ) :
    (coconeFunctor F G τ).map (f⟦m⟧') ≫ (coconeFunctorShiftIso F G τ Y m).hom =
      (coconeFunctorShiftIso F G τ X m).hom ≫ ((coconeFunctor F G τ).map f)⟦m⟧' := by
  apply HomologicalComplex.hom_ext
  intro j
  apply cocone_ext_from
  · simp only [HomologicalComplex.comp_f, coconeFunctor]
    rw [coconeMap_inl_assoc, coconeFunctorShiftIso_inl, coconeFunctorShiftIso_inl_assoc]
    simp only [shiftFunctor_map_f', shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      Category.id_comp, Category.comp_id]
    rw [coconeMap_inl]
    have h := congrArg (fun a ↦ a.f j) ((F.commShiftIso m).hom.naturality f)
    simp only [Functor.comp_map, HomologicalComplex.comp_f, shiftFunctor_map_f'] at h
    simp only [Arrow.homMk_left]
    erw [← Category.assoc, h, Category.assoc]
  · simp only [HomologicalComplex.comp_f, coconeFunctor]
    rw [coconeMap_inr_assoc, coconeFunctorShiftIso_inr, coconeFunctorShiftIso_inr_assoc]
    simp only [shiftFunctor_map_f', Category.assoc, shiftFunctorObjXIso,
      HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv,
      Category.comp_id, Linear.comp_units_smul, Linear.units_smul_comp]
    rw [coconeMap_inr]
    have h := congrArg (fun a ↦ a.f (j - 1)) ((G.commShiftIso m).hom.naturality f)
    simp only [Functor.comp_map, HomologicalComplex.comp_f, shiftFunctor_map_f'] at h
    simp only [Arrow.homMk_right]
    erw [← Category.assoc, h, Category.assoc]
noncomputable def coconeFunctorShiftNatIso (m : ℤ) :
    shiftFunctor S m ⋙ coconeFunctor F G τ ≅
      coconeFunctor F G τ ⋙ shiftFunctor (CochainComplex A ℤ) m :=
  NatIso.ofComponents (fun X ↦ coconeFunctorShiftIso F G τ X m)
    (fun f ↦ coconeFunctorShiftIso_naturality F G τ f m)
@[reassoc]
lemma cast_cochain {K L : CochainComplex A ℤ} {n i i' j j' : ℤ}
    (γ : Cochain K L n) (hi : i = i') (hj : j = j')
    (h : i + n = j) (h' : i' + n = j') :
    (K.XIsoOfEq hi).hom ≫ γ.v i' j' h' = γ.v i j h ≫ (L.XIsoOfEq hj).hom := by
  subst hi
  subst hj
  simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Category.id_comp,
    Category.comp_id]
lemma coconeFunctorShiftNatIso_zero :
    coconeFunctorShiftNatIso F G τ 0 = Functor.CommShift.isoZero (coconeFunctor F G τ) ℤ := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply HomologicalComplex.hom_ext
  intro j
  apply cocone_ext_from
  · change (mappingCocone.inl _).v j j _ ≫
      (coconeFunctorShiftIso F G τ X 0).hom.f j = _
    rw [coconeFunctorShiftIso_inl, Functor.CommShift.isoZero_hom_app]
    simp only [HomologicalComplex.comp_f, coconeFunctor]
    rw [coconeMap_inl_assoc, F.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    simp only [HomologicalComplex.comp_f, shiftFunctorZero_inv_app_f,
      shiftFunctorObjXIso,
      Arrow.homMk_left, Category.assoc]
    erw [cast_cochain_assoc _ (show j = j + 0 by omega)
      (show j = j + 0 by omega) (by omega) (by omega)]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id]
  · change (mappingCocone.inr _).1.v (j - 1) j _ ≫
      (coconeFunctorShiftIso F G τ X 0).hom.f j = _
    rw [coconeFunctorShiftIso_inr, Functor.CommShift.isoZero_hom_app]
    simp only [HomologicalComplex.comp_f, coconeFunctor]
    rw [coconeMap_inr_assoc, G.commShiftIso_zero, Functor.CommShift.isoZero_hom_app]
    simp only [HomologicalComplex.comp_f, shiftFunctorZero_inv_app_f,
      shiftFunctorObjXIso,
      Arrow.homMk_right, Category.assoc, Int.negOnePow_zero, one_smul]
    erw [cast_cochain_assoc _ (show j - 1 = j - 1 + 0 by omega)
      (show j = j + 0 by omega) (by omega) (by omega)]
    simp only [HomologicalComplex.XIsoOfEq_rfl, Iso.refl_inv, Category.comp_id]
lemma coconeFunctorShiftNatIso_add (m n : ℤ) :
    coconeFunctorShiftNatIso F G τ (m + n) =
      Functor.CommShift.isoAdd (coconeFunctorShiftNatIso F G τ m)
        (coconeFunctorShiftNatIso F G τ n) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  apply HomologicalComplex.hom_ext
  intro j
  apply cocone_ext_from
  · change (mappingCocone.inl _).v j j _ ≫
      (coconeFunctorShiftIso F G τ X (m + n)).hom.f j = _
    rw [coconeFunctorShiftIso_inl, Functor.CommShift.isoAdd_hom_app]
    simp only [HomologicalComplex.comp_f, coconeFunctorShiftNatIso,
      NatIso.ofComponents_hom_app, coconeFunctor, shiftFunctor_map_f']
    rw [coconeMap_inl_assoc]
    dsimp only [Functor.comp_obj]
    erw [coconeFunctorShiftIso_inl_assoc]
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.comp_id, Category.id_comp]
    erw [coconeFunctorShiftIso_inl_assoc]
    rw [F.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    simp only [HomologicalComplex.comp_f, shiftFunctor_map_f', shiftFunctorAdd_inv_app_f,
      Arrow.homMk_left, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.assoc]
    erw [Category.id_comp, cast_cochain _ (show j + n + m = j + (m + n) by omega)
      (show j + n + m = j + (m + n) by omega) (by omega) (by omega)]
  · change (mappingCocone.inr _).1.v (j - 1) j _ ≫
      (coconeFunctorShiftIso F G τ X (m + n)).hom.f j = _
    rw [coconeFunctorShiftIso_inr F G τ X (m + n) (j - 1) j (by omega),
      Functor.CommShift.isoAdd_hom_app]
    simp only [HomologicalComplex.comp_f, coconeFunctorShiftNatIso,
      NatIso.ofComponents_hom_app, coconeFunctor, shiftFunctor_map_f']
    rw [coconeMap_inr_assoc]
    dsimp only [Functor.comp_obj]
    erw [coconeFunctorShiftIso_inr_assoc F G τ (X⟦m⟧) n (j - 1) j (by omega)]
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.comp_id, Category.assoc,
      Linear.comp_units_smul, Linear.units_smul_comp]
    erw [coconeFunctorShiftIso_inr_assoc F G τ X m (j - 1 + n) (j + n) (by omega)]
    rw [G.commShiftIso_add, Functor.CommShift.isoAdd_hom_app]
    simp only [HomologicalComplex.comp_f, shiftFunctor_map_f', shiftFunctorAdd_inv_app_f,
      Arrow.homMk_right, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_inv, Category.comp_id, Category.assoc,
      Linear.comp_units_smul, Linear.units_smul_comp, smul_smul, Int.negOnePow_add]
    rw [mul_comm m.negOnePow n.negOnePow]
    erw [cast_cochain _ (show j - 1 + n + m = j - 1 + (m + n) by omega)
      (show j + n + m = j + (m + n) by omega) (by omega) (by omega)]

@[instance_reducible]
noncomputable def coconeCommShift : (coconeFunctor F G τ).CommShift ℤ where
  commShiftIso := coconeFunctorShiftNatIso F G τ
  commShiftIso_zero := coconeFunctorShiftNatIso_zero F G τ
  commShiftIso_add := coconeFunctorShiftNatIso_add F G τ

end CategoryTheory.SignedCoconeShift

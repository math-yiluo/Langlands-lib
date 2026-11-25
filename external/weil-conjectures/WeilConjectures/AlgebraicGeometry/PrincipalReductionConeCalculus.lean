/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.DerivedCompletion
import WeilConjectures.AlgebraicGeometry.PrincipalReductionDerivedNormalization
import WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import WeilConjectures.CategoryTheory.Sites.MonObj

/-!
# Strict principal reduction and its compatible cone comparisons

proof.md`,
Cones paragraph; Stacks Tag 014E, definition-cone
(auxiliary; not a blueprint node).

Positive level n+1 is indexed by n : ℕ, as in AdicCompletion. Cone coordinates
are ordered target, shifted source. The comparison is one natural family,
including its quotient transitions and its specified reduction coaugmentations.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 4096

universe u vC uC

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite Pretriangulated
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

/-- The standard cone coordinates in target, shifted-source order.
Source: Stacks Tag 014E, definition-cone
(auxiliary; not a blueprint node). -/
def principalConeCoordinates {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasBinaryBiproducts C] {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (CochainComplex.mappingCone f).X q ≅ B.X q ⊞ A.X (q + 1) :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod f q (q + 1) rfl ≪≫
    biprod.braiding _ _

/-- The signed four-coordinate interchange (b,a,b',a') to (b,b',a,-a').
Source: blueprint Cones paragraph, explicit cone interchange
(auxiliary; not a blueprint node). -/
def principalConeInterchange {C : Type uC} [Category.{vC} C] [Preadditive C]
    [HasBinaryBiproducts C] (B A B' A' : C) :
    (B ⊞ A) ⊞ (B' ⊞ A') ⟶ (B ⊞ B') ⊞ (A ⊞ A') :=
  biprod.lift
    (biprod.lift (biprod.fst ≫ biprod.fst) (biprod.snd ≫ biprod.fst))
    (biprod.lift (biprod.fst ≫ biprod.snd) (-(biprod.snd ≫ biprod.snd)))

namespace PrincipalConeShift
open CochainComplex
universe vS aS bS
variable {A : Type u} [Category.{vS} A] [Preadditive A] [HasBinaryBiproducts A]
variable {C : Type aS} [Category.{bS} C]
private noncomputable def squareIso {K L K' L' : CochainComplex A ℤ}
    (f : K ⟶ L) (f' : K' ⟶ L') (e : K ≅ K') (e' : L ≅ L')
    (h : f ≫ e'.hom = e.hom ≫ f') : mappingCone f ≅ mappingCone f' where
  hom := mappingCone.map f f' e.hom e'.hom h
  inv := mappingCone.map f' f e.inv e'.inv (by
    rw [← cancel_epi e.hom, ← cancel_mono e'.hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
      Iso.hom_inv_id_assoc, h])
  hom_inv_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.hom_inv_id] using mappingCone.map_id f
  inv_hom_id := by
    rw [← mappingCone.map_comp]
    simpa only [Iso.inv_hom_id] using mappingCone.map_id f'
private noncomputable def coneFunctor {F G : C ⥤ CochainComplex A ℤ} (τ : F ⟶ G) :
    C ⥤ CochainComplex A ℤ where
  obj X := mappingCone (τ.app X)
  map f := mappingCone.map _ _ (F.map f) (G.map f) (τ.naturality f).symm
  map_id X := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]
  map_comp f g := by
    ext i
    simp [mappingCone.ext_from_iff _ (i + 1) i rfl, mappingCone.map]
variable [HasShift C ℤ] {F G : C ⥤ CochainComplex A ℤ}
  [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ]
private noncomputable def coneShiftObj (X : C) (m : ℤ) :
    (coneFunctor τ).obj (X⟦m⟧) ≅ ((coneFunctor τ).obj X)⟦m⟧ :=
  squareIso (τ.app (X⟦m⟧)) ((τ.app X)⟦m⟧')
    ((F.commShiftIso m).app X) ((G.commShiftIso m).app X)
    (NatTrans.shift_app_comm τ m X).symm ≪≫ (mappingCone.shiftIso (τ.app X) m).symm
private theorem coneShift_naturality {X Y : C} (f : X ⟶ Y) (m : ℤ) :
    (coneFunctor τ).map (f⟦m⟧') ≫ (coneShiftObj τ Y m).hom =
      (coneShiftObj τ X m).hom ≫ ((coneFunctor τ).map f)⟦m⟧' := by
  ext i
  apply mappingCone.ext_from (τ.app (X⟦m⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, shiftFunctor_obj_X', coneShiftObj,
      squareIso, Iso.app_hom, Iso.app_inv, mappingCone.shiftIso, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v, Category.assoc,
      mappingCone.inl_v_desc_f, HomComplex.Cochain.units_smul_v, HomComplex.Cochain.shift_v',
      Linear.comp_units_smul, shiftFunctor_map_f', Linear.units_smul_comp, smul_left_cancel_iff]
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simpa only [HomologicalComplex.comp_f, Functor.comp_map,
      CochainComplex.shiftFunctor_map_f'] using
      congrArg (fun g ↦ g.f (i + 1)) ((F.commShiftIso m).hom.naturality f)
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, shiftFunctor_obj_X', coneShiftObj,
      squareIso, Iso.app_hom, Iso.app_inv, mappingCone.shiftIso, Iso.symm_mk, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, Category.assoc,
      mappingCone.inr_f_desc_f, shiftFunctor_map_f']
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    simpa only [HomologicalComplex.comp_f, Functor.comp_map,
      CochainComplex.shiftFunctor_map_f'] using
      congrArg (fun g ↦ g.f i) ((G.commShiftIso m).hom.naturality f)
private noncomputable def coneShiftIso (m : ℤ) :
    CategoryTheory.shiftFunctor C m ⋙ coneFunctor τ ≅
      coneFunctor τ ⋙ CategoryTheory.shiftFunctor _ m :=
  NatIso.ofComponents (fun X ↦ coneShiftObj τ X m) (fun f ↦ coneShift_naturality τ f m)

omit [HasBinaryBiproducts A] in
private theorem cochain_cast {K L : CochainComplex A ℤ} {n : ℤ}
    (γ : HomComplex.Cochain K L n) {p p' q q' : ℤ} (hp : p = p') (hq : q = q')
    (h : p + n = q) (h' : p' + n = q') :
    (HomologicalComplex.XIsoOfEq K hp).inv ≫ γ.v p q h =
      γ.v p' q' h' ≫ (HomologicalComplex.XIsoOfEq L hq).inv := by
  subst hp
  subst hq
  simp
private theorem coneShiftIso_zero :
    coneShiftIso τ 0 = Functor.CommShift.isoZero (coneFunctor τ) ℤ := by
  ext X i
  apply mappingCone.ext_from (τ.app (X⟦(0 : ℤ)⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_zero,
      Iso.app_hom, Functor.CommShift.isoZero_hom_app, shiftFunctorZero_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoZero_inv_app, mappingCone.shiftIso,
      Int.negOnePow_zero, one_smul, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
      shiftFunctorZero'_inv_app_f, mappingCone.inl_v_desc_f, HomComplex.Cochain.shift_v']
    rw [cochain_cast]
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_zero,
      Iso.app_hom, Functor.CommShift.isoZero_hom_app, shiftFunctorZero_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoZero_inv_app, mappingCone.shiftIso,
      Int.negOnePow_zero, one_smul, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, shiftFunctorZero'_inv_app_f,
      mappingCone.inr_f_desc_f, shiftFunctor_map_f']
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality]

private theorem coneShiftIso_add (a b : ℤ) :
    coneShiftIso τ (a + b) = Functor.CommShift.isoAdd (coneShiftIso τ a) (coneShiftIso τ b) := by
  ext X i
  apply mappingCone.ext_from (τ.app (X⟦a + b⟧)) (i + 1) i rfl
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_add,
      Iso.app_hom, Functor.CommShift.isoAdd_hom_app, shiftFunctorAdd_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoAdd_inv_app, mappingCone.shiftIso,
      add_comm a b, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inl_v_desc_f_assoc,
      HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v, shiftFunctor_map_f',
      shiftFunctorAdd'_inv_app_f, mappingCone.inl_v_desc_f, HomComplex.Cochain.units_smul_v,
      HomComplex.Cochain.shift_v', Linear.comp_units_smul, Functor.map_comp,
      Linear.units_smul_comp, smul_smul, ← Int.negOnePow_add, smul_left_cancel_iff]
    rw [cochain_cast]
  · simp only [coneFunctor, mappingCone.map, Int.reduceNeg, Functor.comp_obj,
      shiftFunctor_obj_X', coneShiftIso, coneShiftObj, squareIso, Functor.commShiftIso_add,
      Iso.app_hom, Functor.CommShift.isoAdd_hom_app, shiftFunctorAdd_eq,
      HomComplex.Cochain.ofHom_comp, HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      Category.assoc, Iso.app_inv, Functor.CommShift.isoAdd_inv_app, mappingCone.shiftIso,
      add_comm a b, Iso.symm_mk, NatIso.ofComponents_hom_app, Iso.trans_hom,
      HomologicalComplex.comp_f, mappingCone.inr_f_desc_f_assoc, shiftFunctor_map_f',
      shiftFunctorAdd'_inv_app_f, mappingCone.inr_f_desc_f, Functor.map_comp]
    rw [← HomologicalComplex.XIsoOfEq_inv_naturality]

@[instance_reducible]
private noncomputable def coneCommShift : (coneFunctor τ).CommShift ℤ where
  commShiftIso := coneShiftIso τ
  commShiftIso_zero := coneShiftIso_zero τ
  commShiftIso_add := coneShiftIso_add τ

end PrincipalConeShift

section StrictCones

variable {C : Type uC} [Category.{vC} C] [Preadditive C] [HasBinaryBiproducts C]

private abbrev strictCone (τ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ where
  obj M := CochainComplex.mappingCone (F := M) (G := M) (τ.app M)
  map {_M _N} g := CochainComplex.mappingCone.map _ _ g g (τ.naturality g).symm
  map_id _M := CochainComplex.mappingCone.map_id _
  map_comp _f _g := CochainComplex.mappingCone.map_comp _ _ _ _ _ _ _ _ _

@[reassoc] private theorem coneInl_coordinates {A B : CochainComplex C ℤ}
    (f : A ⟶ B) (q : ℤ) :
    (CochainComplex.mappingCone.inl f).v (q + 1) q (by omega) ≫
        (principalConeCoordinates f q).hom = biprod.inr := by
  apply biprod.hom_ext <;>
    simp [principalConeCoordinates, CochainComplex.mappingCone.inl]

@[reassoc] private theorem coneInr_coordinates {A B : CochainComplex C ℤ}
    (f : A ⟶ B) (q : ℤ) :
    (CochainComplex.mappingCone.inr f).f q ≫
        (principalConeCoordinates f q).hom = biprod.inl := by
  apply biprod.hom_ext <;>
    simp [principalConeCoordinates, CochainComplex.mappingCone.inr]

@[reassoc (attr := simp)]
private theorem coordinates_fst {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (principalConeCoordinates f q).hom ≫ biprod.fst =
      (CochainComplex.mappingCone.snd f).v q q (add_zero q) := by
  apply CochainComplex.mappingCone.ext_from f (q + 1) q rfl <;>
    simp [coneInl_coordinates_assoc, coneInr_coordinates_assoc]

@[reassoc (attr := simp)]
private theorem coordinates_snd {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (principalConeCoordinates f q).hom ≫ biprod.snd =
      (CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl := by
  apply CochainComplex.mappingCone.ext_from f (q + 1) q rfl <;>
    simp [coneInl_coordinates_assoc, coneInr_coordinates_assoc]

private theorem coneMap_coordinates {A B A' B' : CochainComplex C ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f') (q : ℤ) :
    (CochainComplex.mappingCone.map f f' a b h).f q ≫
        (principalConeCoordinates f' q).hom =
      (principalConeCoordinates f q).hom ≫ biprod.map (b.f q) (a.f (q + 1)) := by
  apply CochainComplex.mappingCone.ext_from f (q + 1) q rfl
  · simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v, Category.assoc,
      coneInl_coordinates, coneInl_coordinates_assoc]
    simp [biprod.inr_map]
  · simp only [CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inr_f_desc_f_assoc,
      HomologicalComplex.comp_f, Category.assoc,
      coneInr_coordinates, coneInr_coordinates_assoc]
    simp [biprod.inl_map]

private def strictConeUnit (τ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _) :
    𝟭 _ ⟶ strictCone τ where
  app M := CochainComplex.mappingCone.inr (τ.app M)
  naturality M N f := by
    simpa only [strictCone, CochainComplex.mappingCone.map_eq_mapOfHomotopy] using
      (CochainComplex.mappingCone.triangleMapOfHomotopy_comm₂
        (Homotopy.ofEq (τ.naturality f).symm)).symm

private def conePair {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (q : ℤ) {Z : C} (b : Z ⟶ B.X q) (a : Z ⟶ A.X (q + 1)) :
    Z ⟶ (CochainComplex.mappingCone f).X q :=
  b ≫ (CochainComplex.mappingCone.inr f).f q +
    a ≫ (CochainComplex.mappingCone.inl f).v (q + 1) q (by omega)

@[reassoc (attr := simp)]
private theorem conePair_fst {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (q : ℤ) {Z : C} (b : Z ⟶ B.X q) (a : Z ⟶ A.X (q + 1)) :
    conePair f q b a ≫ (CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl = a := by
  simp [conePair]

@[reassoc (attr := simp)]
private theorem conePair_snd {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (q : ℤ) {Z : C} (b : Z ⟶ B.X q) (a : Z ⟶ A.X (q + 1)) :
    conePair f q b a ≫ (CochainComplex.mappingCone.snd f).v q q (add_zero q) = b := by
  simp [conePair]

@[reassoc (attr := simp)]
private theorem coneMap_fst {A B A' B' : CochainComplex C ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f') (q : ℤ) :
    (CochainComplex.mappingCone.map f f' a b h).f q ≫
        (CochainComplex.mappingCone.fst f').1.v q (q + 1) rfl =
      (CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl ≫ a.f (q + 1) := by
  apply CochainComplex.mappingCone.ext_from f (q + 1) q rfl <;>
    simp [CochainComplex.mappingCone.map]

@[reassoc (attr := simp)]
private theorem coneMap_snd {A B A' B' : CochainComplex C ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f') (q : ℤ) :
    (CochainComplex.mappingCone.map f f' a b h).f q ≫
        (CochainComplex.mappingCone.snd f').v q q (add_zero q) =
      (CochainComplex.mappingCone.snd f).v q q (add_zero q) ≫ b.f q := by
  apply CochainComplex.mappingCone.ext_from f (q + 1) q rfl <;>
    simp [CochainComplex.mappingCone.map]

private abbrev strictConeMap
    (τ σ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    (a : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    (h : ∀ M, τ.app M = a.app M ≫ σ.app M) : strictCone τ ⟶ strictCone σ where
  app M := CochainComplex.mappingCone.map _ _ (a.app M) (𝟙 M) (by
    exact (Category.comp_id (τ.app M)).trans (h M))
  naturality M N g := by
    dsimp only [strictCone]
    rw [← CochainComplex.mappingCone.map_comp, ← CochainComplex.mappingCone.map_comp]
    congr 1
    · exact a.naturality g
    · simp

private theorem strictConeUnit_map
    (τ σ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    (a : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    (h : ∀ M, τ.app M = a.app M ≫ σ.app M) (M : CochainComplex C ℤ) :
    (strictConeUnit τ).app M ≫ (strictConeMap τ σ a h).app M =
      (strictConeUnit σ).app M := by
  simp [strictConeUnit, CochainComplex.mappingCone.map]

section DoubleCones

open CochainComplex CochainComplex.HomComplex Preadditive

private abbrev ca {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (i j : ℤ) (h : i + 1 = j) := (mappingCone.fst f).1.v i j h

private abbrev cb {A B : CochainComplex C ℤ} (f : A ⟶ B) (i : ℤ) :=
  (mappingCone.snd f).v i i (add_zero i)

@[reassoc (attr := simp)]
private theorem conePair_ca {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (q : ℤ) {Z : C} (b : Z ⟶ B.X q) (a : Z ⟶ A.X (q + 1))
    (j : ℤ) (hj : q + 1 = j) :
    conePair f q b a ≫ ca f q j hj = a ≫ (A.XIsoOfEq hj).hom := by
  subst j
  simp

private abbrev diagonal {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :=
  mappingCone.map f f s t h.symm

private abbrev vertical {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :=
  mappingCone.map s t f f h

private def doublePhi {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCone (diagonal s t f h)).X q ⟶ (mappingCone (vertical s t f h)).X q :=
  conePair (vertical s t f h) q
    (conePair t q
      (cb (diagonal s t f h) q ≫ cb f q)
      (ca (diagonal s t f h) q (q + 1) rfl ≫ cb f (q + 1)))
    (conePair s (q + 1)
      (cb (diagonal s t f h) q ≫ ca f q (q + 1) rfl)
      (-(ca (diagonal s t f h) q (q + 1) rfl ≫ ca f (q + 1) (q + 1 + 1) rfl)))

private def doublePsi {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCone (vertical s t f h)).X q ⟶ (mappingCone (diagonal s t f h)).X q :=
  conePair (diagonal s t f h) q
    (conePair f q
      (cb (vertical s t f h) q ≫ cb t q)
      (ca (vertical s t f h) q (q + 1) rfl ≫ cb s (q + 1)))
    (conePair f (q + 1)
      (cb (vertical s t f h) q ≫ ca t q (q + 1) rfl)
      (-(ca (vertical s t f h) q (q + 1) rfl ≫ ca s (q + 1) (q + 1 + 1) rfl)))

@[reassoc (attr := simp)]
private theorem doublePhi_ca {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    doublePhi s t f h q ≫ ca (vertical s t f h) q (q + 1) rfl =
      conePair s (q + 1)
        (cb (diagonal s t f h) q ≫ ca f q (q + 1) rfl)
        (-(ca (diagonal s t f h) q (q + 1) rfl ≫ ca f (q + 1) (q + 1 + 1) rfl)) := by
  simp [doublePhi]

@[reassoc (attr := simp)]
private theorem doublePhi_cb {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    doublePhi s t f h q ≫ cb (vertical s t f h) q =
      conePair t q
        (cb (diagonal s t f h) q ≫ cb f q)
        (ca (diagonal s t f h) q (q + 1) rfl ≫ cb f (q + 1)) := by
  simp [doublePhi]

@[reassoc (attr := simp)]
private theorem doublePsi_ca {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    doublePsi s t f h q ≫ ca (diagonal s t f h) q (q + 1) rfl =
      conePair f (q + 1)
        (cb (vertical s t f h) q ≫ ca t q (q + 1) rfl)
        (-(ca (vertical s t f h) q (q + 1) rfl ≫ ca s (q + 1) (q + 1 + 1) rfl)) := by
  simp [doublePsi]

@[reassoc (attr := simp)]
private theorem doublePsi_cb {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    doublePsi s t f h q ≫ cb (diagonal s t f h) q =
      conePair f q
        (cb (vertical s t f h) q ≫ cb t q)
        (ca (vertical s t f h) q (q + 1) rfl ≫ cb s (q + 1)) := by
  simp [doublePsi]

private def doubleDegreeIso {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (mappingCone (diagonal s t f h)).X q ≅ (mappingCone (vertical s t f h)).X q where
  hom := doublePhi s t f h q
  inv := doublePsi s t f h q
  hom_inv_id := by
    apply mappingCone.ext_to (diagonal s t f h) q (q + 1) rfl
    · apply mappingCone.ext_to f (q + 1) (q + 1 + 1) rfl <;>
        simp [Category.assoc, ca, cb]
    · apply mappingCone.ext_to f q (q + 1) rfl <;>
        simp [Category.assoc, ca, cb]
  inv_hom_id := by
    apply mappingCone.ext_to (vertical s t f h) q (q + 1) rfl
    · apply mappingCone.ext_to s (q + 1) (q + 1 + 1) rfl <;>
        simp [Category.assoc, ca, cb]
    · apply mappingCone.ext_to t q (q + 1) rfl <;>
        simp [Category.assoc, ca, cb]

@[reassoc (attr := simp)]
private theorem cone_d_ca {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (i j k : ℤ) (hij : i + 1 = j) (hjk : j + 1 = k) :
    (mappingCone f).d i j ≫ ca f j k hjk = -ca f i j hij ≫ A.d j k :=
  mappingCone.d_fst_v f i j k hij hjk

@[reassoc (attr := simp)]
private theorem cone_d_cb {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (i j : ℤ) (hij : i + 1 = j) :
    (mappingCone f).d i j ≫ cb f j = ca f i j hij ≫ f.f j + cb f i ≫ B.d i j :=
  mappingCone.d_snd_v f i j hij

private theorem doublePhi_comm {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (i j : ℤ) (hij : i + 1 = j) :
    doublePhi s t f h i ≫ (mappingCone (vertical s t f h)).d i j =
      (mappingCone (diagonal s t f h)).d i j ≫ doublePhi s t f h j := by
  obtain rfl : j = i + 1 := by omega
  apply mappingCone.ext_to (vertical s t f h) (i + 1) (i + 1 + 1) rfl
  · apply mappingCone.ext_to s (i + 1 + 1) (i + 1 + 1 + 1) rfl
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, ca, cb, diagonal, vertical]
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, ca, cb, diagonal, vertical]
      abel
  · apply mappingCone.ext_to t (i + 1) (i + 1 + 1) rfl
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, ca, cb, diagonal, vertical]
      abel
    · simp [Category.assoc, -HomologicalComplex.Hom.comm,
        -HomologicalComplex.Hom.comm_assoc, ca, cb, diagonal, vertical]
      abel

private def doubleInterchange {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCone (diagonal s t f h) ≅ mappingCone (vertical s t f h) :=
  HomologicalComplex.Hom.isoOfComponents (doubleDegreeIso s t f h)
    (fun i j hij ↦ doublePhi_comm s t f h i j hij)

private theorem doubleInterchange_coordinates {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) (q : ℤ) :
    (doubleInterchange s t f h).hom.f q ≫
        (principalConeCoordinates (vertical s t f h) q).hom ≫
        biprod.map (principalConeCoordinates t q).hom
          (principalConeCoordinates s (q + 1)).hom =
      (principalConeCoordinates (diagonal s t f h) q).hom ≫
        biprod.map (principalConeCoordinates f q).hom
          (principalConeCoordinates f (q + 1)).hom ≫
        principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
          (A.X (q + 1 + 1)) := by
  apply biprod.hom_ext
  · apply biprod.hom_ext <;>
      simp [doubleInterchange, doubleDegreeIso, Category.assoc, ca, cb,
        principalConeInterchange]
  · apply biprod.hom_ext <;>
      simp [doubleInterchange, doubleDegreeIso, Category.assoc, ca, cb,
        principalConeInterchange]

private theorem doubleInterchange_unit {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t) :
    mappingCone.inr (diagonal s t f h) ≫ (doubleInterchange s t f h).hom =
      mappingCone.map f (vertical s t f h) (mappingCone.inr s) (mappingCone.inr t)
        (by simp [vertical, mappingCone.map]) := by
  ext q
  apply mappingCone.ext_to (vertical s t f h) q (q + 1) rfl
  · apply mappingCone.ext_to s (q + 1) (q + 1 + 1) rfl <;>
      simp [doubleInterchange, doubleDegreeIso, Category.assoc, ca, cb]
  · apply mappingCone.ext_to t q (q + 1) rfl <;>
      simp [doubleInterchange, doubleDegreeIso, Category.assoc, ca, cb]

private def interchangeOfEq {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f)
    (hg : g = diagonal s t f h) :
    CochainComplex.mappingCone g ≅ CochainComplex.mappingCone (vertical s t f h) :=
  eqToIso (congrArg (fun k : CochainComplex.mappingCone f ⟶
    CochainComplex.mappingCone f ↦ CochainComplex.mappingCone k) hg) ≪≫ doubleInterchange s t f h

@[reassoc (attr := simp)]
private theorem interchangeOfEq_ca {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f)
    (hg : g = diagonal s t f h) (q : ℤ) :
    (interchangeOfEq s t f h g hg).hom.f q ≫ ca (vertical s t f h) q (q + 1) rfl =
      conePair s (q + 1) (cb g q ≫ ca f q (q + 1) rfl)
        (-(ca g q (q + 1) rfl ≫ ca f (q + 1) (q + 1 + 1) rfl)) := by
  subst g
  simp [interchangeOfEq, doubleInterchange, doubleDegreeIso]

@[reassoc (attr := simp)]
private theorem interchangeOfEq_cb {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f)
    (hg : g = diagonal s t f h) (q : ℤ) :
    (interchangeOfEq s t f h g hg).hom.f q ≫ cb (vertical s t f h) q =
      conePair t q (cb g q ≫ cb f q)
        (ca g q (q + 1) rfl ≫ cb f (q + 1)) := by
  subst g
  simp [interchangeOfEq, doubleInterchange, doubleDegreeIso]

private theorem interchangeOfEq_coordinates {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f)
    (hg : g = diagonal s t f h) (q : ℤ) :
    (interchangeOfEq s t f h g hg).hom.f q ≫
        (principalConeCoordinates (vertical s t f h) q).hom ≫
        biprod.map (principalConeCoordinates t q).hom
          (principalConeCoordinates s (q + 1)).hom =
      (principalConeCoordinates g q).hom ≫
        biprod.map (principalConeCoordinates f q).hom
          (principalConeCoordinates f (q + 1)).hom ≫
        principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
          (A.X (q + 1 + 1)) := by
  subst g
  simpa [interchangeOfEq] using doubleInterchange_coordinates s t f h q

private theorem interchangeOfEq_unit {A B : CochainComplex C ℤ}
    (s : A ⟶ A) (t : B ⟶ B) (f : A ⟶ B) (h : s ≫ f = f ≫ t)
    (g : CochainComplex.mappingCone f ⟶ CochainComplex.mappingCone f)
    (hg : g = diagonal s t f h) :
    mappingCone.inr g ≫ (interchangeOfEq s t f h g hg).hom =
      mappingCone.map f (vertical s t f h) (mappingCone.inr s) (mappingCone.inr t)
        (by simp [vertical, mappingCone.map]) := by
  subst g
  simpa [interchangeOfEq] using doubleInterchange_unit s t f h

end DoubleCones

private abbrev chainAction (μ : 𝟭 C ⟶ 𝟭 C) :
    𝟭 (CochainComplex C ℤ) ⟶ 𝟭 (CochainComplex C ℤ) :=
  μ.mapHomologicalComplex (.up ℤ)

private theorem chainAction_cone (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    CochainComplex.mappingCone.map f f ((chainAction μ).app A)
      ((chainAction μ).app B) ((chainAction μ).naturality f) =
        (chainAction μ).app (CochainComplex.mappingCone f) := by
  ext i
  apply CochainComplex.mappingCone.ext_from f (i + 1) i rfl
  · simp only [Int.reduceNeg, CochainComplex.mappingCone.map,
      CochainComplex.mappingCone.inl_v_desc_f,
      CochainComplex.HomComplex.Cochain.zero_cochain_comp_v,
      CochainComplex.HomComplex.Cochain.ofHom_v]
    exact (μ.naturality _).symm
  · simp only [CochainComplex.mappingCone.map, Int.reduceNeg,
      CochainComplex.mappingCone.inr_f_desc_f, HomologicalComplex.comp_f]
    exact (μ.naturality _).symm

private local instance chainAction_commShift (μ : 𝟭 C ⟶ 𝟭 C) :
    NatTrans.CommShift (chainAction μ) ℤ where
  shift_comm n := by
    ext M i
    simp [chainAction, CochainComplex.shiftFunctor_map_f']

@[instance_reducible]
private def strictConeShift (μ : 𝟭 C ⟶ 𝟭 C) :
    (strictCone (chainAction μ)).CommShift ℤ :=
  PrincipalConeShift.coneCommShift (chainAction μ)

private abbrev strictInterchange (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    (strictCone (chainAction μ)).obj (CochainComplex.mappingCone f) ≅
      CochainComplex.mappingCone ((strictCone (chainAction μ)).map f) :=
  interchangeOfEq ((chainAction μ).app A) ((chainAction μ).app B)
    f ((chainAction μ).naturality f).symm _ (chainAction_cone μ f).symm

@[reassoc (attr := simp)]
private theorem strictCone_map_fst (τ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    {M N : CochainComplex C ℤ} (g : M ⟶ N) (q : ℤ) :
    ((strictCone τ).map g).f q ≫ (CochainComplex.mappingCone.fst (τ.app N)).1.v
        q (q + 1) rfl =
      (CochainComplex.mappingCone.fst (τ.app M)).1.v q (q + 1) rfl ≫ g.f (q + 1) := by
  exact coneMap_fst _ _ g g (τ.naturality g).symm q

@[reassoc (attr := simp)]
private theorem strictCone_map_snd (τ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _)
    {M N : CochainComplex C ℤ} (g : M ⟶ N) (q : ℤ) :
    ((strictCone τ).map g).f q ≫ (CochainComplex.mappingCone.snd (τ.app N)).v
        q q (add_zero q) =
      (CochainComplex.mappingCone.snd (τ.app M)).v q q (add_zero q) ≫ g.f q := by
  exact coneMap_snd _ _ g g (τ.naturality g).symm q

@[reassoc (attr := simp)]
private theorem strictInterchange_ca (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (strictInterchange μ f).hom.f q ≫
        (CochainComplex.mappingCone.fst ((strictCone (chainAction μ)).map f)).1.v
          q (q + 1) rfl =
      conePair ((chainAction μ).app A) (q + 1)
        (cb ((chainAction μ).app (CochainComplex.mappingCone f)) q ≫
          ca f q (q + 1) rfl)
        (-(ca ((chainAction μ).app (CochainComplex.mappingCone f)) q (q + 1) rfl ≫
          ca f (q + 1) (q + 1 + 1) rfl)) := by
  exact interchangeOfEq_ca _ _ f _ _ _ q

@[reassoc (attr := simp)]
private theorem strictInterchange_cb (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (strictInterchange μ f).hom.f q ≫
        (CochainComplex.mappingCone.snd ((strictCone (chainAction μ)).map f)).v
          q q (add_zero q) =
      conePair ((chainAction μ).app B) q
        (cb ((chainAction μ).app (CochainComplex.mappingCone f)) q ≫ cb f q)
        (ca ((chainAction μ).app (CochainComplex.mappingCone f)) q (q + 1) rfl ≫
          cb f (q + 1)) := by
  exact interchangeOfEq_cb _ _ f _ _ _ q

@[reassoc (attr := simp)]
private theorem strictShift_ca (μ : 𝟭 C ⟶ 𝟭 C)
    (r : ℤ) (M : CochainComplex C ℤ) (q : ℤ) :
    ((Functor.commShiftIso (self := strictConeShift μ)
        (strictCone (chainAction μ)) r).hom.app M).f q ≫
        (CochainComplex.mappingCone.fst ((chainAction μ).app M)).1.v
          (q + r) (q + r + 1) rfl =
      r.negOnePow •
        ((CochainComplex.mappingCone.fst ((chainAction μ).app (M⟦r⟧))).1.v q (q + 1) rfl ≫
          (M.XIsoOfEq (show q + 1 + r = q + r + 1 by omega)).hom) := by
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl <;>
    simp only [CochainComplex.shiftFunctor_obj_X', Functor.id_obj, Int.reduceNeg,
      Functor.comp_obj, Functor.commShiftIso, PrincipalConeShift.coneShiftIso,
      PrincipalConeShift.coneShiftObj, PrincipalConeShift.squareIso,
      CochainComplex.mappingCone.map, NatIso.trans_app, Iso.trans_hom, Iso.app_hom,
      Functor.rightUnitor_hom_app, Iso.symm_hom, Functor.leftUnitor_inv_app,
      Category.comp_id, CochainComplex.HomComplex.Cochain.id_comp, Category.id_comp,
      Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.leftUnitor_hom_app,
      Functor.rightUnitor_inv_app, CochainComplex.mappingCone.shiftIso, Iso.symm_mk,
      NatIso.ofComponents_hom_app, HomologicalComplex.comp_f, Category.assoc,
      CochainComplex.mappingCone.inl_v_desc_f_assoc,
      CochainComplex.HomComplex.Cochain.units_smul_v,
      CochainComplex.HomComplex.Cochain.shift_v', Linear.units_smul_comp,
      Linear.comp_units_smul, CochainComplex.mappingCone.inl_v_fst_v_assoc,
      smul_left_cancel_iff, CochainComplex.mappingCone.inr_f_desc_f_assoc,
      CochainComplex.shiftFunctor_map_f', CochainComplex.mappingCone.inr_f_fst_v,
      CochainComplex.mappingCone.inr_f_fst_v_assoc, zero_comp, smul_zero]
  rw [← CochainComplex.HomComplex.Cochain.v_comp_XIsoOfEq_hom
    (CochainComplex.mappingCone.fst ((chainAction μ).app M)).1
    (q + r) (q + 1 + r) (q + r + 1) (by omega) (by omega)]
  simp only [CochainComplex.mappingCone.inl_v_fst_v_assoc]
  rfl

@[reassoc (attr := simp)]
private theorem strictShift_cb (μ : 𝟭 C ⟶ 𝟭 C)
    (r : ℤ) (M : CochainComplex C ℤ) (q : ℤ) :
    ((Functor.commShiftIso (self := strictConeShift μ)
        (strictCone (chainAction μ)) r).hom.app M).f q ≫
        (CochainComplex.mappingCone.snd ((chainAction μ).app M)).v
          (q + r) (q + r) (add_zero _) =
      (CochainComplex.mappingCone.snd ((chainAction μ).app (M⟦r⟧))).v q q (add_zero q) := by
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl <;>
    simp [Functor.commShiftIso,
      PrincipalConeShift.coneShiftIso, PrincipalConeShift.coneShiftObj,
      PrincipalConeShift.squareIso, CochainComplex.mappingCone.shiftIso,
      CochainComplex.mappingCone.map, CochainComplex.HomComplex.Cochain.shift_v',
      Category.assoc]

private theorem strictShift_eq (μ : 𝟭 C ⟶ 𝟭 C)
    (r : ℤ) (M : CochainComplex C ℤ) :
    (Functor.commShiftIso (self := strictConeShift μ)
        (strictCone (chainAction μ)) r).hom.app M =
      (CochainComplex.mappingCone.shiftIso ((chainAction μ).app M) r).inv := by
  have h : (PrincipalConeShift.squareIso
      ((chainAction μ).app (M⟦r⟧)) (((chainAction μ).app M)⟦r⟧')
      (((𝟭 (CochainComplex C ℤ)).commShiftIso r).app M)
      (((𝟭 (CochainComplex C ℤ)).commShiftIso r).app M)
      (NatTrans.shift_app_comm (chainAction μ) r M).symm).hom = 𝟙 _ := by
    dsimp only [PrincipalConeShift.squareIso]
    simp only [Iso.app_hom, Functor.commShiftIso_id_hom_app]
    exact CochainComplex.mappingCone.map_id _
  change (PrincipalConeShift.squareIso
    ((chainAction μ).app (M⟦r⟧)) (((chainAction μ).app M)⟦r⟧')
    (((𝟭 (CochainComplex C ℤ)).commShiftIso r).app M)
    (((𝟭 (CochainComplex C ℤ)).commShiftIso r).app M)
    (NatTrans.shift_app_comm (chainAction μ) r M).symm).hom ≫ _ = _
  rw [h, Category.id_comp]
  rfl

private theorem strictInterchange_inr (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    (strictCone (chainAction μ)).map (CochainComplex.mappingCone.inr f) ≫
        (strictInterchange μ f).hom =
      CochainComplex.mappingCone.inr ((strictCone (chainAction μ)).map f) := by
  ext q
  apply CochainComplex.mappingCone.ext_to _ q (q + 1) rfl
  · apply CochainComplex.mappingCone.ext_to ((chainAction μ).app A)
      (q + 1) (q + 1 + 1) rfl <;>
      simp only [HomologicalComplex.comp_f, Category.assoc, strictInterchange_ca_assoc]
    all_goals simp [ca, cb]
  · apply CochainComplex.mappingCone.ext_to ((chainAction μ).app B) q (q + 1) rfl <;>
      simp only [HomologicalComplex.comp_f, Category.assoc,
        strictInterchange_cb_assoc]
    all_goals simp [ca, cb]

private theorem strictInterchange_boundary (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    (strictCone (chainAction μ)).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
        (Functor.commShiftIso (self := strictConeShift μ)
          (strictCone (chainAction μ)) (1 : ℤ)).hom.app A =
      (strictInterchange μ f).hom ≫
        (CochainComplex.mappingCone.triangle ((strictCone (chainAction μ)).map f)).mor₃ := by
  let δ : CochainComplex.mappingCone f ⟶ A⟦(1 : ℤ)⟧ :=
    (CochainComplex.mappingCone.triangle f).mor₃
  have hδ (q : ℤ) : δ.f q =
      -(CochainComplex.mappingCone.fst f).1.v q (q + 1) rfl := by
    simp [δ, CochainComplex.mappingCone.triangle, Triangle.mk_mor₃,
      CochainComplex.HomComplex.Cocycle.homOf_f,
      CochainComplex.HomComplex.Cocycle.rightShift_coe,
      CochainComplex.HomComplex.Cochain.rightShift_v]
  change (strictCone (chainAction μ)).map δ ≫ _ = _
  ext q
  apply CochainComplex.mappingCone.ext_to ((chainAction μ).app A)
    (q + 1) (q + 1 + 1) rfl
  all_goals
    simp only [HomologicalComplex.comp_f, Category.assoc,
      strictShift_ca, strictShift_cb]
    simp [hδ, CochainComplex.mappingCone.triangle, Triangle.mk_mor₃,
      CochainComplex.HomComplex.Cocycle.homOf_f,
      CochainComplex.HomComplex.Cocycle.rightShift_coe,
      CochainComplex.HomComplex.Cochain.rightShift_v, ca, cb]

private theorem strictInterchange_natural (μ : 𝟭 C ⟶ 𝟭 C)
    {A B A' B' : CochainComplex C ℤ}
    (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    (h : f ≫ b = a ≫ f')
    (h' : (strictCone (chainAction μ)).map f ≫ (strictCone (chainAction μ)).map b =
      (strictCone (chainAction μ)).map a ≫ (strictCone (chainAction μ)).map f') :
    (strictCone (chainAction μ)).map (CochainComplex.mappingCone.map f f' a b h) ≫
        (strictInterchange μ f').hom =
      (strictInterchange μ f).hom ≫ CochainComplex.mappingCone.map
        ((strictCone (chainAction μ)).map f) ((strictCone (chainAction μ)).map f')
        ((strictCone (chainAction μ)).map a) ((strictCone (chainAction μ)).map b) h' := by
  ext q
  apply CochainComplex.mappingCone.ext_to _ q (q + 1) rfl
  · apply CochainComplex.mappingCone.ext_to ((chainAction μ).app A')
      (q + 1) (q + 1 + 1) rfl <;>
      simp only [HomologicalComplex.comp_f, Category.assoc, strictInterchange_ca_assoc]
    all_goals simp [Category.assoc, ca, cb]
  · apply CochainComplex.mappingCone.ext_to ((chainAction μ).app B') q (q + 1) rfl <;>
      simp only [HomologicalComplex.comp_f, Category.assoc,
        strictInterchange_cb_assoc]
    all_goals simp [Category.assoc, ca, cb]

omit [Preadditive C] [HasBinaryBiproducts C] in
@[reassoc (attr := simp)]
private theorem central_move (μ : 𝟭 C ⟶ 𝟭 C) {U V : C} (g : U ⟶ V) :
    μ.app U ≫ g = g ≫ μ.app V := by
  exact (μ.naturality g).symm

private theorem strictInterchange_row (μ ν a : 𝟭 C ⟶ 𝟭 C)
    (h : ∀ M : CochainComplex C ℤ,
      (chainAction μ).app M = (chainAction a).app M ≫ (chainAction ν).app M)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    (strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).app
        (CochainComplex.mappingCone f) ≫ (strictInterchange ν f).hom =
      (strictInterchange μ f).hom ≫ CochainComplex.mappingCone.map
        ((strictCone (chainAction μ)).map f) ((strictCone (chainAction ν)).map f)
        ((strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).app A)
        ((strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).app B)
        ((strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).naturality f) := by
  ext q
  apply CochainComplex.mappingCone.ext_to _ q (q + 1) rfl
  · apply CochainComplex.mappingCone.ext_to ((chainAction ν).app A)
      (q + 1) (q + 1 + 1) rfl <;>
      simp [Category.assoc, ca, cb]
  · apply CochainComplex.mappingCone.ext_to ((chainAction ν).app B) q (q + 1) rfl <;>
      simp [Category.assoc, ca, cb]

private theorem strictConeMap_shift (μ ν a : 𝟭 C ⟶ 𝟭 C)
    (h : ∀ M : CochainComplex C ℤ,
      (chainAction μ).app M = (chainAction a).app M ≫ (chainAction ν).app M)
    (r : ℤ) (M : CochainComplex C ℤ) :
    (strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).app (M⟦r⟧) ≫
        (Functor.commShiftIso (self := strictConeShift ν)
          (strictCone (chainAction ν)) r).hom.app M =
      (Functor.commShiftIso (self := strictConeShift μ)
          (strictCone (chainAction μ)) r).hom.app M ≫
        ((strictConeMap (chainAction μ) (chainAction ν) (chainAction a) h).app M)⟦r⟧' := by
  ext q
  apply CochainComplex.mappingCone.ext_from _ (q + 1) q rfl
  · simp [Functor.commShiftIso,
      PrincipalConeShift.coneShiftIso, PrincipalConeShift.coneShiftObj,
      PrincipalConeShift.squareIso, CochainComplex.mappingCone.shiftIso,
      CochainComplex.mappingCone.map, Category.assoc,
      CochainComplex.HomComplex.Cochain.shift_v', chainAction]
  · simp [Functor.commShiftIso,
      PrincipalConeShift.coneShiftIso, PrincipalConeShift.coneShiftObj,
      PrincipalConeShift.squareIso, CochainComplex.mappingCone.shiftIso,
      CochainComplex.mappingCone.map, Category.assoc]

private theorem strictConeUnit_shift (μ : 𝟭 C ⟶ 𝟭 C)
    (r : ℤ) (M : CochainComplex C ℤ) :
    (strictConeUnit (chainAction μ)).app (M⟦r⟧) ≫
        (Functor.commShiftIso (self := strictConeShift μ)
          (strictCone (chainAction μ)) r).hom.app M =
      ((strictConeUnit (chainAction μ)).app M)⟦r⟧' := by
  ext q
  simp [Functor.commShiftIso, strictConeUnit,
    PrincipalConeShift.coneShiftIso, PrincipalConeShift.coneShiftObj,
    PrincipalConeShift.squareIso, CochainComplex.mappingCone.shiftIso,
    CochainComplex.mappingCone.map]

private theorem strictInterchange_coordinates (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ) :
    (strictInterchange μ f).hom.f q ≫
        (principalConeCoordinates ((strictCone (chainAction μ)).map f) q).hom ≫
        biprod.map (principalConeCoordinates ((chainAction μ).app B) q).hom
          (principalConeCoordinates ((chainAction μ).app A) (q + 1)).hom =
      (principalConeCoordinates ((chainAction μ).app (CochainComplex.mappingCone f)) q).hom ≫
        biprod.map (principalConeCoordinates f q).hom
          (principalConeCoordinates f (q + 1)).hom ≫
        principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
          (A.X (q + 1 + 1)) := by
  exact interchangeOfEq_coordinates ((chainAction μ).app A) ((chainAction μ).app B)
    f ((chainAction μ).naturality f).symm _ (chainAction_cone μ f).symm q

private theorem strictInterchange_unit (μ : 𝟭 C ⟶ 𝟭 C)
    {A B : CochainComplex C ℤ} (f : A ⟶ B) :
    (strictConeUnit (chainAction μ)).app (CochainComplex.mappingCone f) ≫
        (strictInterchange μ f).hom =
      CochainComplex.mappingCone.map f ((strictCone (chainAction μ)).map f)
        ((strictConeUnit (chainAction μ)).app A) ((strictConeUnit (chainAction μ)).app B)
        ((strictConeUnit (chainAction μ)).naturality f) := by
  exact interchangeOfEq_unit ((chainAction μ).app A) ((chainAction μ).app B)
    f ((chainAction μ).naturality f).symm _ (chainAction_cone μ f).symm

private theorem strictConeShift_coordinates (μ : 𝟭 C ⟶ 𝟭 C)
    (r : ℤ) (M : CochainComplex C ℤ) (q : ℤ) :
    ((Functor.commShiftIso (self := strictConeShift μ)
        (strictCone (chainAction μ)) r).hom.app M).f q ≫
        (((strictCone (chainAction μ)).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
        (principalConeCoordinates ((chainAction μ).app M) (q + r)).hom =
      (principalConeCoordinates ((chainAction μ).app (M⟦r⟧)) q).hom ≫
        biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
          (r.negOnePow • (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
            (add_right_comm q r 1)).hom) := by
  dsimp only [strictCone, Functor.comp_obj, Functor.id_obj]
  simp only [CochainComplex.shiftFunctor_obj_X', CochainComplex.shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom,
    Category.id_comp]
  apply biprod.hom_ext
  · simp only [Category.assoc, coordinates_fst, biprod.map_fst,
      Category.comp_id, strictShift_cb]
    exact (coordinates_fst ((chainAction μ).app (M⟦r⟧)) q).symm
  · simp only [Category.assoc, coordinates_snd, biprod.map_snd,
      Linear.comp_units_smul, strictShift_ca]
    convert congrArg (fun z ↦ r.negOnePow •
      (z ≫ (M.XIsoOfEq (show q + 1 + r = q + r + 1 by omega)).hom))
      (coordinates_snd ((chainAction μ).app (M⟦r⟧)) q).symm using 1
    all_goals simp only [Category.assoc]
    all_goals rfl

end StrictCones

private theorem strictCone_quasiIso {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory C]
    (τ : 𝟭 (CochainComplex C ℤ) ⟶ 𝟭 _) {M N : CochainComplex C ℤ}
    (g : M ⟶ N) (hg : QuasiIso g) : QuasiIso ((strictCone τ).map g) := by
  have := hg
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).mp
  exact isIso₃_of_isIso₁₂
    (DerivedCategory.Q.mapTriangle.map
      (CochainComplex.mappingCone.triangleMap _ _ g g (τ.naturality g).symm))
    (DerivedCategory.mappingCone_triangle_distinguished (τ.app M))
    (DerivedCategory.mappingCone_triangle_distinguished (τ.app N))
    (inferInstance : IsIso (DerivedCategory.Q.map g))
    (inferInstance : IsIso (DerivedCategory.Q.map g))

private theorem strict_calculus {C : Type uC} [Category.{vC} C] [Abelian C]
    [HasDerivedCategory C]
    (μ : ℕ → (𝟭 C ⟶ 𝟭 C)) (a : 𝟭 C ⟶ 𝟭 C)
    (hs : ∀ (n : ℕ) (M : CochainComplex C ℤ),
      (chainAction (μ (n + 1))).app M =
        (chainAction a).app M ≫ (chainAction (μ n)).app M)
    (F : ℕ → DerivedCategory C ⥤ DerivedCategory C)
    (sF : ∀ n : ℕ, (F n).CommShift ℤ)
    (κ : ∀ n : ℕ, strictCone (chainAction (μ n)) ⋙ DerivedCategory.Q ≅
      DerivedCategory.Q ⋙ F n)
    (step : ∀ (n : ℕ) (M : CochainComplex C ℤ),
      (F (n + 1)).obj (DerivedCategory.Q.obj M) ⟶ (F n).obj (DerivedCategory.Q.obj M))
    (unit : ∀ (n : ℕ) (M : CochainComplex C ℤ),
      DerivedCategory.Q.obj M ⟶ (F n).obj (DerivedCategory.Q.obj M))
    (hF : ∀ n : ℕ, (F n).Additive ∧
      @Functor.IsTriangulated _ _ _ _ _ _ (F n) (sF n) _ _ _ _ _ _ _ _)
    (hT : ∀ (n : ℕ) (M : CochainComplex C ℤ),
      DerivedCategory.Q.map ((strictConeMap _ _ (chainAction a) (hs n)).app M) ≫
          (κ n).hom.app M = (κ (n + 1)).hom.app M ≫ step n M)
    (hj : ∀ (n : ℕ) (M : CochainComplex C ℤ),
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr ((chainAction (μ n)).app M)) ≫
        (κ n).hom.app M = unit n M)
    (hκ : ∀ (n : ℕ) (r : ℤ) (M : CochainComplex C ℤ),
      DerivedCategory.Q.map
          (CochainComplex.mappingCone.shiftIso ((chainAction (μ n)).app M) r).inv ≫
          (DerivedCategory.Q.commShiftIso r).hom.app
            (CochainComplex.mappingCone ((chainAction (μ n)).app M)) ≫
          ((κ n).hom.app M)⟦r⟧' =
        (κ n).hom.app (M⟦r⟧) ≫
          (F n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
          (Functor.commShiftIso (self := sF n) (F n) r).hom.app (DerivedCategory.Q.obj M)) :
    ∃ (D : ℕ → CochainComplex C ℤ ⥤ CochainComplex C ℤ)
        (hobj : ∀ (n : ℕ) (M : CochainComplex C ℤ),
          (D n).obj M = CochainComplex.mappingCone ((chainAction (μ n)).app M))
        (χ : ∀ (n : ℕ) (M : CochainComplex C ℤ) (q : ℤ),
          ((D n).obj M).X q ≅ M.X q ⊞ M.X (q + 1))
        (T : ∀ n : ℕ, D (n + 1) ⟶ D n)
        (j : ∀ n : ℕ, 𝟭 (CochainComplex C ℤ) ⟶ D n)
        (sD : ∀ n : ℕ, (D n).CommShift ℤ)
        (sF : ∀ n : ℕ, (F n).CommShift ℤ)
        (κ : ∀ n : ℕ, D n ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ F n)
        (Φ : ∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B),
          (D n).obj (CochainComplex.mappingCone f) ≅
            CochainComplex.mappingCone ((D n).map f)),
        (∀ (n : ℕ) (M : CochainComplex C ℤ) (q : ℤ),
          χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (hobj n M)) ≪≫
            principalConeCoordinates ((chainAction (μ n)).app M) q) ∧
        (∀ (n : ℕ) {M N : CochainComplex C ℤ} (g : M ⟶ N) (q : ℤ),
          ((D n).map g).f q ≫ (χ n N q).hom =
            (χ n M q).hom ≫ biprod.map (g.f q) (g.f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex C ℤ) (q : ℤ),
          ((T n).app M).f q ≫ (χ n M q).hom =
            (χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
              (((chainAction a).app M).f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex C ℤ) (q : ℤ),
          ((j n).app M).f q ≫ (χ n M q).hom = biprod.inl) ∧
        (∀ (n : ℕ) (M : CochainComplex C ℤ),
          (j (n + 1)).app M ≫ (T n).app M = (j n).app M) ∧
        (∀ (n : ℕ) {M N : CochainComplex C ℤ} (g : M ⟶ N),
          QuasiIso g → QuasiIso ((D n).map g)) ∧
        (∀ n : ℕ, (F n).Additive ∧
          @Functor.IsTriangulated _ _ _ _ _ _ (F n)
            (sF n) _ _ _ _ _ _ _ _) ∧
        (∀ (n : ℕ) (M : CochainComplex C ℤ),
          DerivedCategory.Q.map ((T n).app M) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫ step n M) ∧
        (∀ (n : ℕ) (M : CochainComplex C ℤ),
          DerivedCategory.Q.map ((j n).app M) ≫ (κ n).hom.app M =
            unit n M) ∧
        (∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B) (q : ℤ),
          (Φ n f).hom.f q ≫ (principalConeCoordinates ((D n).map f) q).hom ≫
              biprod.map (χ n B q).hom (χ n A (q + 1)).hom =
            (χ n (CochainComplex.mappingCone f) q).hom ≫
              biprod.map (principalConeCoordinates f q).hom
                (principalConeCoordinates f (q + 1)).hom ≫
              principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
                (A.X (q + 1 + 1))) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex C ℤ) (q : ℤ),
          ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M).f q ≫
              (((D n).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
              (χ n M (q + r)).hom =
            (χ n (M⟦r⟧) q).hom ≫
              biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
                (r.negOnePow •
                  (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
                    (add_right_comm q r 1)).hom)) ∧
        (∀ (n : ℕ) {A B A' B' : CochainComplex C ℤ}
          (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
          (h : f ≫ b = a ≫ f')
          (h' : (D n).map f ≫ (D n).map b = (D n).map a ≫ (D n).map f'),
          (D n).map (CochainComplex.mappingCone.map f f' a b h) ≫ (Φ n f').hom =
            (Φ n f).hom ≫ CochainComplex.mappingCone.map
              ((D n).map f) ((D n).map f') ((D n).map a) ((D n).map b) h') ∧
        (∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B),
          (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
              ((D (n + 1)).map f) ((D n).map f) ((T n).app A) ((T n).app B)
              ((T n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex C ℤ),
          (T n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
              ((T n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.inr ((D n).map f)) ∧
        (∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
              (Functor.commShiftIso (self := sD n) (D n) (1 : ℤ)).hom.app A =
            (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((D n).map f)).mor₃) ∧
        (∀ (n : ℕ) {A B : CochainComplex C ℤ} (f : A ⟶ B),
          (j n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.map f ((D n).map f) ((j n).app A) ((j n).app B)
              ((j n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex C ℤ),
          (j n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            ((j n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex C ℤ),
          DerivedCategory.Q.map
              ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M) ≫
              (DerivedCategory.Q.commShiftIso r).hom.app ((D n).obj M) ≫
              ((κ n).hom.app M)⟦r⟧' =
            (κ n).hom.app (M⟦r⟧) ≫
              (F n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
              (Functor.commShiftIso (self := sF n) (F n) r).hom.app
                (DerivedCategory.Q.obj M)) := by
  refine ⟨fun n ↦ strictCone (chainAction (μ n)), fun _ _ ↦ rfl,
    fun n M q ↦ principalConeCoordinates ((chainAction (μ n)).app M) q,
    fun n ↦ strictConeMap _ _ (chainAction a) (hs n),
    fun n ↦ strictConeUnit _, fun n ↦ strictConeShift (μ n),
    sF, κ, fun n _ _ f ↦ strictInterchange (μ n) f, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hF, hT, hj, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intros
    simp
  · intro n M N g q
    exact coneMap_coordinates _ _ g g ((chainAction (μ n)).naturality g).symm q
  · intro n M q
    dsimp only [strictConeMap, strictCone, chainAction, Functor.id_obj]
    simpa only [HomologicalComplex.id_f] using
      coneMap_coordinates (A := M) (B := M) (A' := M) (B' := M)
        _ _ ((chainAction a).app M) (𝟙 M) ((Category.comp_id _).trans (hs n M)) q
  · intro n M q
    exact coneInr_coordinates _ q
  · intro n M
    exact strictConeUnit_map _ _ _ (hs n) M
  · intro n M N g hg
    exact strictCone_quasiIso _ g hg
  · intro n A B f q
    exact strictInterchange_coordinates (μ n) f q
  · intro n r M q
    exact strictConeShift_coordinates (μ n) r M q
  · intro n A B A' B' f f' a b h h'
    exact strictInterchange_natural (μ n) f f' a b h h'
  · intro n A B f
    exact strictInterchange_row _ _ _ (hs n) f
  · intro n r M
    exact strictConeMap_shift _ _ _ (hs n) r M
  · intro n A B f
    exact strictInterchange_inr (μ n) f
  · intro n A B f
    exact strictInterchange_boundary (μ n) f
  · intro n A B f
    exact strictInterchange_unit (μ n) f
  · intro n r M
    exact strictConeUnit_shift (μ n) r M
  · intro n r M
    exact (congrArg (fun z ↦ DerivedCategory.Q.map z ≫
      (DerivedCategory.Q.commShiftIso r).hom.app
        ((strictCone (chainAction (μ n))).obj M) ≫
        ((κ n).hom.app M)⟦r⟧') (strictShift_eq (μ n) r M)).trans (hκ n r M)

namespace PrincipalReduction

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- Multiplication by the (n+1)-st power of the specified uniformizer on a complex.
Source: blueprint Cones paragraph and the scalar construction in the resolution
(auxiliary; not a blueprint node). -/
abbrev scalar (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (n : ℕ)
    (M : CochainComplex (AdicCompletion.Modules l E X) ℤ) : M ⟶ M :=
  DerivedNakayama.scalarOnComplex l E X (d ^ (n + 1)) M

/-- The canonical derived reduction followed by integral scalar restriction.
Source: blueprint Cones paragraph, underlying integral-module reductions
(auxiliary; not a blueprint node). -/
abbrev reductionFunctor (n : ℕ) : DerivedCategory (AdicCompletion.Modules l E X) ⥤
    DerivedCategory (AdicCompletion.Modules l E X) :=
  AdicCompletion.derivedReduction l E X n ⋙ AdicCompletion.restrict l E X n

open AlgebraicGeometry.ProEtale.AdicCompletion

private def uniformizerMap : DerivedNakayama.integerRing l E ⟶ DerivedNakayama.integerRing l E := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine ⟨{ app := fun S ↦ ?_, naturality := ?_ }⟩
  · exact AddCommGrpCat.ofHom
      { toFun := fun f ↦ ULift.up
          (ContinuousMap.const S.unop (Padic.coefficientExtensionUniformizer l E) * f.down)
        map_zero' := by apply ULift.ext; exact mul_zero _
        map_add' := by intro f g; apply ULift.ext; exact mul_add _ _ _ }
  · intro S T f
    rfl

private def uniformizerEnd : End (Mod.regular (DerivedNakayama.integerRing l E)) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  refine .of (Mod.homMk (uniformizerMap l E) ?_)
  change MonObj.mul ≫ uniformizerMap l E =
    DerivedNakayama.integerRing l E ◁ uniformizerMap l E ≫ MonObj.mul
  apply Sheaf.tensor_hom_ext
  simp only [Functor.map_comp]
  rw [← Category.assoc, Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  rw [← Functor.LaxMonoidal.μ_natural_right_assoc,
    Sheaf.μ_sheafToPresheaf_comp_map_mul_sheafCompose]
  apply NatTrans.ext
  funext S
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.toIntLinearMap_injective
  apply TensorProduct.ext'
  intro f g
  apply ULift.ext
  apply ContinuousMap.ext
  intro x
  change Padic.coefficientExtensionUniformizer l E * (f.down x * g.down x) =
    f.down x * (Padic.coefficientExtensionUniformizer l E * g.down x)
  ring

private theorem uniformizerEnd_apply (S : Profinite.{u}ᵒᵖ)
    (f : (DerivedNakayama.integerRing l E).obj.obj S) (x : S.unop) :
    (((uniformizerEnd l E).asHom.hom.hom.app S) f).down x =
      Padic.coefficientExtensionUniformizer l E * f.down x := by
  rfl

private theorem uniformizer_exists :
    ∃ d : End (Mod.regular (DerivedNakayama.integerRing l E)),
      ∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
        (x : S.unop), ((d.asHom.hom.hom.app S) a).down x =
          Padic.coefficientExtensionUniformizer l E * a.down x :=
  ⟨uniformizerEnd l E, uniformizerEnd_apply l E⟩

private abbrev action (d : End (Mod.regular (DerivedNakayama.integerRing l E))) :
    𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ 𝟭 _ :=
  chainAction (DerivedNakayama.scalarOnModules l E X d)

private theorem action_mul
    (a b : End (Mod.regular (DerivedNakayama.integerRing l E)))
    (M : CochainComplex (Modules l E X) ℤ) :
    (action l E X (a * b)).app M =
      (action l E X b).app M ≫ (action l E X a).app M := by
  have h : DerivedNakayama.scalarOnModules l E X (a * b) =
      DerivedNakayama.scalarOnModules l E X b ≫
        DerivedNakayama.scalarOnModules l E X a := by
    unfold DerivedNakayama.scalarOnModules
    simp only [End.mul_asHom, Functor.map_comp, Category.assoc,
      Iso.hom_inv_id_assoc]
    simp only [← Functor.map_comp_assoc]
    congr 2
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp]
  apply HomologicalComplex.hom_ext
  intro i
  exact congrArg (fun z ↦ z.app (M.X i)) h

attribute [local irreducible] DerivedNakayama.scalarOnModules uniformizerEnd

private theorem action_succ
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (n : ℕ)
    (M : CochainComplex (Modules l E X) ℤ) :
    (action l E X (d ^ (n + 1 + 1))).app M =
      (action l E X d).app M ≫ (action l E X (d ^ (n + 1))).app M := by
  rw [pow_succ, action_mul]

/-- Strict principal reductions, with the signed cone and shift comparisons and their
canonical derived interpretation, simultaneously at all positive levels.

Stacks Tag 014E, definition-cone
(auxiliary; not a blueprint node).

Proof plan (the ten steps of the node):
1. Use the scalar differential (dx + pi^(n+1)y,-dy). Diagonal maps are functorial;
   (x,pi y) is a chain map by pi^(n+1)pi=pi^(n+2), and (m,0) is the coaugmentation.
2. Morphisms of scalar cone triangles and lem-sf-triangle-morphism-iso show
   quasi-isomorphism preservation. Localization descends the functor and its maps;
   the direct-sum coordinates prove additivity after localization.
3. The two-term resolution of lemma-reduction-derived-nakayama--1 has flat rank-one
   terms; lem-weil-pbc-independent-bounded-flat-kflat makes it K-flat.
4. Resolve M using lem-pc-kflat-resolution. The signed tensor interchange identifies
   its tensor with that two-term resolution with this scalar cone. The localization
   and transformation-extension clauses of lem-weil-pbc-site-derived-tensor-descent
   give one natural comparison on all unbounded complexes.
5. Lift coefficient transitions by (pi,id) and reduction by the degree-zero identity.
   Tensoring identifies them with the specified transition and coaugmentation, so
   their localizations are the canonical maps of definition-derived-adic-completeness.
6. Expand the four-coordinate differentials. The map (b,a,b',a') to (b,b',a,-a')
   is a chain isomorphism with inverse (u,v,w,z) to (u,w,v,-z).
7. The shift differential is (-1)^r d. The map (x,y) to (x,(-1)^r y) intertwines
   the differentials, is its own inverse, and is coherent under addition of integers.
8. Diagonal chain maps commute with both formulas. Multiplication by pi on the
   second coordinate commutes with the permutation and sign, giving all tower squares.
9. Cone inclusion becomes inclusion; the negative-projection boundary becomes
   (-a,a') after the shift comparison. Coaugmentations become the cone map of the
   two coaugmentations and the shifted coaugmentation, respectively.
10. The cone and boundary squares identify images of cone triangles with cone
    triangles. Every distinguished derived triangle has a cone representative, so
    the localized functor with this shift structure is additive and exact. -/
theorem principal_reduction_cone_calculus :
    ∃ d : End (Mod.regular (DerivedNakayama.integerRing l E)),
      (∀ (S : Profinite.{u}ᵒᵖ) (a : (DerivedNakayama.integerRing l E).obj.obj S)
        (s : S.unop), ((d.asHom.hom.hom.app S) a).down s =
          Padic.coefficientExtensionUniformizer l E * a.down s) ∧
      ∃ (D : ℕ → CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ)
        (hobj : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          (D n).obj M = CochainComplex.mappingCone (scalar l E X d n M))
        (χ : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((D n).obj M).X q ≅ M.X q ⊞ M.X (q + 1))
        (T : ∀ n : ℕ, D (n + 1) ⟶ D n)
        (j : ∀ n : ℕ, 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ D n)
        (sD : ∀ n : ℕ, (D n).CommShift ℤ)
        (sF : ∀ n : ℕ, (reductionFunctor l E X n).CommShift ℤ)
        (κ : ∀ n : ℕ, D n ⋙ DerivedCategory.Q ≅
          DerivedCategory.Q ⋙ reductionFunctor l E X n)
        (Φ : ∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).obj (CochainComplex.mappingCone f) ≅
            CochainComplex.mappingCone ((D n).map f)),
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (hobj n M)) ≪≫
            principalConeCoordinates (scalar l E X d n M) q) ∧
        (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N) (q : ℤ),
          ((D n).map g).f q ≫ (χ n N q).hom =
            (χ n M q).hom ≫ biprod.map (g.f q) (g.f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((T n).app M).f q ≫ (χ n M q).hom =
            (χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
              ((DerivedNakayama.scalarOnComplex l E X d M).f (q + 1))) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((j n).app M).f q ≫ (χ n M q).hom = biprod.inl) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          (j (n + 1)).app M ≫ (T n).app M = (j n).app M) ∧
        (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N),
          QuasiIso g → QuasiIso ((D n).map g)) ∧
        (∀ n : ℕ, (reductionFunctor l E X n).Additive ∧
          @Functor.IsTriangulated _ _ _ _ _ _ (reductionFunctor l E X n)
            (sF n) _ _ _ _ _ _ _ _) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map ((T n).app M) ≫ (κ n).hom.app M =
            (κ (n + 1)).hom.app M ≫ integralStep l E X (DerivedCategory.Q.obj M) n) ∧
        (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map ((j n).app M) ≫ (κ n).hom.app M =
            (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app
              (DerivedCategory.Q.obj M)) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B) (q : ℤ),
          (Φ n f).hom.f q ≫ (principalConeCoordinates ((D n).map f) q).hom ≫
              biprod.map (χ n B q).hom (χ n A (q + 1)).hom =
            (χ n (CochainComplex.mappingCone f) q).hom ≫
              biprod.map (principalConeCoordinates f q).hom
                (principalConeCoordinates f (q + 1)).hom ≫
              principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
                (A.X (q + 1 + 1))) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
          ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M).f q ≫
              (((D n).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
              (χ n M (q + r)).hom =
            (χ n (M⟦r⟧) q).hom ≫
              biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
                (r.negOnePow •
                  (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
                    (add_right_comm q r 1)).hom)) ∧
        (∀ (n : ℕ) {A B A' B' : CochainComplex (Modules l E X) ℤ}
          (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
          (h : f ≫ b = a ≫ f')
          (h' : (D n).map f ≫ (D n).map b = (D n).map a ≫ (D n).map f'),
          (D n).map (CochainComplex.mappingCone.map f f' a b h) ≫ (Φ n f').hom =
            (Φ n f).hom ≫ CochainComplex.mappingCone.map
              ((D n).map f) ((D n).map f') ((D n).map a) ((D n).map b) h') ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
              ((D (n + 1)).map f) ((D n).map f) ((T n).app A) ((T n).app B)
              ((T n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          (T n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            (Functor.commShiftIso (self := sD (n + 1)) (D (n + 1)) r).hom.app M ≫
              ((T n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.inr ((D n).map f)) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
              (Functor.commShiftIso (self := sD n) (D n) (1 : ℤ)).hom.app A =
            (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((D n).map f)).mor₃) ∧
        (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
          (j n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
            CochainComplex.mappingCone.map f ((D n).map f) ((j n).app A) ((j n).app B)
              ((j n).naturality f)) ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          (j n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (D n) r).hom.app M =
            ((j n).app M)⟦r⟧') ∧
        (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
          DerivedCategory.Q.map
              ((Functor.commShiftIso (self := sD n) (D n) r).hom.app M) ≫
              (DerivedCategory.Q.commShiftIso r).hom.app ((D n).obj M) ≫
              ((κ n).hom.app M)⟦r⟧' =
            (κ n).hom.app (M⟦r⟧) ≫
              (reductionFunctor l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
              (Functor.commShiftIso (self := sF n) (reductionFunctor l E X n) r).hom.app
                (DerivedCategory.Q.obj M)) := by
  refine (uniformizer_exists l E).elim (fun d hd ↦ ?_)
  refine (PrincipalNormalization.derived_principal_normalization l E X d hd
    (action_succ l E X d)).elim (fun sF hsF ↦ ?_)
  refine hsF.elim (fun κ h ↦ ?_)
  refine ⟨d, hd, ?_⟩
  exact strict_calculus
    (fun n ↦ DerivedNakayama.scalarOnModules l E X (d ^ (n + 1)))
    (DerivedNakayama.scalarOnModules l E X d) (action_succ l E X d)
    (reductionFunctor l E X) sF κ
    (fun n M ↦ integralStep l E X (DerivedCategory.Q.obj M) n)
    (fun n M ↦ (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app
      (DerivedCategory.Q.obj M)) h.1 h.2.1 h.2.2.1 h.2.2.2

end PrincipalReduction
end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale.PrincipalReduction

open AlgebraicGeometry.ProEtale.AdicCompletion

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The strict data of the simultaneous principal calculus. Its canonical predicate
also retains all existential comparison data and equations of the node.
Its strict objects, maps, transitions and units are fixed
by the scalar and coordinate equations; the comparisons retain all normalizations.
Source: blueprint first-reduction proof, Cones paragraph; Stacks Tag 014E
(auxiliary; not a blueprint node). -/
structure PrincipalReductionConeData where
  d : End (Mod.regular (DerivedNakayama.integerRing l E))
  D : ℕ → CochainComplex (Modules l E X) ℤ ⥤ CochainComplex (Modules l E X) ℤ
  hobj : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
    (D n).obj M = CochainComplex.mappingCone (scalar l E X d n M)
  χ : ∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
    ((D n).obj M).X q ≅ M.X q ⊞ M.X (q + 1)
  T : ∀ n : ℕ, D (n + 1) ⟶ D n
  j : ∀ n : ℕ, 𝟭 (CochainComplex (Modules l E X) ℤ) ⟶ D n

/-- Exact canonical characterization of the simultaneous principal calculus.
The conjunction is under the scalar test binders. This is equivalent to placing
its remaining clauses outside them: use the one-point profinite test and the zero
section. Keeping these binders shared avoids repeated closed-proof abstraction.
Source: blueprint first-reduction proof, Cones paragraph; Stacks Tag 014E
(auxiliary; not a blueprint node). -/
def PrincipalReductionConeData.IsCanonical (data : PrincipalReductionConeData l E X) : Prop :=
  ∀ (S : Profinite.{u}ᵒᵖ)
    (a : (DerivedNakayama.integerRing l E).obj.obj S) (s : S.unop),
    ((data.d.asHom.hom.hom.app S) a).down s = Padic.coefficientExtensionUniformizer l E * a.down s ∧
    ∃ (sD : ∀ n : ℕ, (data.D n).CommShift ℤ)
      (sF : ∀ n : ℕ, (reductionFunctor l E X n).CommShift ℤ)
      (κ : ∀ n : ℕ, data.D n ⋙ DerivedCategory.Q ≅
        DerivedCategory.Q ⋙ reductionFunctor l E X n)
      (Φ : ∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
        (data.D n).obj (CochainComplex.mappingCone f) ≅
          CochainComplex.mappingCone ((data.D n).map f)),
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      data.χ n M q = eqToIso (congrArg (fun K ↦ K.X q) (data.hobj n M)) ≪≫
        principalConeCoordinates (scalar l E X data.d n M) q) ∧
    (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N) (q : ℤ),
      ((data.D n).map g).f q ≫ (data.χ n N q).hom =
        (data.χ n M q).hom ≫ biprod.map (g.f q) (g.f (q + 1))) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((data.T n).app M).f q ≫ (data.χ n M q).hom =
        (data.χ (n + 1) M q).hom ≫ biprod.map (𝟙 _)
          ((DerivedNakayama.scalarOnComplex l E X data.d M).f (q + 1))) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((data.j n).app M).f q ≫ (data.χ n M q).hom = biprod.inl) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j (n + 1)).app M ≫ (data.T n).app M = (data.j n).app M) ∧
    (∀ (n : ℕ) {M N : CochainComplex (Modules l E X) ℤ} (g : M ⟶ N),
      QuasiIso g → QuasiIso ((data.D n).map g)) ∧
    (∀ n : ℕ, (reductionFunctor l E X n).Additive ∧
      @Functor.IsTriangulated _ _ _ _ _ _ (reductionFunctor l E X n)
        (sF n) _ _ _ _ _ _ _ _) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map ((data.T n).app M) ≫ (κ n).hom.app M =
        (κ (n + 1)).hom.app M ≫ integralStep l E X (DerivedCategory.Q.obj M) n) ∧
    (∀ (n : ℕ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map ((data.j n).app M) ≫ (κ n).hom.app M =
        (Mod.derivedExtendMapDerivedCategoryAdjunction (quotient l E X n)).unit.app
          (DerivedCategory.Q.obj M)) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B) (q : ℤ),
      (Φ n f).hom.f q ≫ (principalConeCoordinates ((data.D n).map f) q).hom ≫
          biprod.map (data.χ n B q).hom (data.χ n A (q + 1)).hom =
        (data.χ n (CochainComplex.mappingCone f) q).hom ≫
          biprod.map (principalConeCoordinates f q).hom
            (principalConeCoordinates f (q + 1)).hom ≫
          principalConeInterchange (B.X q) (A.X (q + 1)) (B.X (q + 1))
            (A.X (q + 1 + 1))) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ) (q : ℤ),
      ((Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M).f q ≫
          (((data.D n).obj M).shiftFunctorObjXIso r q (q + r) rfl).hom ≫
          (data.χ n M (q + r)).hom =
        (data.χ n (M⟦r⟧) q).hom ≫
          biprod.map (M.shiftFunctorObjXIso r q (q + r) rfl).hom
            (r.negOnePow •
              (M.shiftFunctorObjXIso r (q + 1) (q + r + 1)
                (add_right_comm q r 1)).hom)) ∧
    (∀ (n : ℕ) {A B A' B' : CochainComplex (Modules l E X) ℤ}
      (f : A ⟶ B) (f' : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
      (h : f ≫ b = a ≫ f')
      (h' : (data.D n).map f ≫ (data.D n).map b = (data.D n).map a ≫ (data.D n).map f'),
      (data.D n).map (CochainComplex.mappingCone.map f f' a b h) ≫ (Φ n f').hom =
        (Φ n f).hom ≫ CochainComplex.mappingCone.map
          ((data.D n).map f) ((data.D n).map f') ((data.D n).map a) ((data.D n).map b) h') ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.T n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        (Φ (n + 1) f).hom ≫ CochainComplex.mappingCone.map
          ((data.D (n + 1)).map f) ((data.D n).map f) ((data.T n).app A) ((data.T n).app B)
          ((data.T n).naturality f)) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      (data.T n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
        (Functor.commShiftIso (self := sD (n + 1)) (data.D (n + 1)) r).hom.app M ≫
          ((data.T n).app M)⟦r⟧') ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.D n).map (CochainComplex.mappingCone.inr f) ≫ (Φ n f).hom =
        CochainComplex.mappingCone.inr ((data.D n).map f)) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.D n).map (CochainComplex.mappingCone.triangle f).mor₃ ≫
          (Functor.commShiftIso (self := sD n) (data.D n) (1 : ℤ)).hom.app A =
        (Φ n f).hom ≫ (CochainComplex.mappingCone.triangle ((data.D n).map f)).mor₃) ∧
    (∀ (n : ℕ) {A B : CochainComplex (Modules l E X) ℤ} (f : A ⟶ B),
      (data.j n).app (CochainComplex.mappingCone f) ≫ (Φ n f).hom =
        CochainComplex.mappingCone.map f ((data.D n).map f) ((data.j n).app A) ((data.j n).app B)
          ((data.j n).naturality f)) ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      (data.j n).app (M⟦r⟧) ≫ (Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M =
        ((data.j n).app M)⟦r⟧') ∧
    (∀ (n : ℕ) (r : ℤ) (M : CochainComplex (Modules l E X) ℤ),
      DerivedCategory.Q.map
          ((Functor.commShiftIso (self := sD n) (data.D n) r).hom.app M) ≫
          (DerivedCategory.Q.commShiftIso r).hom.app ((data.D n).obj M) ≫
          ((κ n).hom.app M)⟦r⟧' =
        (κ n).hom.app (M⟦r⟧) ≫
          (reductionFunctor l E X n).map ((DerivedCategory.Q.commShiftIso r).hom.app M) ≫
          (Functor.commShiftIso (self := sF n) (reductionFunctor l E X n) r).hom.app
            (DerivedCategory.Q.obj M))

/-- Strict principal reductions, with the signed cone and shift comparisons and their
canonical derived interpretation, simultaneously at all positive levels.

Stacks Tag 014E, definition-cone
(auxiliary; not a blueprint node).

Proof plan (the ten steps of the node):
1. Use the scalar differential (dx + pi^(n+1)y,-dy). Diagonal maps are functorial;
   (x,pi y) is a chain map by pi^(n+1)pi=pi^(n+2), and (m,0) is the coaugmentation.
2. Morphisms of scalar cone triangles and lem-sf-triangle-morphism-iso show
   quasi-isomorphism preservation. Localization descends the functor and its maps;
   the direct-sum coordinates prove additivity after localization.
3. The two-term resolution of lemma-reduction-derived-nakayama--1 has flat rank-one
   terms; lem-weil-pbc-independent-bounded-flat-kflat makes it K-flat.
4. Resolve M using lem-pc-kflat-resolution. The signed tensor interchange identifies
   its tensor with that two-term resolution with this scalar cone. The localization
   and transformation-extension clauses of lem-weil-pbc-site-derived-tensor-descent
   give one natural comparison on all unbounded complexes.
5. Lift coefficient transitions by (pi,id) and reduction by the degree-zero identity.
   Tensoring identifies them with the specified transition and coaugmentation, so
   their localizations are the canonical maps of definition-derived-adic-completeness.
6. Expand the four-coordinate differentials. The map (b,a,b',a') to (b,b',a,-a')
   is a chain isomorphism with inverse (u,v,w,z) to (u,w,v,-z).
7. The shift differential is (-1)^r d. The map (x,y) to (x,(-1)^r y) intertwines
   the differentials, is its own inverse, and is coherent under addition of integers.
8. Diagonal chain maps commute with both formulas. Multiplication by pi on the
   second coordinate commutes with the permutation and sign, giving all tower squares.
9. Cone inclusion becomes inclusion; the negative-projection boundary becomes
   (-a,a') after the shift comparison. Coaugmentations become the cone map of the
   two coaugmentations and the shifted coaugmentation, respectively.
10. The cone and boundary squares identify images of cone triangles with cone
    triangles. Every distinguished derived triangle has a cone representative, so
    the localized functor with this shift structure is additive and exact. -/
theorem principalReductionConeData :
    ∃ data : PrincipalReductionConeData l E X, data.IsCanonical l E X := by
  obtain ⟨d, hd, D, hobj, χ, T, j, sD, sF, κ, Φ, h⟩ :=
    principal_reduction_cone_calculus l E X
  refine ⟨⟨d, D, hobj, χ, T, j⟩, ?_⟩
  intro S a s
  exact ⟨hd S a s, sD, sF, κ, Φ, h⟩

end AlgebraicGeometry.ProEtale.PrincipalReduction

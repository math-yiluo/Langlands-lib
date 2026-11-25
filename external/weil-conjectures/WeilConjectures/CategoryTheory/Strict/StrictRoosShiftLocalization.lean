/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift

/-!
# Signed strict Roos shifts and prescribed localization

Source: Stacks Project, Tag 014E, definition-cone; Tag 011G,
definition-shift-cochain; Tag 04VG, localization universal property
(blueprint: lem-a1-strict-roos-shift-localization).

The strict functor and inclusion are `roosF` and `roosι`. Natural tower index `n`
represents positive index `n+1`. The localization categories, their universes and
localization functors are arbitrary prescribed choices.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uT vT uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open CochainComplex

namespace StrictRoosShiftProof

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

private noncomputable abbrev shiftInclusion [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : limit I.asFunctor ⟶ roosP I :=
  Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))

section LimitModel
variable [HasLimitsOfShape ℕᵒᵖ A]

omit [HasCountableProducts A] in
private lemma baseLimit_additive : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive := by
  constructor
  intro X Y f g
  apply limit.hom_ext
  intro n
  simp [lim_map]

attribute [local instance] baseLimit_additive

private noncomputable def limitModelCone (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    Cone I.asFunctor where
  pt := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) |>.obj I
  π :=
    { app := fun n ↦ (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I
      naturality := by
        intro n m f
        ext q
        change 𝟙 (limit (I.X q)) ≫ limit.π (I.X q) m =
          limit.π (I.X q) n ≫ (I.X q).map f
        rw [Category.id_comp, limit.w] }

private noncomputable def limitModelLimit (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsLimit (limitModelCone I) := by
  apply HomologicalComplex.isLimitOfEval
  intro q
  exact limit.isLimit (I.X q)

private noncomputable def limitModelPointIso (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).obj I ≅
      limit I.asFunctor :=
  (limitModelLimit I).conePointUniqueUpToIso (limit.isLimit I.asFunctor)

omit [HasCountableProducts A] in
private lemma limitModelPointIso_hom_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    (limitModelPointIso I).hom ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limitModelLimit I) (limit.isLimit I.asFunctor) n

private noncomputable def limitModelIso :
    (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) ≅
      roosLimitFunctor :=
  NatIso.ofComponents limitModelPointIso (by
    intro X Y f
    dsimp only [roosLimitFunctor, Functor.comp_map,
      HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    apply limit.hom_ext
    intro n
    dsimp only [HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
    simp only [Category.assoc, limitModelPointIso_hom_π, lim_map, limMap_π]
    rw [← Category.assoc, limitModelPointIso_hom_π]
    exact (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).naturality f)

@[instance_reducible]
private noncomputable def limitShift : (roosLimitFunctor (A := A)).CommShift ℤ :=
  Functor.CommShift.ofIso limitModelIso ℤ

omit [HasCountableProducts A] in
private lemma limitModel_hom_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕᵒᵖ) :
    limitModelIso.hom.app I ≫ limit.π I.asFunctor n =
      (NatTrans.mapHomologicalComplex (lim.π n) (.up ℤ)).app I :=
  limitModelPointIso_hom_π I n

omit [HasCountableProducts A] in
private lemma limitShift_π (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m q : ℤ) (n : ℕ) :
    ((Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I).f q ≫
      (CochainComplex.shiftFunctorObjXIso (limit I.asFunctor) m q (q + m) rfl).hom ≫
        (limit.π I.asFunctor (op n)).f (q + m) =
      (limit.π (I⟦m⟧).asFunctor (op n)).f q ≫
        ((I.shiftFunctorObjXIso m q (q + m) rfl).hom).app (op n) := by
  simp only [roosLimitFunctor, Functor.comp_obj,
    HomologicalComplex.complexOfFunctorsToFunctorToComplex_obj]
  change (((Functor.CommShift.ofIso limitModelIso ℤ).commShiftIso m).hom.app I).f q ≫ _ = _
  rw [Functor.CommShift.ofIso_commShiftIso_hom_app]
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
    shiftFunctor_map_f', shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, NatTrans.id_app]
  have h := congrArg (fun f ↦ f.f (q + m)) (limitModel_hom_π I (op n))
  simp only [HomologicalComplex.comp_f] at h
  erw [Category.assoc, Category.id_comp, Category.comp_id, Category.id_comp, h]
  have h' := congrArg (fun f ↦ f.f q)
    ((limitModelIso.app (I⟦m⟧)).inv_hom_id_assoc
      (limit.π (I⟦m⟧).asFunctor (op n)))
  simp only [Iso.app_hom, Iso.app_inv, HomologicalComplex.comp_f] at h'
  rw [← h']
  congr 1
  exact (congrArg (fun f ↦ f.f q)
    (limitModel_hom_π (I⟦m⟧) (op n))).symm

end LimitModel

private noncomputable abbrev π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :=
  (Pi.π (fun n : ℕ ↦ N.asFunctor.obj (op n)) n).f q

private noncomputable abbrev v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :=
  (roosProj N).f q

private noncomputable abbrev ucoord (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (q p : ℤ) (h : q - 1 = p) : (roosF.obj N).X q ⟶ (roosP N).X p :=
  (mappingCocone.snd (roosU N)).v q p (by omega)

private noncomputable abbrev levelFunctor (n : ℕ) :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ where
  obj N := N.asFunctor.obj (op n)
  map f := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n)
  map_id N := by ext q; rfl
  map_comp f g := by ext q; rfl

@[instance_reducible]
private noncomputable def levelCommShift (n : ℕ) :
    (levelFunctor (A := A) n).CommShift ℤ := by
  change (((evaluation ℕᵒᵖ A).obj (op n)).mapHomologicalComplex
    (ComplexShape.up ℤ)).CommShift ℤ
  infer_instance

attribute [local instance] levelCommShift

omit [HasCountableProducts A] in
private theorem levelShift_f (n : ℕ) (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) :
    ((Functor.commShiftIso (levelFunctor (A := A) n)
      (self := levelCommShift n) r).hom.app N).f q =
      𝟙 ((N.X (q + r)).obj (op n)) := by
  rfl

private noncomputable abbrev productFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  ProductShift.productFunctor (levelFunctor (A := A))

@[instance_reducible]
private noncomputable def productShift : (productFunctor (A := A)).CommShift ℤ :=
  ProductShift.productCommShift (levelFunctor (A := A))

attribute [local instance] productShift

private noncomputable def productShiftComponent
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosP (N⟦r⟧)).X q ⟶ (roosP N).X (q + r) :=
  (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q

private theorem productShiftComponent_eq
    (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    productShiftComponent N r q =
      (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom.f q := rfl

private theorem productShift_hom_f (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m q : ℤ) :
    ((Functor.commShiftIso productFunctor (self := productShift) m).hom.app I).f q =
      (ProductShift.productShiftIso (levelFunctor (A := A)) I m).hom.f q := rfl

private theorem productShift_π (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r q : ℤ) (n : ℕ) :
    productShiftComponent N r q ≫
        π N (q + r) n =
      π (N⟦r⟧) q n ≫
        ((shiftFunctorObjXIso N r q (q + r) rfl).hom).app (op n) := by
  have h := congrArg (fun k ↦ k.f q)
    (ProductShift.productShiftIso_π (levelFunctor (A := A)) N r n)
  simp only [HomologicalComplex.comp_f, levelShift_f] at h
  erw [Category.comp_id] at h
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, NatTrans.id_app]
  erw [Category.comp_id]
  simpa only [productShiftComponent, π, shiftFunctor_map_f'] using h

attribute [local irreducible] productShiftComponent

private noncomputable def transitionEndomorphism : productFunctor (A := A) ⟶ productFunctor where
  app := roosU
  naturality _ _ f := (roosU_natural f).symm

private theorem transitionEndomorphism_shift :
    NatTrans.CommShift (transitionEndomorphism (A := A)) ℤ := by
  constructor
  intro r
  apply NatTrans.ext
  funext N
  change (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom ≫
      (roosU N)⟦r⟧' =
    roosU (N⟦r⟧) ≫ (ProductShift.productShiftIso (levelFunctor (A := A)) N r).hom
  apply ProductShift.productShift_hom_ext (levelFunctor (A := A)) N r
  intro n
  rw [Category.assoc, ← Functor.map_comp]
  have hu (M : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (n : ℕ) :
      roosU M ≫ Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n =
        Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) n -
          Pi.π (fun n : ℕ ↦ M.asFunctor.obj (op n)) (n + 1) ≫
            M.asFunctor.map (homOfLE (Nat.le_succ n)).op :=
    (towerTransitionEndomorphism_eq_iff
      (K := fun n : ℕ ↦ M.asFunctor.obj (op n))
      (fun n : ℕ ↦ M.asFunctor.map (homOfLE (Nat.le_succ n)).op) _).mp rfl n
  erw [hu]
  rw [Category.assoc, ProductShift.productShiftIso_π]
  simp only [Functor.map_sub, Functor.map_comp, Preadditive.comp_sub]
  erw [ProductShift.productShiftIso_π, ProductShift.productShiftIso_π_assoc]
  conv_rhs => erw [← Category.assoc, hu]
  simp only [Preadditive.sub_comp, Category.assoc]
  congr 1
  ext q
  simp [HomologicalComplex.comp_f, shiftFunctor_map_f', levelShift_f, levelFunctor]

attribute [local instance] transitionEndomorphism_shift

private noncomputable abbrev signedFunctor :
    CochainComplex (ℕᵒᵖ ⥤ A) ℤ ⥤ CochainComplex A ℤ :=
  SignedCoconeShift.coconeFunctor productFunctor productFunctor transitionEndomorphism

@[instance_reducible]
private noncomputable def signedCommShift : (signedFunctor (A := A)).CommShift ℤ :=
  SignedCoconeShift.coconeCommShift _ _ _

omit [HasCountableProducts A] in
private theorem cofiberMap_eq_coneMap
    {K L K' L' : CochainComplex A ℤ} (s : K ⟶ L) (s' : K' ⟶ L')
    (a : K ⟶ K') (b : L ⟶ L') (h : s ≫ b = a ≫ s') :
    HomologicalComplex.homotopyCofiber.mapArrowHom s s'
      (fun j ↦ ⟨j - 1, Int.sub_add_cancel j 1⟩) (Arrow.homMk a b h.symm) =
      mappingCone.map s s' a b h := by
  ext i
  apply HomologicalComplex.homotopyCofiber.ext_from_X s (i + 1) i rfl
  all_goals simp [HomologicalComplex.homotopyCofiber.mapArrowHom,
    HomologicalComplex.homotopyCofiber.desc_f,
    HomologicalComplex.homotopyCofiber.inrCompHomotopy_hom,
    mappingCone.map, mappingCone.desc, mappingCone.descCochain,
    HomComplex.Cochain.comp_v, mappingCone.inl, mappingCone.fst, mappingCone.snd,
    mappingCone.inr]

private noncomputable def signedRoosIso : signedFunctor (A := A) ≅ roosF :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro N N' f
    simp only [Iso.refl_hom, Category.comp_id, Category.id_comp]
    exact congrArg ((CategoryTheory.shiftFunctor (CochainComplex A ℤ) (-1 : ℤ)).map)
      (cofiberMap_eq_coneMap (roosU N) (roosU N')
        (roosPmap f) (roosPmap f) (roosU_natural f)))

@[instance_reducible]
private noncomputable def roosCommShift : (roosF (A := A)).CommShift ℤ := by
  let := signedCommShift (A := A)
  exact Functor.CommShift.ofIso signedRoosIso ℤ

private noncomputable def roosShiftMap (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosF.obj (N⟦r⟧) ⟶ (roosF.obj N)⟦r⟧ :=
  (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N

private theorem roosShiftMap_eq (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (Functor.commShiftIso roosF (self := roosCommShift (A := A)) r).hom.app N := rfl

attribute [local irreducible] roosShiftMap

private theorem roosShift_hom (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r : ℤ) :
    roosShiftMap N r =
      (SignedCoconeShift.coconeFunctorShiftIso productFunctor productFunctor
        transitionEndomorphism N r).hom := by
  rw [roosShiftMap_eq]
  let := signedCommShift (A := A)
  change ((Functor.CommShift.ofIso signedRoosIso ℤ).commShiftIso r).hom.app N = _
  simp only [Functor.CommShift.ofIso_commShiftIso_hom_app, signedRoosIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app, Iso.refl_hom,
    Iso.refl_inv, Functor.map_id, Category.comp_id]
  erw [Category.id_comp]
  rfl

attribute [local irreducible] roosCommShift

@[reassoc]
private theorem roosShift_inl (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (mappingCocone.inl (roosU (N⟦r⟧))).v q q (add_zero q) ≫
        (roosShiftMap N r).f q =
      productShiftComponent N r q ≫
        (mappingCocone.inl (roosU N)).v (q + r) (q + r) (add_zero _) ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inl
    productFunctor productFunctor transitionEndomorphism N r q

@[reassoc]
private theorem roosShift_inr (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (r p q : ℤ) (h : p + 1 = q) :
    (mappingCocone.inr (roosU (N⟦r⟧))).1.v p q h ≫
        (roosShiftMap N r).f q =
      r.negOnePow •
        (productShiftComponent N r p ≫
          (mappingCocone.inr (roosU N)).1.v (p + r) (q + r) (by omega) ≫
          (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).inv) := by
  rw [roosShift_hom, productShiftComponent_eq]
  exact SignedCoconeShift.coconeFunctorShiftIso_inr
    productFunctor productFunctor transitionEndomorphism N r p q h

private theorem v_eq_fst (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    v N q = (mappingCocone.fst (roosU N)).f q := rfl

@[reassoc]
private theorem roosShift_v (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫ v N (q + r) =
      v (N⟦r⟧) q ≫
        productShiftComponent N r q := by
  simp only [v_eq_fst]
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_fst_f, mappingCocone.inl_v_fst_f_assoc,
      Category.comp_id]
  · rw [roosShift_inr_assoc]
    simp only [Category.assoc, Linear.units_smul_comp,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_fst_f, mappingCocone.inr_v_fst_f_assoc,
      comp_zero, zero_comp, smul_zero]

@[reassoc]
private theorem roosShift_u (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (r q : ℤ) :
    (roosShiftMap N r).f q ≫
        (shiftFunctorObjXIso (roosF.obj N) r q (q + r) rfl).hom ≫
        ucoord N (q + r) ((q - 1) + r) (by omega) =
      r.negOnePow • (ucoord (N⟦r⟧) q (q - 1) rfl ≫
        productShiftComponent N r (q - 1)) := by
  apply SignedCoconeShift.cocone_ext_from (roosU (N⟦r⟧)) q
  · rw [roosShift_inl_assoc]
    simp only [ucoord, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inl_v_snd_v, mappingCocone.inl_v_snd_v_assoc,
      comp_zero, zero_comp, smul_zero]
  · rw [roosShift_inr_assoc]
    simp only [ucoord, Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul,
      Iso.inv_hom_id_assoc,
      mappingCocone.inr_v_snd_v, mappingCocone.inr_v_snd_v_assoc,
      Category.comp_id]

private noncomputable def productLimit (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) :
    IsLimit (Fan.mk ((roosP N).X q) (π N q)) :=
  isLimitOfHasProductOfPreservesLimit
    (HomologicalComplex.eval A (ComplexShape.up ℤ) q)
    (fun n : ℕ ↦ N.asFunctor.obj (op n))

private theorem product_ext (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ)
    {T : A} {f g : T ⟶ (roosP N).X q}
    (h : ∀ n : ℕ, f ≫ π N q n = g ≫ π N q n) : f = g := by
  apply (productLimit N q).hom_ext
  rintro ⟨n⟩
  exact h n

private theorem roos_ext_at {N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {T : A} (q p : ℤ) (hp : q - 1 = p) {f g : T ⟶ (roosF.obj N).X q}
    (hv : f ≫ v N q = g ≫ v N q)
    (hu : f ≫ ucoord N q p hp = g ≫ ucoord N q p hp) : f = g := by
  have hid := mappingCocone.id_X (roosU N) q p (by omega)
  change v N q ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
    ucoord N q p hp ≫
      (mappingCocone.inr (roosU N)).1.v p q (by omega) = 𝟙 _ at hid
  calc
    f = f ≫ 𝟙 _ := (Category.comp_id _).symm
    _ = f ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by rw [hid]
    _ = g ≫ ((v N q) ≫ (mappingCocone.inl (roosU N)).v q q (add_zero q) +
        ucoord N q p hp ≫
          (mappingCocone.inr (roosU N)).1.v p q (by omega)) := by
      simp only [Preadditive.comp_add, ← Category.assoc, hv, hu]
    _ = g := by rw [hid, Category.comp_id]

variable [HasLimitsOfShape ℕᵒᵖ A]

private lemma roosι_u (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q p : ℤ)
    (h : q - 1 = p) : (roosι I).f q ≫ ucoord I q p h = 0 := by
  simp [roosι, roosLift, ucoord]

private lemma inclusion_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    shiftInclusion (I⟦m⟧) ≫
        (Functor.commShiftIso productFunctor (self := productShift) m).hom.app I =
      (Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I ≫
        (shiftInclusion I)⟦m⟧' := by
  ext q
  apply product_ext I (q + m)
  intro n
  simp only [HomologicalComplex.comp_f, shiftFunctor_map_f', Category.assoc]
  rw [productShift_hom_f, ← productShiftComponent_eq, productShift_π]
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (q : ℤ) (n : ℕ) :
      (shiftInclusion I).f q ≫ π I q n =
        (limit.π I.asFunctor (op n)).f q :=
    congrArg (fun f ↦ f.f q) (Pi.lift_comp_π (fun n : ℕ ↦ limit.π I.asFunctor (op n)) n)
  simp only [← Category.assoc, hi]
  have h := limitShift_π I m q n
  erw [Category.id_comp] at h
  exact h.symm

private lemma augmentation_shift (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (m : ℤ) :
    roosι (I⟦m⟧) ≫ roosShiftMap I m =
      (Functor.commShiftIso roosLimitFunctor (self := limitShift) m).hom.app I ≫
        (roosι I)⟦m⟧' := by
  ext q
  apply roos_ext_at (q + m) ((q - 1) + m) (by omega)
  · have hv := roosShift_v I m q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hv
    erw [Category.id_comp] at hv
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [hv]
    have hi := congrArg (fun f ↦ f.f q) (inclusion_shift I m)
    simp only [HomologicalComplex.comp_f, shiftFunctor_map_f'] at hi
    have hf (N : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (j : ℤ) :
        (roosι N).f j ≫ (mappingCocone.fst (roosU N)).f j =
          (shiftInclusion N).f j :=
      by simp [roosι, roosLift, shiftInclusion]
    simp only [v_eq_fst, ← Category.assoc, hf, productShiftComponent_eq]
    simpa only [productShift_hom_f] using hi
  · have hu := roosShift_u I m q
    simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom] at hu
    erw [Category.id_comp] at hu
    simp only [HomologicalComplex.comp_f, Category.assoc, shiftFunctor_map_f']
    erw [hu]
    simp only [Linear.comp_units_smul, ← Category.assoc, roosι_u,
      zero_comp, smul_zero, comp_zero]

end StrictRoosShiftProof

open StrictRoosShiftProof

end CategoryTheory

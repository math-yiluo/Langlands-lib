/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import WeilConjectures.CategoryTheory.DerivedExactSquareComposition
import WeilConjectures.CategoryTheory.Integral.IntegralResidueMatePasting

/-! # Composition and unit of the system coefficient mate

Source: Zheng, Constructions 4.1 and 5.14--5.15, Lemma 5.16; Stacks Tag 0GL6.
-/

@[expose] public noncomputable section

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale.SystemProjection

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
private theorem scalar_mate_unit
    {A B : Type*} [Category A] [Category B]
    {L : A ⥤ A} {R : A ⥤ A} {S : B ⥤ B} {T : B ⥤ B}
    (a : L ⊣ R) (b : S ⊣ T) (F : A ⥤ B)
    (r : R ⋙ F ⟶ F ⋙ T) (δ : R ≅ 𝟭 A) (ε : T ≅ 𝟭 B)
    (h : ∀ N, F.map (δ.inv.app N) ≫ r.app N = ε.inv.app (F.obj N)) (M : A) :
    ((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).app M ≫
        F.map (((a.ofNatIsoRight δ).leftAdjointUniq Adjunction.id).hom.app M) =
      ((b.ofNatIsoRight ε).leftAdjointUniq Adjunction.id).hom.app (F.obj M) := by
  let i := (a.ofNatIsoRight δ).leftAdjointUniq Adjunction.id
  let j := (b.ofNatIsoRight ε).leftAdjointUniq Adjunction.id
  have hi : a.unit.app M ≫ R.map (i.hom.app M) = δ.inv.app M := by
    have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (a.ofNatIsoRight δ) Adjunction.id M
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at ht
    apply (cancel_mono (δ.hom.app M)).1
    simpa only [i, Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Iso.inv_hom_id_app,
      Category.assoc] using ht
  have hj : b.unit.app (F.obj M) ≫ T.map (j.hom.app (F.obj M)) =
      ε.inv.app (F.obj M) := by
    have ht := Adjunction.homEquiv_leftAdjointUniq_hom_app
      (b.ofNatIsoRight ε) Adjunction.id (F.obj M)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.homEquiv_unit] at ht
    apply (cancel_mono (ε.hom.app (F.obj M))).1
    simpa only [j, Functor.id_obj, Adjunction.id_unit, NatTrans.id_app, Iso.inv_hom_id_app,
      Category.assoc] using ht
  have hm := unit_mateEquiv_symm a b (TwoSquare.mk _ _ _ _ r) M
  change F.map (a.unit.app M) ≫ r.app (L.obj M) =
    b.unit.app (F.obj M) ≫
      T.map (((mateEquiv a b).symm (TwoSquare.mk _ _ _ _ r)).app M) at hm
  apply (b.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hm]
  simp only [Category.assoc]
  erw [← r.naturality (i.hom.app M)]
  change F.map (a.unit.app M) ≫ F.map (R.map (i.hom.app M)) ≫ r.app M = _
  rw [← F.map_comp_assoc, hi, h, hj]

set_option backward.defeqAttrib.useBackward true in
private theorem mate_whisker
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {F F' : A ⥤ C} {G G' : B ⥤ D}
    (a : L ⊣ R) (b : L' ⊣ R') (t : TwoSquare F L L' G)
    (f : F' ⟶ F) (g : G ⟶ G') :
    (mateEquiv a b ((t.whiskerTop f).whiskerBottom g)) =
      Functor.whiskerLeft R f ≫ (mateEquiv a b t) ≫
        Functor.whiskerRight g R' := by
  ext N
  simp only [mateEquiv_apply, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Category.id_comp, Functor.map_comp, Category.assoc]
  rw [← b.unit_naturality_assoc]
  simp only [Functor.comp_map]
  have hg := congrArg R'.map (g.naturality (a.counit.app N))
  simp only [R'.map_comp] at hg
  rw [← reassoc_of% hg]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.defeqAttrib.useBackward true in
private theorem mate_identity
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {U : A ⥤ A} {V : B ⥤ B}
    (r : U ⋙ L ⟶ L ⋙ V) (i : U ≅ 𝟭 A) (j : V ≅ 𝟭 B)
    (h : ∀ M, L.map (i.hom.app M) = r.app M ≫ j.hom.app (L.obj M)) (N : B) :
    (mateEquiv a a (TwoSquare.mk _ _ _ _ r)).app N ≫ R.map (j.hom.app N) =
      i.hom.app (R.obj N) := by
  have hr : r.app (R.obj N) ≫ j.hom.app (L.obj (R.obj N)) =
      L.map (i.hom.app (R.obj N)) := (h _).symm
  rw [mateEquiv_apply]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Functor.comp_obj, Functor.comp_map, TwoSquare.mk, Category.id_comp,
    Category.assoc]
  erw [Category.id_comp]
  change a.unit.app (U.obj (R.obj N)) ≫ R.map (r.app (R.obj N)) ≫
    R.map (V.map (a.counit.app N)) ≫ R.map (j.hom.app N) = _
  have hj := j.hom.naturality (a.counit.app N)
  dsimp only [Functor.id_map, Functor.id_obj, Functor.comp_obj] at hj
  rw [← R.map_comp, hj, R.map_comp]
  rw [← R.map_comp_assoc, hr]
  have hu := a.unit.naturality (i.hom.app (R.obj N))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.id_obj, Functor.comp_obj] at hu
  rw [← reassoc_of% hu]
  rw [a.right_triangle_components, Category.comp_id]

set_option backward.defeqAttrib.useBackward true in
private theorem inverseMate_identity
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (a : L ⊣ R) {F : A ⥤ A} {G : B ⥤ B}
    (r : R ⋙ F ⟶ G ⋙ R) (i : F ≅ 𝟭 A) (j : G ≅ 𝟭 B)
    (h : ∀ N, r.app N ≫ R.map (j.hom.app N) = i.hom.app (R.obj N)) (M : A) :
    L.map (i.hom.app M) =
      ((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ r)).app M ≫
        j.hom.app (L.obj M) := by
  have hm := unit_mateEquiv_symm a a (TwoSquare.mk _ _ _ _ r) M
  change F.map (a.unit.app M) ≫ r.app (L.obj M) =
    a.unit.app (F.obj M) ≫
      R.map (((mateEquiv a a).symm (TwoSquare.mk _ _ _ _ r)).app M) at hm
  apply (a.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [← hm]
  simp only [Category.assoc]
  rw [h]
  have hu := a.unit.naturality (i.hom.app M)
  dsimp only [Functor.comp_map, Functor.id_map] at hu
  rw [← hu]
  exact (i.hom.naturality (a.unit.app M)).symm

private theorem reverse_square
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X Y : A} {U V : B} (i : X ≅ Y) (j : U ≅ V)
    (r : F.obj Y ⟶ V) (s : F.obj X ⟶ U)
    (h : F.map i.inv ≫ s = r ≫ j.inv) :
    F.map i.hom ≫ r = s ≫ j.hom := by
  apply (cancel_epi (F.map i.inv)).1
  simp only [← F.map_comp_assoc, Iso.inv_hom_id, F.map_id, Category.id_comp]
  rw [reassoc_of% h]
  simp

private theorem exact_unit_square
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (R : A ⥤ A) (S : B ⥤ B) (T : A ⥤ B)
    [R.Additive] [S.Additive] [T.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    (ρ : R ⋙ T ≅ T ⋙ S) (η : R ≅ 𝟭 A) (θ : S ≅ 𝟭 B)
    (h : ∀ M, ρ.hom.app M ≫ θ.hom.app (T.obj M) = T.map (η.hom.app M))
    (M : DerivedCategory A) :
    (Functor.mapDerivedCategorySquareIso ρ).hom.app M ≫
        (Functor.exactDerivedRestrictionUnit S θ).hom.app (T.mapDerivedCategory.obj M) =
      T.mapDerivedCategory.map ((Functor.exactDerivedRestrictionUnit R η).hom.app M) := by
  have hρ : ρ ≪≫ Functor.isoWhiskerLeft T θ = Functor.isoWhiskerRight η T := by
    ext N
    exact h N
  have hd := congrArg (fun i ↦ (Functor.mapDerivedCategoryNatIso i).hom) hρ
  rw [Functor.mapDerivedCategoryNatIso_trans] at hd
  have hl := Functor.mapDerivedCategoryNatIso_isoWhiskerLeft T θ
  have hr := Functor.mapDerivedCategoryNatIso_isoWhiskerRight η T
  have hul := Functor.mapDerivedCategoryCompIso_id_comp T
  have hur := Functor.mapDerivedCategoryCompIso_comp_id T
  have hl' := congrArg (fun t ↦ t ≫ Functor.whiskerLeft T.mapDerivedCategory
    (Functor.mapDerivedCategoryIdIso B).hom) hl
  have hr' := congrArg (fun t ↦ t ≫ Functor.whiskerRight
    (Functor.mapDerivedCategoryIdIso A).hom T.mapDerivedCategory) hr
  simp only [Category.assoc, hur] at hl'
  simp only [Category.assoc, hul] at hr'
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso R T).inv.app M)).1
  simp only [Functor.mapDerivedCategorySquareIso, Functor.exactDerivedRestrictionUnit,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hlM := NatTrans.congr_app hl' M
  have hrM := NatTrans.congr_app hr' M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hlM hrM
  rw [← hlM, ← hrM]
  simpa only [NatTrans.comp_app, Category.assoc] using
    congrArg (fun f ↦ f ≫ NatTrans.app (𝟙 T.mapDerivedCategory) M) (NatTrans.congr_app hd M)

open WeilConjectures.SemilinearSections

private abbrev ordinaryComp (W : Scheme.{u}) {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (a : B ⟶ C) (b : C ⟶ D) :
    res (ringMap W b) ⋙ res (ringMap W a) ≅ res (ringMap W (a ≫ b)) :=
  SheafOfModules.systemScalarRestrictionComposition.{u + 1, u, u + 1}
    (ringMap W a) (ringMap W b) (ringMap W (a ≫ b))
    ((coefficientFunctor W).map_comp a b)

private abbrev derivedComp (W : Scheme.{u}) {B C D : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    (a : B ⟶ C) (b : C ⟶ D) :
    restriction W b ⋙ restriction W a ≅ restriction W (a ≫ b) :=
  Functor.exactDerivedRestrictionComposition _ _ _ (ordinaryComp W a b)

private abbrev ordinaryUnit (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    res (ringMap W (𝟙 B)) ≅ 𝟭 (Modules W B) :=
  SheafOfModules.systemScalarRestrictionUnit.{u + 1, u, u + 1}
    (ringMap W (𝟙 B)) ((coefficientFunctor W).map_id B)

private abbrev derivedUnit (W : Scheme.{u}) (B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}) :
    restriction W (𝟙 B) ≅ 𝟭 (Derived W B) :=
  Functor.exactDerivedRestrictionUnit _ (ordinaryUnit W B)

private theorem ordinary_image_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Modules X B) :
    r.ordinary.hom.app M ≫ (ordinaryUnit Y B).hom.app (d.toDirectImage.push.obj M) =
      d.toDirectImage.push.map ((ordinaryUnit X B).hom.app M) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rcases U with ⟨n, U⟩
  ext x
  exact eq_of_heq (r.sections M n (op U) x)

private theorem ordinary_inverse_unit
    {X Y : Scheme.{u}} {g : X ⟶ Y} {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}}
    {d : Image g B} (r : RestrictionImage (𝟙 B) d d) (M : Modules Y B) :
    r.inverseImage.hom.app M ≫ (ordinaryUnit X B).hom.app (d.inverse.obj M) =
      d.inverse.map ((ordinaryUnit Y B).hom.app M) := by
  rw [r.inverseImage_mate]
  symm
  apply inverseMate_identity d.adjunction r.ordinary.inv (ordinaryUnit Y B)
    (ordinaryUnit X B) (fun N ↦ ?_) M
  apply (cancel_epi (r.ordinary.hom.app N)).1
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (ordinary_image_unit r N).symm

private theorem ordinary_open_unit
    {X Z : Scheme.{u}} {j : X ⟶ Z} [IsOpenImmersion j]
    {B : ℕᵒᵖ ⥤ CommRingCat.{u + 1}} {d : OpenImage j B}
    (r : RestrictionOpen (𝟙 B) d d) (M : Modules X B) :
    r.ordinary.hom.app M ≫ (ordinaryUnit Z B).hom.app (d.extension.obj M) =
      d.extension.map ((ordinaryUnit X B).hom.app M) := by
  rw [r.mate]
  symm
  apply inverseMate_identity d.openAdjunction r.image.inverseImage.inv (ordinaryUnit X B)
    (ordinaryUnit Z B) (fun N ↦ ?_) M
  apply (cancel_epi (r.image.inverseImage.hom.app N)).1
  simpa only [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp] using
    (ordinary_inverse_unit r.image N).symm

end AlgebraicGeometry.Etale.SystemProjection

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ExtendedLocalizationCech
public import WeilConjectures.CategoryTheory.RingedCompletionUnit
import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex

/-! # The coefficient-Hom unit for the ring in degree zero

Source: Stacks Project, Algebraization, Tag 099I, first arrow of the final composite.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

namespace ModuleCat

private noncomputable def coefficientScalarSection
    {A D : Type u} [Ring A] [Ring D] (ψ : A →+* D) (M : ModuleCat.{u} D) (m : M) :
    (restrictScalars ψ).obj (ModuleCat.of D D) ⟶ (restrictScalars ψ).obj M :=
  ModuleCat.ofHom
    (X := (restrictScalars ψ).obj (ModuleCat.of D D))
    (Y := (restrictScalars ψ).obj M)
    { toFun (b : D) := b • m
      map_add' b c := by
        change D at b c
        exact add_smul b c m
      map_smul' a b := by
        change A at a
        change D at b
        change (ψ a * b) • m = ψ a • (b • m)
        exact mul_smul _ _ _ }

end ModuleCat

namespace PresheafOfModules

variable {C : Type u} [SmallCategory C]
  {R B : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ B)

private abbrev coefficientRestriction :=
  restrictScalars.{u} (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))

private noncomputable def coefficientUnitSection
    (M : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat))
    (U : C) (m : M.obj (op U)) :
    (restrictOver R U).obj ((coefficientRestriction φ).obj
        (unit (B ⋙ forget₂ CommRingCat RingCat))) ⟶
      (restrictOver R U).obj ((coefficientRestriction φ).obj M) where
  app W := ModuleCat.coefficientScalarSection (φ.app (op W.unop.left)).hom
    (M.obj (op W.unop.left)) (M.map W.unop.hom.op m)
  naturality {W W'} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    change B.obj (op W.unop.left) at b
    symm
    change M.map f.unop.left.op
        (b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op m)) =
      B.map f.unop.left.op b •
        (show M.obj (op W'.unop.left) from M.map W'.unop.hom.op m)
    rw [M.map_smul, ← PresheafOfModules.map_comp_apply, ← op_comp, Over.w]
    rfl

private noncomputable def coefficientUnitMap
    (M : PresheafOfModules.{u} (B ⋙ forget₂ CommRingCat RingCat)) :
    (coefficientRestriction φ).obj M ⟶
      homObj ((coefficientRestriction φ).obj (unit (B ⋙ forget₂ CommRingCat RingCat)))
        ((coefficientRestriction φ).obj M) :=
    { app U := ModuleCat.ofHom
        (X := ((coefficientRestriction φ).obj M).obj U)
        (Y := (homObj ((coefficientRestriction φ).obj
          (unit (B ⋙ forget₂ CommRingCat RingCat)))
            ((coefficientRestriction φ).obj M)).obj U)
        { toFun m := coefficientUnitSection φ M U.unop m
          map_add' m m' := by
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            change B.obj (op W.unop.left) at b
            change M.obj U at m m'
            change b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op (m + m')) =
              b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op m) +
                b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op m')
            rw [map_add, smul_add]
          map_smul' a m := by
            change R.obj U at a
            apply PresheafOfModules.hom_ext
            intro W
            apply ModuleCat.hom_ext
            apply LinearMap.ext
            intro b
            change B.obj (op W.unop.left) at b
            change M.obj U at m
            change b • (show M.obj (op W.unop.left) from
                M.map W.unop.hom.op (φ.app U a • m)) =
              φ.app _ (R.map W.unop.hom.op a) •
                (b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op m))
            rw [M.map_smul]
            have h := CategoryTheory.congr_fun (φ.naturality W.unop.hom.op) a
            change φ.app _ (R.map W.unop.hom.op a) =
              B.map W.unop.hom.op (φ.app U a) at h
            change b • (B.map W.unop.hom.op (φ.app U a) •
                (show M.obj (op W.unop.left) from M.map W.unop.hom.op m)) =
              φ.app (op W.unop.left) (R.map W.unop.hom.op a) •
                (b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op m))
            rw [h, ← mul_smul, ← mul_smul, mul_comm] }
      naturality {U V} f := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        apply PresheafOfModules.hom_ext
        intro W
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro b
        change B.obj (op W.unop.left) at b
        change M.obj U at m
        change b • (show M.obj (op W.unop.left) from M.map W.unop.hom.op (M.map f m)) =
          b • (show M.obj (op W.unop.left) from
            M.map ((Over.map f.unop).obj W.unop).hom.op m)
        rw [← PresheafOfModules.map_comp_apply]
        rfl }

end PresheafOfModules

namespace SheafOfModules

attribute [local irreducible] homComplexFunctor homComplexIsLimit

private theorem postcomposeSquare
    {D : Type u} [Category.{v} D] {X Y Z T U : D}
    {f : X ⟶ Y} {p : Y ⟶ Z} {q : X ⟶ T} {g : T ⟶ Z}
    (h : f ≫ p = q ≫ g) (k : Z ⟶ U) :
    f ≫ p ≫ k = q ≫ g ≫ k := by
  rw [← Category.assoc, h, Category.assoc]

private theorem normalizedComposite
    {D : Type u} [Category.{v} D] {X Y Z T V W : D}
    {a : X ⟶ Y} {b : Y ⟶ Z} {c : Z ⟶ T} {d : T ⟶ X}
    {p : Z ⟶ V} {q : Y ⟶ W} {i : W ⟶ V} {k : V ⟶ X} {t : X ⟶ W}
    (hb : b ≫ p = q ≫ i) (hc : c ≫ d = p ≫ k)
    (ha : a ≫ q = t) (ht : t ≫ i ≫ k = 𝟙 X) :
    a ≫ b ≫ c ≫ d = 𝟙 X := by
  rw [hc, ← Category.assoc b p k, hb, Category.assoc q i k,
    ← Category.assoc a q (i ≫ k), ha]
  exact ht

private theorem composite_inverse_of_components
    {D : Type u} [Category.{v} D] [HasZeroMorphisms D]
    {M X Y Z : CochainComplex D ℤ}
    (a : M ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (e : Z ≅ M)
    (h : ∀ n : ℤ, a.f n ≫ b.f n ≫ c.f n ≫ e.hom.f n = 𝟙 (M.X n)) :
    a ≫ b ≫ c = e.inv := by
  apply (cancel_mono e.hom).1
  refine Eq.trans (b := 𝟙 M) ?_ e.inv_hom_id.symm
  apply HomologicalComplex.hom_ext
  intro n
  simpa only [HomologicalComplex.comp_f, HomologicalComplex.id_f, Category.assoc] using h n

private theorem singleCoefficientMap
    {D E : Type u} [Category.{v} D] [Category.{v} E]
    [HasZeroMorphisms D] [HasZeroMorphisms E] [HasZeroObject D] [HasZeroObject E]
    (r : D ⥤ E) [r.PreservesZeroMorphisms] (A : D) (B : E) (f : B ⟶ r.obj A) :
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ≫
      (((HomologicalComplex.single E (.up ℤ) 0).map f ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app A).f 0) ≫
      r.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 A).hom = f := by
  simp only [HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Category.assoc,
    Iso.inv_hom_id_assoc, ← r.map_comp, Iso.inv_hom_id, r.map_id, Category.comp_id]

end SheafOfModules

namespace SheafOfModules

attribute [local irreducible] homComplexFunctor

private theorem liftedUnit_naturality
    {D E : Type u} [Category.{v} D] [Category.{v} E]
    (r : D ⥤ E)
    (hinj : ∀ {X Y : D} {f g : X ⟶ Y}, r.map f = r.map g → f = g)
    (H : Dᵒᵖ × E ⥤ D) (K : Eᵒᵖ × E ⥤ E)
    (i : H ⋙ r ≅ r.op.prod (𝟭 E) ⋙ K) (A : D)
    (a : ∀ M : D, M ⟶ H.obj (op A, r.obj M))
    (b : ∀ M : D, r.obj M ⟶ K.obj (op (r.obj A), r.obj M))
    (ha : ∀ M, r.map (a M) ≫ i.hom.app (op A, r.obj M) = b M)
    (hb : ∀ {M N : D} (f : M ⟶ N),
      r.map f ≫ b N = b M ≫ K.map ((𝟙 (r.obj A)).op, r.map f))
    {M N : D} (f : M ⟶ N) :
    f ≫ a N = a M ≫ H.map ((𝟙 A).op, r.map f) := by
  apply hinj
  apply (cancel_mono (i.hom.app (op A, r.obj N))).1
  have hn := i.hom.naturality
    (show (op A, r.obj M) ⟶ (op A, r.obj N) from ((𝟙 A).op, r.map f))
  change r.map (H.map (X := (op A, r.obj M)) (Y := (op A, r.obj N))
      ((𝟙 A).op, r.map f)) ≫ i.hom.app (op A, r.obj N) =
    i.hom.app (op A, r.obj M) ≫ K.map
      (X := (op (r.obj A), r.obj M)) (Y := (op (r.obj A), r.obj N))
      ((r.map (𝟙 A)).op, r.map f) at hn
  rw [r.map_id] at hn
  rw [r.map_comp, r.map_comp, Category.assoc, ha,
    Category.assoc, hn, ← Category.assoc, ha]
  exact hb f

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

private noncomputable def unitRawSection
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (U : C) (m : M.val.obj (op U)) :
    (PresheafOfModules.restrictOver R.obj U).obj
        ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
            (unit
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))).val ⟶
      (PresheafOfModules.restrictOver R.obj U).obj ((restrictScalars.{u} ((sheafCompose J (forget₂
          CommRingCat.{u} RingCat.{u})).map φ)).obj M).val :=
  PresheafOfModules.coefficientUnitSection φ.hom M.val U m

private theorem unitRawSection_app
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (U : C) (m : M.val.obj (op U)) (W : (Over U)ᵒᵖ)
    (b : B.obj.obj (op W.unop.left)) :
    ((unitRawSection φ M U m).app W).hom b =
      b • (show M.val.obj (op W.unop.left) from M.val.map W.unop.hom.op m) := rfl

private noncomputable def unitRawMap
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj M ⟶
      homObj (R := R) ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).map φ)).obj (unit
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)))
        ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
            M) where
  val := PresheafOfModules.coefficientUnitMap φ.hom M.val

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem sheaf_comp_apply
    {S : Sheaf J RingCat.{u}} {M N P : SheafOfModules.{u} S}
    (f : M ⟶ N) (g : N ⟶ P) (U : Cᵒᵖ) (m : M.val.obj U) :
    (((f ≫ g).val.app U).hom m) = (g.val.app U).hom ((f.val.app U).hom m) := rfl

private theorem rawMap_apply
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (U : Cᵒᵖ) (m : M.val.obj U) :
    ((unitRawMap φ M).val.app U).hom m = unitRawSection φ M U.unop m := rfl

private theorem homMap_apply
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (f : M' ⟶ M) (g : N ⟶ N') (U : Cᵒᵖ)
    (h : (homObj (R := R) M N).val.obj U) (W : (Over U.unop)ᵒᵖ)
    (m : M'.val.obj (op W.unop.left)) :
    ((((homObjMap (R := R) f g).val.app U).hom h).app W).hom m =
      (g.val.app (op W.unop.left)).hom ((h.app W).hom
        ((f.val.app (op W.unop.left)).hom m)) := rfl

private theorem homUnit_apply
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (U : Cᵒᵖ) (h : (homObj (R := R) (unit _) N).val.obj U) :
    (((homObjUnitIso N).hom.val.app U).hom h) =
      (h.app (op (Over.mk (𝟙 U.unop)))).hom (1 : R.obj.obj U) := rfl

private noncomputable def liftRestriction
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)}
    (f : (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        M ⟶ (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        φ)).obj N)
    (h : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
      (f.val.app U).hom (b • m) =
        @SMul.smul _ _ (N.val.obj U).isModule.toSMul b ((f.val.app U).hom m)) : M ⟶ N where
  val :=
    { app U := ModuleCat.ofHom
        { toFun (m : M.val.obj U) := (show N.val.obj U from (f.val.app U).hom m)
          map_add' m m' := (f.val.app U).hom.map_add m m'
          map_smul' := h U }
      naturality {U V} g := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro m
        exact PresheafOfModules.naturality_apply f.val g m }

private theorem restriction_injective
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)}
    {f g : M ⟶ N} (h : (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).map φ)).map f = (restrictScalars.{u} ((sheafCompose J (forget₂
        CommRingCat.{u} RingCat.{u})).map φ)).map g) :
    f = g := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  exact congrArg (fun k ↦ (k.val.app U).hom m) h

variable (H :
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
        SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
  (i : H ⋙ restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
      (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor R))
  (haction : ∀ (M : SheafOfModules.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
          (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
          (U : C)
          (b : ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj.obj (op U))
          (h : (H.obj (op M, N)).val.obj (op U)) (W : Over U)
          (m : M.val.obj (op W.left)),
          (((i.hom.app (op M, N)).val.app (op U)).hom
            (@SMul.smul _ _ ((H.obj (op M, N)).val.obj (op U)).isModule.toSMul b h)).app (op W) m =
            (((i.hom.app (op M, N)).val.app (op U)).hom h).app (op W)
              (@SMul.smul _ _ (M.val.obj (op W.left)).isModule.toSMul
                (B.obj.map W.hom.op b) m))

private noncomputable def baseComparison (M : (SheafOfModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj B))) (N : (SheafOfModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj R))) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        (H.obj (op M, N)) ≅
      homObj (R := R) ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).map φ)).obj M) N :=
  i.app (op M, N)

attribute [local irreducible] unitRawMap unitRawSection

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
private theorem sectionIso_injective
    {S : Sheaf J RingCat.{u}} {M N : SheafOfModules.{u} S}
    (e : M ≅ N) (U : Cᵒᵖ) : Function.Injective ((e.hom.val.app U).hom) := by
  intro a b h
  have he (x : M.val.obj U) :
      (e.inv.val.app U).hom ((e.hom.val.app U).hom x) = x :=
    congrArg (fun k ↦ (k.val.app U).hom x) e.hom_inv_id
  exact (he a).symm.trans ((congrArg ((e.inv.val.app U).hom) h).trans (he b))

private noncomputable def unitBase (M : (SheafOfModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj B))) :
    M ⟶ H.obj (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj M)
          := by
  let A := unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)
  let j := baseComparison φ H i A ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).map φ)).obj M)
  let f : (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
      M ⟶
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
          (H.obj (op A, (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).map φ)).obj M)) :=
    unitRawMap φ M ≫ j.inv
  apply liftRestriction φ f
  intro U b m
  apply sectionIso_injective j U
  have he (x : M.val.obj U) :
      (j.hom.val.app U).hom ((f.val.app U).hom x) =
        unitRawSection φ M U.unop x := by
    have h := congrArg (fun k ↦ (k.val.app U).hom x)
      (show f ≫ j.hom = unitRawMap φ M by
        dsimp only [f]; simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
    change (j.hom.val.app U).hom ((f.val.app U).hom x) =
      ((unitRawMap φ M).val.app U).hom x at h
    exact h.trans (rawMap_apply φ M U x)
  rw [he]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  change B.obj.obj (op W.unop.left) at a
  have hact := haction A ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).map φ)).obj M) U.unop b
    ((f.val.app U).hom m) W.unop a
  change ((unitRawSection φ M U.unop (b • m)).app W).hom a = _
  refine Eq.trans ?_ hact.symm
  have hx := congrArg (fun k ↦ (k.app W).hom
      (B.obj.map W.unop.hom.op b • a)) (he m)
  rw [unitRawSection_app, M.val.map_smul]
  refine Eq.trans ?_ hx.symm
  rw [unitRawSection_app]
  change a • (B.obj.map W.unop.hom.op b •
      (show M.val.obj (op W.unop.left) from M.val.map W.unop.hom.op m)) =
    (B.obj.map W.unop.hom.op b * a) •
      (show M.val.obj (op W.unop.left) from M.val.map W.unop.hom.op m)
  rw [← mul_smul, mul_comm]

private theorem restriction_liftRestriction
    {M N : (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))}
    (f : (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        M ⟶ (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        φ)).obj N)
    (h : ∀ (U : Cᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U),
      (f.val.app U).hom (b • m) =
        @SMul.smul _ _ (N.val.obj U).isModule.toSMul b ((f.val.app U).hom m)) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map
        (liftRestriction φ f h) = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rfl

private theorem unitBase_comparison (M : (SheafOfModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj B))) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map
        (unitBase φ H i haction M) ≫
      coefficientHomObjComparisonHom φ H i
        (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
            M) = unitRawMap φ M := by
  dsimp only [unitBase]
  rw [restriction_liftRestriction]
  change (unitRawMap φ M ≫ (baseComparison φ H i _ _).inv) ≫
    (baseComparison φ H i _ _).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

attribute [local irreducible] unitBase

private theorem unitRawMap_evaluation
    (M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)) :
    unitRawMap φ M ≫ homObjMap (R := R) (LocalizationCech.unitMap φ) (𝟙 _) ≫
      (homObjUnitIso ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).map φ)).obj M)).hom = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [sheaf_comp_apply, sheaf_comp_apply, homUnit_apply, homMap_apply,
    rawMap_apply, unitRawSection_app]
  have h := (LocalizationCech.unitMap_existsUnique φ).choose_spec.1 U 1
  change ((LocalizationCech.unitMap φ).val.app U).hom (1 : R.obj.obj U) =
    φ.hom.app U (1 : R.obj.obj U) at h
  change (show B.obj.obj U from
    ((LocalizationCech.unitMap φ).val.app U).hom (1 : R.obj.obj U)) •
      (show M.val.obj U from M.val.map (𝟙 U.unop).op m) = m
  rw [h, map_one, one_smul, op_id]
  change M.val.map (𝟙 U) m = m
  rw [M.val.map_id]
  rfl

private theorem unitRawMap_naturality
    {M N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)}
    (f : M ⟶ N) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map f ≫
        unitRawMap φ N = unitRawMap φ M ≫
      homObjMap (R := R) (𝟙 _) ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
          RingCat.{u})).map φ)).map f) := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  rw [sheaf_comp_apply, sheaf_comp_apply, rawMap_apply]
  apply PresheafOfModules.hom_ext
  intro W
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro b
  rw [homMap_apply, rawMap_apply, unitRawSection_app, unitRawSection_app]
  change B.obj.obj (op W.unop.left) at b
  change M.val.obj U at m
  change b • (show N.val.obj (op W.unop.left) from
      N.val.map W.unop.hom.op ((f.val.app U).hom m)) =
    (f.val.app (op W.unop.left)).hom
      (b • (show M.val.obj (op W.unop.left) from M.val.map W.unop.hom.op m))
  rw [(f.val.app _).hom.map_smul, PresheafOfModules.naturality_apply]

attribute [local irreducible] homObjMap homObjUnitIso

private theorem unitBase_naturality
    (η : ∀ M : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B),
        M ⟶ H.obj (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
        (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
        M))
    (hη : ∀ M, (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        φ)).map (η M) ≫ coefficientHomObjComparisonHom φ H i
          (op (unit ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).obj B)), (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
        RingCat.{u})).map φ)).obj M) = unitRawMap φ M)
    {M N : (SheafOfModules.{u} ((sheafCompose J (forget₂
    CommRingCat.{u} RingCat.{u})).obj B))} (f : M ⟶ N) :
    f ≫ η N = η M ≫
      H.map (X := (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
          (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
              M))
        (Y := (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
          (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj
              N)) ((𝟙 _).op, (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
              RingCat.{u})).map φ)).map f) := by
  exact liftedUnit_naturality (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat.{u}
      RingCat.{u})).map φ)) (fun h ↦ restriction_injective φ h)
    H (Functor.uncurry.obj (homFunctor R)) i
    (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B))
    (η) (unitRawMap φ) (hη)
    (by
      intro M N g
      rw [comparisonHomMap]
      exact unitRawMap_naturality φ g) f

include haction in
/-- Expose the explicit base-unit construction through its normalization law. -/
private theorem exists_unitBase :
    ∃ η : ∀ M : SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B),
      M ⟶ H.obj
        (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
          (restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj M),
      ∀ M, (restrictScalars.{u}
          ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).map (η M) ≫
        coefficientHomObjComparisonHom φ H i
          (op (unit ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj B)),
            (restrictScalars.{u}
              ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)).obj M) =
          unitRawMap φ M :=
  ⟨unitBase φ H i haction, unitBase_comparison φ H i haction⟩

end SheafOfModules

namespace SheafOfModules

variable {A E : Type u} [Category.{v} A] [Category.{v} E]
    [Preadditive A] [HasZeroMorphisms E]
    (r : A ⥤ E) [r.PreservesZeroMorphisms] (H : Aᵒᵖ × E ⥤ A)
    (L : CochainComplex A ℤ)
    (η : ∀ M : A, M ⟶ H.obj (op (L.X 0), r.obj M))
    (hη : ∀ {M N : A} (f : M ⟶ N),
      f ≫ η N = η M ≫ H.map (X := (op (L.X 0), r.obj M))
        (Y := (op (L.X 0), r.obj N)) ((𝟙 (L.X 0)).op, r.map f))

private noncomputable def genericUnitComponent (M : CochainComplex A ℤ)
    (n p q : ℤ) (h : p + n = q) :
    M.X n ⟶ H.obj (op (L.X p),
      r.obj (M.X q)) := by
  by_cases hp : p = 0
  · subst p
    simp only [zero_add] at h
    subst q
    exact η (M.X n)
  · exact 0

omit [HasZeroMorphisms E] [r.PreservesZeroMorphisms] in
private theorem genericUnitComponent_zero (M : CochainComplex A ℤ) (n : ℤ) :
    genericUnitComponent r H L η M n 0 n (by omega) =
      η (M.X n) := by
  simp only [genericUnitComponent, dite_eq_left]

omit [HasZeroMorphisms E] [r.PreservesZeroMorphisms] in
include hη in
private theorem genericUnitComponent_naturality {M N : CochainComplex A ℤ}
    (f : M ⟶ N) (n p q : ℤ) (h : p + n = q) :
    f.f n ≫ genericUnitComponent r H L η N n p q h =
      genericUnitComponent r H L η M n p q h ≫
        H.map (X := (op (L.X p),
            r.obj (M.X q)))
          (Y := (op (L.X p),
            r.obj (N.X q)))
          ((𝟙 _).op, r.map (f.f q)) := by
  by_cases hp : p = 0
  · subst p
    have hq' : q = n := by omega
    revert h
    rw [hq']
    intro h
    rw [genericUnitComponent_zero, genericUnitComponent_zero, hη]
  · simp only [genericUnitComponent, dite_eq_right hp, comp_zero, zero_comp]

private theorem uncurryCurry_map
    {D E F : Type u} [Category.{v} D] [Category.{v} E] [Category.{v} F]
    (H : D × E ⥤ F) {X Y : D × E} (f : X ⟶ Y) :
    ((Functor.uncurry.obj (Functor.curry.obj H)).map f : H.obj X ⟶ H.obj Y) =
      H.map f := by
  change H.map (X := X) (Y := (Y.1, X.2)) (f.1, 𝟙 X.2) ≫
    H.map (X := (Y.1, X.2)) (Y := Y) (𝟙 Y.1, f.2) = _
  rw [← H.map_comp]
  congr 1
  apply Prod.ext
  · exact Category.comp_id _
  · exact Category.id_comp _

include hη in
private theorem genericUnitChain
    (hL : ∀ n m : ℤ, L.d n m = 0)
    (hLzero : ∀ p : ℤ, p ≠ 0 → IsZero (L.X p))
    (haddLeft : ∀ N, ((Functor.curry.obj H).flip.obj N).Additive)
    (G : (CochainComplex A ℤ)ᵒᵖ ⥤
      CochainComplex E ℤ ⥤ CochainComplex A ℤ)
    (dG : ProductHomComplexData (Functor.curry.obj H) G) :
    ∃ α : 𝟭 (CochainComplex A ℤ) ⟶
        r.mapHomologicalComplex (.up ℤ) ⋙
          G.obj (op L),
      ∀ (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q),
        (α.app M).f n ≫
          dG.π L
            ((r.mapHomologicalComplex (.up ℤ)).obj M) n p q h =
          genericUnitComponent r H L η M n p q h := by
  let rc := r.mapHomologicalComplex (.up ℤ)
  let π := dG.π
  have hπ := dG.isLimit
  have hd := dG.differential
  have hm := dG.naturality
  let a (M : CochainComplex A ℤ) (n : ℤ) :
      M.X n ⟶ ((G.obj (op L)).obj (rc.obj M)).X n :=
    Fan.IsLimit.lift (hπ L (rc.obj M) n).some
      (fun p ↦ genericUnitComponent r H L η M n p (p + n) rfl)
  have ha (M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q) :
      a M n ≫ π L (rc.obj M) n p q h = genericUnitComponent r H L η M n p q h := by
    subst q
    exact Fan.IsLimit.fac (hπ L (rc.obj M) n).some _ p
  have hz (p : ℤ) (hp : p ≠ 0) (N : E) :
      IsZero (H.obj (op (L.X p), N)) := by
    have := haddLeft N
    exact ((Functor.curry.obj H).flip.obj N).map_isZero
      (hLzero p hp).op
  have ha_comm (M : CochainComplex A ℤ) (n m : ℤ)
      (hnm : n + 1 = m) (p q : ℤ) (h : p + m = q) :
      (a M n ≫ ((G.obj (op L)).obj (rc.obj M)).d n m) ≫
          π L (rc.obj M) m p q h =
        (M.d n m ≫ a M m) ≫ π L (rc.obj M) m p q h := by
    by_cases hp : p = 0
    · subst p
      have hq : q = m := by omega
      revert h
      rw [hq]
      intro h
      have hzero :
          (Functor.uncurry.obj (Functor.curry.obj H)).map
            (X := (op (L.X (m - n)), (rc.obj M).X m))
            (Y := (op (L.X 0), (rc.obj M).X m))
            ((L.d 0 (m - n)).op, 𝟙 _) = 0 := by
        have := haddLeft ((rc.obj M).X m)
        rw [hL, op_zero]
        rw [uncurryCurry_map]
        change ((Functor.curry.obj H).flip.obj ((rc.obj M).X m)).map 0 = 0
        exact Functor.map_zero _ _ _
      have hd' := hd L (rc.obj M) n m 0 m n (m - n) hnm
        (by omega) (by omega) (by omega)
      rw [hzero, comp_zero, smul_zero, sub_zero] at hd'
      rw [Category.assoc, Category.assoc]
      rw [hd', ← Category.assoc, ha, ha, genericUnitComponent_zero, genericUnitComponent_zero]
      rw [uncurryCurry_map]
      exact (hη (M.d n m)).symm
    · exact (hz p hp ((rc.obj M).X q)).eq_of_tgt _ _
  let α (M : CochainComplex A ℤ) :
      M ⟶ (G.obj (op L)).obj (rc.obj M) :=
    { f := a M
      comm' n m hnm := by
        apply Fan.IsLimit.hom_ext (hπ L (rc.obj M) m).some
        intro p
        exact ha_comm M n m hnm p (p + m) rfl }
  refine ⟨{ app := α, naturality := ?_ }, ?_⟩
  · intro M N f
    apply HomologicalComplex.hom_ext
    intro n
    apply Fan.IsLimit.hom_ext (hπ L (rc.obj N) n).some
    intro p
    change (f.f n ≫ a N n) ≫ π L (rc.obj N) n p (p + n) rfl =
      (a M n ≫ ((G.obj (op L)).map (rc.map f)).f n) ≫
        π L (rc.obj N) n p (p + n) rfl
    have hm' := hm L L (rc.obj M) (rc.obj N) (𝟙 L) (rc.map f) n p (p + n) rfl
    simp only [op_id, G.map_id, NatTrans.id_app, Category.id_comp] at hm'
    rw [Category.assoc, ha, Category.assoc, hm', ← Category.assoc, ha]
    rw [uncurryCurry_map]
    exact genericUnitComponent_naturality r H L η hη f n p (p + n) rfl
  · exact ha

end SheafOfModules

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] homComplexFunctor homComplexIsLimit
attribute [local irreducible] sheafCompose SheafOfModules.restrictScalars
  SheafOfModules.coefficientHomObjComparisonHom SheafOfModules.genericUnitComponent

private theorem ringedEvaluation_f
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (M : ringedSiteComplex R) (n : ℤ) :
    (ringedHomUnitFunctorEvaluationIso R M).hom.f n =
      SheafOfModules.complexHomProjection (ringedSiteRingComplex R) M n 0 n (by omega) ≫
        (SheafOfModules.homObjUnitIso (M.X n)).hom := by
  unfold SheafOfModules.complexHomProjection
  exact (ringedHomUnitFunctorEvaluationIso_hom_f R M n).trans
    (ringedHomUnitEvaluationMap_normalized R M n)

attribute [local irreducible] ringedHomUnitEvaluationIso
  ringedHomUnitFunctorEvaluationIso homComplexUnitEvaluation homComplexπ

-- Keep the propositional instance witnesses small at the concrete interface.
private theorem unitProducts
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (S : Sheaf J RingCat.{u}) : HasProducts.{0} (SheafOfModules.{u} S) := by
  intro K
  apply SheafOfModules.hasLimitsOfShape

-- The complex unit depends only on the degree-zero normalization of the ring map.
-- Construct it with an abstract map and a shared sheaf-composition instance.
private theorem coefficientHom_unit_of_degreeZero
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    ∀ (σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B)),
      σ.f 0 = SheafOfModules.LocalizationCech.unitMap φ →
    ∃ F : (ringedSiteComplex B)ᵒᵖ ⥤ ringedSiteComplex R ⥤ ringedSiteComplex B,
      ∃ c : Functor.uncurry.obj F ⋙ rc ≅
          rc.op.prod (𝟭 _) ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)),
        ∃ α : 𝟭 (ringedSiteComplex B) ⟶ rc ⋙ F.obj (op (ringedSiteRingComplex B)),
          ∀ M : ringedSiteComplex B,
            rc.map (α.app M) ≫ c.hom.app (op (ringedSiteRingComplex B), rc.obj M) ≫
                ((homComplexFunctor (R := R)).map σ.op).app (rc.obj M) =
              (by
                change rc.obj M ⟶ ((homComplexFunctor (R := R)).obj
                  (op (ringedSiteRingComplex R))).obj (rc.obj M)
                exact (ringedHomUnitEvaluationIso R (rc.obj M)).inv) := by
  intro r rc σ hσ0
  let : HasProducts.{0} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
    unitProducts ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)
  let L := ringedSiteRingComplex B
  let δ : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      r.obj (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
    σ.f 0
  change δ = SheafOfModules.LocalizationCech.unitMap φ at hσ0
  obtain ⟨H, i, haction, haddRight, haddLeft⟩ :=
    SheafOfModules.exists_restrictedCoefficientHomFunctor φ
  obtain ⟨η, hη⟩ := SheafOfModules.exists_unitBase φ H i haction
  clear haction
  obtain ⟨G, ⟨dG⟩⟩ := SheafOfModules.extendProductFromSeparateAdditivity H
    haddRight haddLeft
  obtain ⟨c, hc⟩ := SheafOfModules.coefficientHomComplex_comparison φ H i G dG
  obtain ⟨α, hα⟩ := SheafOfModules.genericUnitChain r H L η
    (by intro M N f; exact SheafOfModules.unitBase_naturality φ H i η hη f)
    (by intro n m; exact HomologicalComplex.single_obj_d (.up ℤ) 0 _ n m)
    (by
      intro p hp
      exact HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 _ p hp)
    haddLeft G dG
  refine ⟨G, c, α, ?_⟩
  intro M
  let N := rc.obj M
  let b : rc.obj ((G.obj (op L)).obj N) ⟶
      ((homComplexFunctor (R := R)).obj (op (rc.obj L))).obj N := c.hom.app (op L, N)
  let f := ((homComplexFunctor (R := R)).map σ.op).app N
  let e := ringedHomUnitFunctorEvaluationIso R N
  refine Eq.trans ?_ (ringedHomUnitFunctorEvaluationIso_inv_eq R N)
  refine SheafOfModules.composite_inverse_of_components (rc.map (α.app M)) b f e ?_
  intro n
  let a : N.X n ⟶ r.obj (((G.obj (op L)).obj N).X n) := (rc.map (α.app M)).f n
  let p : (((homComplexFunctor (R := R)).obj (op (rc.obj L))).obj N).X n ⟶
      SheafOfModules.homObj (R := R) (r.obj (L.X 0)) (N.X n) :=
    SheafOfModules.complexHomProjection (rc.obj L) N n 0 n (by omega)
  let q : ((G.obj (op L)).obj N).X n ⟶ H.obj (op (L.X 0), N.X n) :=
    dG.π L N n 0 n (by omega)
  let j := SheafOfModules.coefficientHomObjComparisonHom φ H i (op (L.X 0), N.X n)
  let k := SheafOfModules.homObjMap (R := R) δ (𝟙 (N.X n)) ≫
    (SheafOfModules.homObjUnitIso (N.X n)).hom
  have hb : b.f n ≫ p = r.map q ≫ j := hc L N n 0 n (by omega)
  have hm := SheafOfModules.complexHomProjection_map_left (M := N) σ n 0 n (by omega)
  have hf : f.f n ≫ e.hom.f n = p ≫ k :=
    (congrArg (fun v ↦ f.f n ≫ v) (ringedEvaluation_f R N n)).trans
      (SheafOfModules.postcomposeSquare hm (SheafOfModules.homObjUnitIso (N.X n)).hom)
  let t : N.X n ⟶ r.obj (H.obj (op (L.X 0), N.X n)) := r.map (η (M.X n))
  have ha : a ≫ r.map q = t :=
    (r.map_comp _ _).symm.trans
      (congrArg r.map ((hα M n 0 n (by omega)).trans
        (SheafOfModules.genericUnitComponent_zero _ _ _ _ M n)))
  have ht : t ≫ j ≫ k = 𝟙 (N.X n) := by
    have hv := (congrArg
      (fun z ↦ z ≫
        SheafOfModules.homObjMap (R := R) (SheafOfModules.LocalizationCech.unitMap φ)
          (𝟙 (r.obj (M.X n))) ≫
        (SheafOfModules.homObjUnitIso (r.obj (M.X n))).hom)
      (hη (M.X n))).trans (SheafOfModules.unitRawMap_evaluation φ (M.X n))
    change r.map (η (M.X n)) ≫
      SheafOfModules.coefficientHomObjComparisonHom φ H i
        (op (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)),
          r.obj (M.X n)) ≫
      SheafOfModules.homObjMap (R := R) δ (𝟙 (r.obj (M.X n))) ≫
      (SheafOfModules.homObjUnitIso (r.obj (M.X n))).hom = 𝟙 (r.obj (M.X n))
    rw [hσ0]
    simpa only [Category.assoc] using hv
  exact SheafOfModules.normalizedComposite hb hf ha ht

-- The statement and its normalization compare several chosen Hom-complex constructions.
/-- The coefficient-Hom bifunctor has a unit at the coefficient ring, normalized by
restriction and evaluation at one.
Source: Stacks Project, Algebraization, Tag 099I, first arrow of the final composite.
(auxiliary; not a blueprint node).

Proof: take the coefficient internal Hom with its precomposition B-action and form its
product Hom complexes. Restriction preserves the products. Choose the comparison with
the R-valued Hom complex by requiring its composite with every product projection to
be the restricted coefficient projection followed by the underlying-Hom comparison.
The differential and induced-map formulas show that this is a natural chain isomorphism
in both variables. In degree n define the unit by the product lift whose p-th component
is zero for p != 0. For p=0 use the B-linear map sending a section m to the R-linear map
b -> b*m, transporting the source along B[0]^0 = B. It is B-linear because the action on
Hom is precomposition with multiplication. The ring single complex has zero differential,
so the Hom differential is just postcomposition with d_M, which commutes with this map.
Thus the lifts are a chain map natural in M. After restriction and precomposition with
R[0] -> r(B[0]), the only nonzero component sends m to (a -> phi(a)*m) = (a -> a*m).
This is exactly the inverse of evaluation at one. The normalization of the comparison
and equality on product projections prove the identity. The construction also applies
to zero rings, empty sites and zero complexes; no flatness or injectivity is used. -/
theorem exists_coefficientHom_unit
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B) :
    let r := SheafOfModules.restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let rc := r.mapHomologicalComplex (.up ℤ)
    let σ : ringedSiteRingComplex R ⟶ rc.obj (ringedSiteRingComplex B) :=
      (HomologicalComplex.single _ (.up ℤ) 0).map
          (SheafOfModules.LocalizationCech.unitMap φ) ≫
        (HomologicalComplex.singleMapHomologicalComplex r (.up ℤ) 0).inv.app
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    ∃ F : (ringedSiteComplex B)ᵒᵖ ⥤ ringedSiteComplex R ⥤ ringedSiteComplex B,
      ∃ c : Functor.uncurry.obj F ⋙ rc ≅
          rc.op.prod (𝟭 _) ⋙ Functor.uncurry.obj (homComplexFunctor (R := R)),
        ∃ α : 𝟭 (ringedSiteComplex B) ⟶ rc ⋙ F.obj (op (ringedSiteRingComplex B)),
          ∀ M : ringedSiteComplex B,
            rc.map (α.app M) ≫ c.hom.app (op (ringedSiteRingComplex B), rc.obj M) ≫
                ((homComplexFunctor (R := R)).map σ.op).app (rc.obj M) =
              (by
                change rc.obj M ⟶ ((homComplexFunctor (R := R)).obj
                  (op (ringedSiteRingComplex R))).obj (rc.obj M)
                exact (ringedHomUnitEvaluationIso R (rc.obj M)).inv) := by
  have : J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u}) :=
    ringedCompletionHasSheafCompose J
  intro r rc σ
  have hσ := SheafOfModules.singleCoefficientMap r _ _
    (SheafOfModules.LocalizationCech.unitMap φ)
  let δ : SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⟶
      r.obj (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) :=
    σ.f 0
  have hσ0 : δ = SheafOfModules.LocalizationCech.unitMap φ := by
    have h : (𝟙 _) ≫ δ ≫ r.map (𝟙 _) =
        SheafOfModules.LocalizationCech.unitMap φ := hσ
    simpa only [Functor.map_id, Category.id_comp, Category.comp_id] using h
  exact coefficientHom_unit_of_degreeZero φ σ hσ0

end CategoryTheory

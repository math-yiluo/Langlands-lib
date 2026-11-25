/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import WeilConjectures.Algebra.Homology.RingedHomRestrictionComparison
import WeilConjectures.Algebra.Homology.HomComplexComponents
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Coherent restriction of ordinary internal Hom complexes

Source: Stacks Project, Tags 0A8X and 08JB.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.RingedHomRestriction

private abbrev restricted {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :=
  (F.sheafPushforwardContinuous CommRingCat K J).obj R

private def directRestrict {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :
    Modules R ⥤ Modules (restricted (K := K) F R) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ F (R.obj ⋙ forget₂ _ _)).obj M.val
      isSheaf := ((F.sheafPushforwardContinuous _ K J).obj ⟨_, M.isSheaf⟩).property }
  map f := ⟨(PresheafOfModules.pushforward₀ F (R.obj ⋙ forget₂ _ _)).map f.val⟩

private abbrev restrict {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :
    Modules R ⥤ Modules (restricted (K := K) F R) :=
  SheafOfModules.pushforward.{u} (F := F) (J := K) (K := J) (R := Rings R)
    (𝟙 ((F.sheafPushforwardContinuous RingCat K J).obj (Rings R)))

private def standardIso {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :
    directRestrict (K := K) F R ≅ restrict (K := K) F R :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun X ↦
      (ModuleCat.restrictScalarsId'App _ rfl
        (((PresheafOfModules.pushforward₀ F
          (R.obj ⋙ forget₂ CommRingCat RingCat)).obj M.val).obj X)).symm)
      (by intros; ext x; rfl)) (by intros; ext X x; rfl)

private def rawFactorMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : D ⥤ C) (R : Cᵒᵖ ⥤ CommRingCat.{u})
    (M N : PresheafOfModules.{u} (R ⋙ forget₂ _ _)) :
    (PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M N) ⟶
      PresheafOfModules.homObj (R := F.op ⋙ R)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N) where
  app X := ModuleCat.ofHom
    (X := (PresheafOfModules.homObj (R := R) M N).obj (F.op.obj X))
    (Y := (PresheafOfModules.homObj (R := F.op ⋙ R)
      ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
      ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N)).obj X)
    { toFun := fun φ ↦ (PresheafOfModules.pushforward₀ (Over.post (X := X.unop) F) _).map φ
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality f := by
    ext φ : 2
    apply PresheafOfModules.hom_ext
    intro W
    ext x
    change φ.app (op (Over.mk (F.map W.unop.hom ≫ F.map f.unop))) x =
      φ.app (op (Over.mk (F.map (W.unop.hom ≫ f.unop)))) x
    exact PresheafOfModules.restrictOver_hom_app_congr φ (F.map_comp _ _).symm x

private def directFactorMap
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u})
    (M N : Modules R) :
    (directRestrict (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ⟶
      SheafOfModules.homObj (R := restricted (K := K) F R)
        ((directRestrict (K := K) F R).obj M) ((directRestrict (K := K) F R).obj N) :=
  ⟨rawFactorMap F R.obj M.val N.val⟩

private theorem directFactorMap_val
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u})
    (M N : Modules R) :
    (directFactorMap (K := K) F R M N).val = rawFactorMap F R.obj M.val N.val := by
  rfl

private theorem restriction_map_bijective
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    (F : C ⥤ D) [F.IsEquivalence] (R : Dᵒᵖ ⥤ RingCat.{u})
    (M N : PresheafOfModules.{u} R) :
    Function.Bijective (fun f : M ⟶ N ↦ (PresheafOfModules.pushforward₀ F R).map f) := by
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{u}).obj F.op
  have hi : Function.Injective (fun f : M ⟶ N ↦
      (PresheafOfModules.pushforward₀ F R).map f) := by
    intro f g h
    apply (PresheafOfModules.toPresheaf R).map_injective
    apply W.map_injective
    exact congrArg ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map) h
  refine ⟨hi, ?_⟩
  intro α
  let β : M.presheaf ⟶ N.presheaf :=
    W.preimage ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map α)
  have hb (X : Cᵒᵖ) (x : M.obj (F.op.obj X)) :
      β.app (F.op.obj X) x = α.app X x :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (W.map_preimage (X := M.presheaf) (Y := N.presheaf)
        ((PresheafOfModules.toPresheaf (F.op ⋙ R)).map α)) X) x
  have hs (Y : Dᵒᵖ) (r : R.obj Y) (x : M.obj Y) :
      β.app Y (r • x) = r • β.app Y x := by
    let e := F.op.objObjPreimageIso Y
    apply (ConcreteCategory.bijective_of_isIso (N.presheaf.map e.inv)).1
    change N.map e.inv (β.app Y (r • x)) = N.map e.inv (r • β.app Y x)
    have hn (z : M.obj Y) :
        N.map e.inv (β.app Y z) = β.app _ (M.map e.inv z) :=
      (β.naturality_apply e.inv z).symm
    rw [hn, M.map_smul, hb, map_smul, N.map_smul, hn, hb]
  refine ⟨PresheafOfModules.homMk β hs, ?_⟩
  ext X x
  exact hb X x

private theorem directFactorMap_isIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u})
    (hF : ∀ X : D, (Over.post (X := X) F).IsEquivalence) (M N : Modules R) :
    IsIso (directFactorMap (K := K) F R M N) := by
  have h (X : Dᵒᵖ) : IsIso ((directFactorMap (K := K) F R M N).val.app X) := by
    let := hF X.unop
    rw [directFactorMap_val, ConcreteCategory.isIso_iff_bijective]
    exact restriction_map_bijective (Over.post (X := X.unop) F) _
      ((PresheafOfModules.restrictOver R.obj (F.obj X.unop)).obj M.val)
      ((PresheafOfModules.restrictOver R.obj (F.obj X.unop)).obj N.val)
  have : IsIso (directFactorMap (K := K) F R M N).val := by
    let e := PresheafOfModules.isoMk (fun X ↦ asIso ((directFactorMap (K := K) F R M N).val.app X))
      (fun _ _ f ↦ (directFactorMap (K := K) F R M N).val.naturality f)
    change IsIso e.hom
    infer_instance
  let e : (directRestrict (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := restricted (K := K) F R)
        ((directRestrict (K := K) F R).obj M) ((directRestrict (K := K) F R).obj N) :=
    { hom := directFactorMap (K := K) F R M N
      inv := ⟨inv (directFactorMap (K := K) F R M N).val⟩
      hom_inv_id := SheafOfModules.hom_ext (IsIso.hom_inv_id _)
      inv_hom_id := SheafOfModules.hom_ext (IsIso.inv_hom_id _) }
  exact e.isIso_hom

attribute [local irreducible] rawFactorMap directFactorMap

private def bifunctorIso
    {A B : Type*} [Category A] [Category B] (H : A → A → B)
    (map : ∀ {M M' N N'}, (M' ⟶ M) → (N ⟶ N') → (H M N ⟶ H M' N'))
    (hid : ∀ M N, map (𝟙 M) (𝟙 N) = 𝟙 (H M N))
    (hcomp : ∀ {M M' M'' N N' N''} (f : M' ⟶ M) (f' : M'' ⟶ M')
      (g : N ⟶ N') (g' : N' ⟶ N''), map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g'))
    {M M' N N'} (e : M ≅ M') (d : N ≅ N') : H M N ≅ H M' N' where
  hom := map e.inv d.hom
  inv := map e.hom d.inv
  hom_inv_id := by rw [hcomp, Iso.hom_inv_id, Iso.hom_inv_id, hid]
  inv_hom_id := by rw [hcomp, Iso.inv_hom_id, Iso.inv_hom_id, hid]

private def factorIso
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u})
    (hF : ∀ X : D, (Over.post (X := X) F).IsEquivalence) (M N : Modules R) :
    (restrict (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := restricted (K := K) F R)
        ((restrict (K := K) F R).obj M) ((restrict (K := K) F R).obj N) :=
  ((standardIso (K := K) F R).app _).symm ≪≫
    @asIso _ _ _ _ (directFactorMap (K := K) F R M N)
      (directFactorMap_isIso (K := K) F R hF M N) ≪≫
    bifunctorIso (SheafOfModules.homObj (R := restricted (K := K) F R))
      (fun f g ↦ SheafOfModules.homObjMap (R := restricted (K := K) F R) f g)
      (fun M N ↦ SheafOfModules.homObjMap_id.{u, u, u, u}
        (R := restricted (K := K) F R) (M := M) (N := N))
      (fun f f' g g' ↦ SheafOfModules.homObjMap_comp_homObjMap f f' g g')
      ((standardIso (K := K) F R).app M) ((standardIso (K := K) F R).app N)

private theorem factorIso_apply
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u})
    (hF : ∀ X : D, (Over.post (X := X) F).IsEquivalence) (M N : Modules R)
    (X : Dᵒᵖ)
    (φ : ((restrict (K := K) F R).obj (SheafOfModules.homObj (R := R) M N)).val.obj X)
    (Y : (Over X.unop)ᵒᵖ) (x : M.val.obj (op (F.obj Y.unop.left))) :
    (((factorIso (K := K) F R hF M N).hom.val.app X φ).app Y) x =
      φ.app (op (Over.mk (F.map Y.unop.hom))) x := by
  unfold factorIso bifunctorIso directFactorMap rawFactorMap
  rfl

attribute [local irreducible] factorIso standardIso directRestrict

private theorem restriction_products
    {C D : Type u} [SmallCategory C] [SmallCategory D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : D ⥤ C) [F.IsContinuous K J] (R : Sheaf J CommRingCat.{u}) :
    PreservesLimitsOfShape (Discrete ℤ) (restrict (K := K) F R) := by
  let T := SheafOfModules.forget (Rings (restricted (K := K) F R)) ⋙
    PresheafOfModules.toPresheaf _
  have : PreservesLimitsOfShape (Discrete ℤ) (restrict (K := K) F R ⋙ T) := by
    change PreservesLimitsOfShape (Discrete ℤ)
      ((SheafOfModules.forget (Rings R) ⋙ PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℤ) T :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ T

private theorem post_forget_equivalence
    {C : Type u} [SmallCategory C] (U : C) (X : Over U) :
    (Over.post (X := X) (Over.forget U)).IsEquivalence := by
  let : (Over.iteratedSliceForward X).IsEquivalence :=
    (Over.iteratedSliceEquiv X).isEquivalence_functor
  exact Functor.isEquivalence_of_iso (Over.iteratedSliceForwardIsoPost U X).symm

private theorem post_map_equivalence
    {C : Type u} [SmallCategory C] {U V : C} (f : V ⟶ U) (X : Over V) :
    (Over.post (X := X) (Over.map f)).IsEquivalence := by
  let G := Over.iteratedSliceForward ((Over.map f).obj X)
  let : G.IsEquivalence := (Over.iteratedSliceEquiv ((Over.map f).obj X)).isEquivalence_functor
  have : (Over.post (X := X) (Over.map f) ⋙ G).IsEquivalence := by
    change (Over.iteratedSliceForward X).IsEquivalence
    exact (Over.iteratedSliceEquiv X).isEquivalence_functor
  exact Functor.isEquivalence_of_comp_right _ G

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Preadditive.comp_zsmul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hα, hβ]

private theorem fanIso {E : Type*} [Category E] {ι : Type*}
    {A B : E} {f g : ι → E} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : IsLimit (Fan.mk A π)) (hτ : IsLimit (Fan.mk B τ)) (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

private abbrev termwise {A B : Type*} [Category A] [Category B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (T : A ⥤ B) [T.PreservesZeroMorphisms] :=
  T.mapHomologicalComplex (.up ℤ)

private theorem ordinary_map_π
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {X Y : (Complex R)ᵒᵖ × Complex R} (f : X ⟶ Y)
    (n p q : ℤ) (h : p + n = q) :
    ((ordinary R).map f).f n ≫ homComplexπ (R := R) Y.1.unop Y.2 n p q h =
      homComplexπ (R := R) X.1.unop X.2 n p q h ≫
        SheafOfModules.homObjMap (R := R) (f.1.unop.f p) (f.2.f q) :=
  homComplexFunctor_map_f_π f.1.unop f.2 n p q h

private structure ComplexHomShape (A : Type*) [Category A] [Preadditive A] where
  H : ((CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ) ⥤ CochainComplex A ℤ
  obj : A → A → A
  map : ∀ {M M' N N' : A}, (M' ⟶ M) → (N ⟶ N') → (obj M N ⟶ obj M' N')

private structure ComplexHomData {A : Type*} [Category A] [Preadditive A]
    (S : ComplexHomShape A) where
  π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ) (_h : p + n = q),
    (S.H.obj (op L, M)).X n ⟶ S.obj (L.X p) (M.X q)
  isLimit : ∀ L M n,
    IsLimit (Fan.mk ((S.H.obj (op L, M)).X n) (fun p : ℤ ↦ π L M n p (p + n) rfl))
  d_π : ∀ L M n m p q q' p' (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
    (S.H.obj (op L, M)).d n m ≫ π L M m p q hpq =
      π L M n p q' hq' ≫ S.map (𝟙 (L.X p)) (M.d q' q) -
        n.negOnePow • (π L M n p' q hp' ≫ S.map (L.d p p') (𝟙 (M.X q)))
  map_π : ∀ {X Y : (CochainComplex A ℤ)ᵒᵖ × CochainComplex A ℤ} (f : X ⟶ Y)
      n p q (h : p + n = q),
    (S.H.map f).f n ≫ π Y.1.unop Y.2 n p q h =
      π X.1.unop X.2 n p q h ≫ S.map (f.1.unop.f p) (f.2.f q)

private abbrev ComplexHomData.H {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := S.H

private abbrev ComplexHomData.obj {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := S.obj

private abbrev ComplexHomData.map {A : Type*} [Category A] [Preadditive A]
    {S : ComplexHomShape A} (_R : ComplexHomData S) := @S.map

private abbrev ordinaryShape
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : ComplexHomShape (Modules R) where
  H := ordinary R
  obj := SheafOfModules.homObj (R := R)
  map := fun f g ↦ SheafOfModules.homObjMap (R := R) f g

private def ordinaryData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) : ComplexHomData (ordinaryShape R) where
  π := homComplexπ (R := R)
  isLimit := homComplexIsLimit (R := R)
  d_π := homComplex_d_π (R := R)
  map_π := ordinary_map_π R

attribute [local irreducible] homComplexFunctor ordinaryData

private def gradedIso
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B) [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (L M : (CochainComplex A ℤ)) (n : ℤ) :
    T.obj ((R.H.obj (op L, M)).X n) ≅
      (S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).X n :=
  (fanIso _ _
    (isLimitFanMkObjOfIsLimit T _ _ (R.isLimit L M n))
    (S.isLimit ((termwise T).obj L) ((termwise T).obj M) n)
    (fun p ↦ γ (L.X p) (M.X (p + n)))).choose

private theorem gradedIso_π
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B) [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (L M : (CochainComplex A ℤ)) (n p q : ℤ) (h : p + n = q) :
    (gradedIso R S T γ L M n).hom ≫
        S.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ (γ (L.X p) (M.X q)).hom := by
  subst q
  exact (fanIso _ _
    (isLimitFanMkObjOfIsLimit T _ _ (R.isLimit L M n))
    (S.isLimit ((termwise T).obj L) ((termwise T).obj M) n)
    (fun p ↦ γ (L.X p) (M.X (p + n)))).choose_spec p

attribute [local irreducible] gradedIso

private theorem gradedIso_comm
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ))
      (n m : ℤ) (hnm : n + 1 = m) :
      (gradedIso R S T γ L M n).hom ≫
        (S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).d n m =
        T.map ((R.H.obj (op L, M)).d n m) ≫ (gradedIso R S T γ L M m).hom := by
    apply (S.isLimit ((termwise T).obj L) ((termwise T).obj M) m).hom_ext
    rintro ⟨p⟩
    change ((gradedIso R S T γ L M n).hom ≫ _) ≫
      S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl =
      (T.map _ ≫ (gradedIso R S T γ L M m).hom) ≫
      S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl
    have hH := R.d_π L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := S.d_π ((termwise T).obj L) ((termwise T).obj M)
      n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    simp only [Units.smul_def] at hH hK
    have hh := factor_differential (C := A) (D :=
      B) T
      ((R.H.obj (op L, M)).d n m)
      ((S.H.obj (op ((termwise T).obj L), (termwise T).obj M)).d n m)
      (R.π L M n p (p + n) rfl)
      (R.π L M n (p + 1) (p + m) (by omega))
      (R.π L M m p (p + m) rfl)
      (R.map (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (R.map (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (S.π ((termwise T).obj L) ((termwise T).obj M) n p (p + n) rfl)
      (S.π ((termwise T).obj L) ((termwise T).obj M) n (p + 1) (p + m) (by omega))
      (S.π ((termwise T).obj L) ((termwise T).obj M) m p (p + m) rfl)
      (S.map (𝟙 (((termwise T).obj L).X p))
        (((termwise T).obj M).d (p + n) (p + m)))
      (S.map (((termwise T).obj L).d p (p + 1))
        (𝟙 (((termwise T).obj M).X (p + m))))
      (gradedIso R S T γ L M n).hom (gradedIso R S T γ L M m).hom
      (γ (L.X p) (M.X (p + n))).hom
      (γ (L.X (p + 1)) (M.X (p + m))).hom
      (γ (L.X p) (M.X (p + m))).hom (n.negOnePow : ℤ) hH hK
      (gradedIso_π R S T γ L M n p (p + n) rfl)
      (gradedIso_π R S T γ L M n (p + 1) (p + m) (by omega))
      (gradedIso_π R S T γ L M m p (p + m) rfl)
    apply hh
    · dsimp only [termwise, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (𝟙 (L.X p)) (M.d (p + n) (p + m))
    · dsimp only [termwise, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (L.d p (p + 1)) (𝟙 (M.X (p + m)))

private def comparisonObj
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ)) :
    (termwise T).obj ((R.H).obj (op L, M)) ≅
      (S.H).obj (op ((termwise T).obj L), (termwise T).obj M) :=
  HomologicalComplex.Hom.isoOfComponents (gradedIso R S T γ L M)
    (gradedIso_comm R S T γ hγ L M)

private theorem comparisonObj_π
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ)) (n p q : ℤ) (h : p + n = q) :
    ((comparisonObj R S T γ hγ L M).hom).f n ≫
        S.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ (γ (L.X p) (M.X q)).hom :=
  gradedIso_π R S T γ L M n p q h

private theorem comparisonObj_naturality
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    {X Y : ((CochainComplex A ℤ))ᵒᵖ × (CochainComplex A ℤ)} (f : X ⟶ Y) :
      (R.H ⋙ termwise T).map f ≫ (comparisonObj R S T γ hγ Y.1.unop Y.2).hom =
        (comparisonObj R S T γ hγ X.1.unop X.2).hom ≫
          (((termwise T).op.prod (termwise T)) ⋙ S.H).map f := by
    rcases X with ⟨⟨L⟩, M⟩
    rcases Y with ⟨⟨L'⟩, M'⟩
    apply HomologicalComplex.hom_ext
    intro n
    apply (S.isLimit ((termwise T).obj L') ((termwise T).obj M') n).hom_ext
    rintro ⟨p⟩
    change (T.map (((R.H).map f).f n) ≫ (gradedIso R S T γ L' M' n).hom) ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl =
      ((gradedIso R S T γ L M n).hom ≫
          ((S.H).map (((termwise T).op.prod (termwise T)).map f)).f n) ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl
    have hR := R.map_π f n p (p + n) rfl
    have hS := S.map_π (((termwise T).op.prod (termwise T)).map f)
      n p (p + n) rfl
    change (S.H.map (((termwise T).op.prod (termwise T)).map f)).f n ≫
        S.π ((termwise T).obj L') ((termwise T).obj M') n p (p + n) rfl =
      S.π ((termwise T).obj L) ((termwise T).obj M) n p (p + n) rfl ≫
        S.map (T.map (f.1.unop.f p)) (T.map (f.2.f (p + n))) at hS
    rw [Category.assoc, gradedIso_π, ← Category.assoc, ← T.map_comp, hR,
      T.map_comp, Category.assoc, hγ, ← Category.assoc, ← gradedIso_π, Category.assoc]
    simpa only [Category.assoc] using
      congrArg ((gradedIso R S T γ L M n).hom ≫ ·) hS.symm

attribute [local irreducible] comparisonObj

private def comparison
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g)) :
    R.H ⋙ termwise T ≅ ((termwise T).op.prod (termwise T)) ⋙ S.H :=
  NatIso.ofComponents (fun X ↦ comparisonObj R S T γ hγ X.1.unop X.2)
    (fun f ↦ comparisonObj_naturality R S T γ hγ f)

private theorem comparison_π
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g))
    (L M : (CochainComplex A ℤ)) (n p q : ℤ) (h : p + n = q) :
    ((comparison R S T γ hγ).hom.app (op L, M)).f n ≫
        S.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ (γ (L.X p) (M.X q)).hom :=
  comparisonObj_π R S T γ hγ L M n p q h

attribute [local irreducible] comparison

private structure ComparisonData
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
where
  iso : R.H ⋙ termwise T ≅ ((termwise T).op.prod (termwise T)) ⋙ S.H
  π : ∀ (L M : CochainComplex A ℤ) (n p q : ℤ) (h : p + n = q),
    (iso.hom.app (op L, M)).f n ≫
        S.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ (γ (L.X p) (M.X q)).hom

private def comparisonData
    {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB)
    (T : A ⥤ B)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : A,
      T.obj (R.obj M N) ≅
        S.obj (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : A} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (R.map f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ S.map (T.map f) (T.map g)) :
    ComparisonData R S T γ where
  iso := comparison R S T γ hγ
  π := comparison_π R S T γ hγ

private theorem coherent_comparisons
    {A B E : Type*} [Category A] [Category B] [Category E]
    [Preadditive A] [Preadditive B] [Preadditive E]
    {RA : ComplexHomShape A} {SB : ComplexHomShape B}
    (R : ComplexHomData RA) (S : ComplexHomData SB) {WE : ComplexHomShape E} (W : ComplexHomData WE)
    (F : A ⥤ B) (G : B ⥤ E)
    (T : A ⥤ E) [F.Additive] [G.Additive] [T.Additive]
    (c : F ⋙ G ≅ T)
    (α : ∀ A B, F.obj (R.obj A B) ⟶
      S.obj (F.obj A) (F.obj B))
    (β : ∀ A B, G.obj (S.obj A B) ⟶
      W.obj (G.obj A) (G.obj B))
    (δ : ∀ A B, T.obj (R.obj A B) ⟶
      W.obj (T.obj A) (T.obj B))
    (a : R.H ⋙ termwise F ≅ ((termwise F).op.prod (termwise F)) ⋙ S.H)
    (b : S.H ⋙ termwise G ≅ ((termwise G).op.prod (termwise G)) ⋙ W.H)
    (d : R.H ⋙ termwise T ≅ ((termwise T).op.prod (termwise T)) ⋙ W.H)
    (ha : ∀ L M n p q h,
      (a.hom.app (op L, M)).f n ≫
        S.π ((termwise F).obj L) ((termwise F).obj M) n p q h =
      F.map (R.π L M n p q h) ≫ α (L.X p) (M.X q))
    (hb : ∀ L M n p q h,
      (b.hom.app (op L, M)).f n ≫
        W.π ((termwise G).obj L) ((termwise G).obj M) n p q h =
      G.map (S.π L M n p q h) ≫ β (L.X p) (M.X q))
    (hd : ∀ L M n p q h,
      (d.hom.app (op L, M)).f n ≫
        W.π ((termwise T).obj L) ((termwise T).obj M) n p q h =
      T.map (R.π L M n p q h) ≫ δ (L.X p) (M.X q))
    (hc : ∀ A B,
      G.map (α A B) ≫ β (F.obj A) (F.obj B) ≫
        W.map (c.inv.app A) (c.hom.app B) =
      c.hom.app (R.obj A B) ≫ δ A B) :
    Compatible (R.H) (S.H) (W.H)
      (termwise F) (termwise G) (termwise T)
      (Functor.mapHomologicalComplexCompIso c (.up ℤ)) a b d := by
  intro L M
  let cc := Functor.mapHomologicalComplexCompIso c (.up ℤ)
  apply HomologicalComplex.hom_ext
  intro n
  apply (W.isLimit ((termwise T).obj L) ((termwise T).obj M) n).hom_ext
  rintro ⟨p⟩
  let q := p + n
  have hpq : p + n = q := rfl
  change (G.map ((a.hom.app (op L, M)).f n) ≫
      (b.hom.app (op ((termwise F).obj L), (termwise F).obj M)).f n ≫
      ((W.H).map
        (X := (op ((termwise G).obj ((termwise F).obj L)),
          (termwise G).obj ((termwise F).obj M)))
        (Y := (op ((termwise T).obj L), (termwise T).obj M))
        ((cc.inv.app L).op, cc.hom.app M)).f n) ≫
      W.π ((termwise T).obj L) ((termwise T).obj M) n p q hpq =
    ((cc.hom.app ((R.H).obj (op L, M))).f n ≫
      (d.hom.app (op L, M)).f n) ≫
        W.π ((termwise T).obj L) ((termwise T).obj M) n p q hpq
  rw [Category.assoc, Category.assoc, W.map_π,
    ← Category.assoc ((b.hom.app _).f n), hb,
    Category.assoc, ← Category.assoc (G.map _), ← G.map_comp, ha,
    G.map_comp, Category.assoc]
  change G.map (F.map (R.π L M n p q hpq)) ≫
      G.map (α (L.X p) (M.X q)) ≫ β (F.obj (L.X p)) (F.obj (M.X q)) ≫
        W.map (c.inv.app (L.X p)) (c.hom.app (M.X q)) =
    (c.hom.app ((R.H.obj (op L, M)).X n) ≫
      (d.hom.app (op L, M)).f n) ≫
        W.π ((termwise T).obj L) ((termwise T).obj M) n p q hpq
  rw [hc, ← Category.assoc]
  calc
    _ = (c.hom.app ((R.H.obj (op L, M)).X n) ≫
        T.map (R.π L M n p q hpq)) ≫ δ (L.X p) (M.X q) :=
      congrArg (fun k ↦ k ≫ δ (L.X p) (M.X q))
        (c.hom.naturality (R.π L M n p q hpq))
    _ = _ := (Category.assoc _ _ _).trans
      ((congrArg (c.hom.app ((R.H.obj (op L, M)).X n) ≫ ·)
        (hd L M n p q hpq).symm).trans (Category.assoc _ _ _).symm)

private def sliceFactor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C) (A B : Modules R) :
    (SheafOfModules.overFunctor (Rings R) U).obj (SheafOfModules.homObj (R := R) A B) ≅
      SheafOfModules.homObj (R := R.over U) (A.over U) (B.over U) :=
  factorIso (K := J.over U) (Over.forget U) R (post_forget_equivalence U) A B

private def mapFactor
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {U V : C} (f : V ⟶ U)
    (A B : Modules (R.over U)) :
    (SheafOfModules.overMap (Rings R) f).obj (SheafOfModules.homObj (R := R.over U) A B) ≅
      SheafOfModules.homObj (R := R.over V)
        ((SheafOfModules.overMap (Rings R) f).obj A)
        ((SheafOfModules.overMap (Rings R) f).obj B) :=
  factorIso (K := J.over V) (Over.map f) (R.over U) (post_map_equivalence f) A B

private theorem sliceFactor_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    {A A' B B' : Modules R} (f : A' ⟶ A) (g : B ⟶ B') :
    (SheafOfModules.overFunctor (Rings R) U).map (SheafOfModules.homObjMap (R := R) f g) ≫
      (sliceFactor R U A' B').hom = (sliceFactor R U A B).hom ≫
        SheafOfModules.homObjMap (R := R.over U) (f.over U) (g.over U) := by
  unfold sliceFactor
  apply SheafOfModules.hom_ext
  ext W φ : 3
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  change (((factorIso (K := J.over U) (Over.forget U) R
      (post_forget_equivalence U) A' B').hom.val.app W
      ((SheafOfModules.homObjMap (R := R) f g).val.app
        ((Over.forget U).op.obj W) φ)).app Z) x =
    g.val.app (op Z.unop.left.left)
      ((((factorIso (K := J.over U) (Over.forget U) R
        (post_forget_equivalence U) A B).hom.val.app W φ).app Z)
          (f.val.app (op Z.unop.left.left) x))
  simp only [factorIso_apply]
  rfl

private theorem mapFactor_naturality
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {U V : C} (f : V ⟶ U)
    {A A' B B' : Modules (R.over U)} (g : A' ⟶ A) (h : B ⟶ B') :
    (SheafOfModules.overMap (Rings R) f).map (SheafOfModules.homObjMap (R := R.over U) g h) ≫
      (mapFactor R f A' B').hom = (mapFactor R f A B).hom ≫
        SheafOfModules.homObjMap (R := R.over V)
          ((SheafOfModules.overMap (Rings R) f).map g)
          ((SheafOfModules.overMap (Rings R) f).map h) := by
  unfold mapFactor
  apply SheafOfModules.hom_ext
  ext W φ : 3
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  change (((factorIso (K := J.over V) (Over.map f) (R.over U)
      (post_map_equivalence f) A' B').hom.val.app W
      ((SheafOfModules.homObjMap (R := R.over U) g h).val.app
        ((Over.map f).op.obj W) φ)).app Z) x =
    h.val.app ((Over.map f).op.obj (op Z.unop.left))
      ((((factorIso (K := J.over V) (Over.map f) (R.over U)
        (post_map_equivalence f) A B).hom.val.app W φ).app Z)
          (g.val.app ((Over.map f).op.obj (op Z.unop.left)) x))
  simp only [factorIso_apply]
  rfl

private def sliceComparisonData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) (U : C)
    [(SheafOfModules.overFunctor (Rings R) U).Additive] :=
  letI : PreservesLimitsOfShape (Discrete ℤ) (SheafOfModules.overFunctor (Rings R) U) :=
    restriction_products (K := J.over U) (Over.forget U) R
  comparisonData (ordinaryData R) (ordinaryData (R.over U))
    (SheafOfModules.overFunctor (Rings R) U) (sliceFactor R U) (sliceFactor_naturality R U)

private def mapComparisonData
    {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
    (R : Sheaf J CommRingCat.{u}) {U V : C} (f : V ⟶ U)
    [(SheafOfModules.overMap (Rings R) f).Additive] :=
  letI : PreservesLimitsOfShape (Discrete ℤ) (SheafOfModules.overMap (Rings R) f) :=
    restriction_products (K := J.over V) (Over.map f) (R.over U)
  comparisonData (ordinaryData (R.over U)) (ordinaryData (R.over V))
    (SheafOfModules.overMap (Rings R) f) (mapFactor R f) (mapFactor_naturality R f)

attribute [local irreducible] sliceComparisonData mapComparisonData

private theorem factor_coherence
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u}) {U V : C} (f : V ⟶ U) (A B : Modules R) :
    (SheafOfModules.overMap (Rings R) f).map
        ((sliceFactor R U A B).hom) ≫
      (mapFactor R f (A.over U) (B.over U)).hom ≫
      SheafOfModules.homObjMap (R := R.over V)
        ((SheafOfModules.overFunctorMap (Rings R) f).inv.app A)
        ((SheafOfModules.overFunctorMap (Rings R) f).hom.app B) =
      (SheafOfModules.overFunctorMap (Rings R) f).hom.app
          (SheafOfModules.homObj (R := R) A B) ≫
        (sliceFactor R V A B).hom := by
  unfold sliceFactor mapFactor
  apply SheafOfModules.hom_ext
  ext W φ : 3
  apply PresheafOfModules.hom_ext
  intro Z
  ext x
  change (((factorIso (K := J.over V) (Over.map f) (R.over U)
      (post_map_equivalence f) (A.over U) (B.over U)).hom.val.app W
      ((factorIso (K := J.over U) (Over.forget U) R
        (post_forget_equivalence U) A B).hom.val.app ((Over.map f).op.obj W) φ)).app Z) x =
    (((factorIso (K := J.over V) (Over.forget V) R
      (post_forget_equivalence V) A B).hom.val.app W φ).app Z) x
  simp only [factorIso_apply]
  exact factorIso_apply (K := J.over U) (Over.forget U) R
    (post_forget_equivalence U) A B ((Over.map f).op.obj W) φ
    (op (Over.mk ((Over.map f).map Z.unop.hom))) x

/-- The ordinary Hom-complex comparisons for slice restriction and relocalization form a
compatible family. No derived category, K-injective replacement, or boundedness is involved.

Source: Stacks Project, sites-cohomology.tex, Tags 0A8X and 08JB; the latter's proof refers to
this computation in the construction of internal Hom.
(auxiliary; not a blueprint node).

Proof: In degree n restrict the product over p of the sheaves Hom(L^p,M^(p+n)). Slice
restriction and relocalization preserve these products, since their underlying presheaves
are precomposition. The sheaf Hom comparison sends a local linear map to the same map on
the further slice, using the iterated-slice equivalence. Apply these factor comparisons to
the product-limit projections of homComplex. They commute with precomposition and
postcomposition, hence identify both terms of d_M f - (-1)^n f d_L. The product
isomorphisms are therefore chain isomorphisms natural in both complexes. For V to U,
successive and direct restrictions evaluate each factor at the same object over V;
composition transport is the identity there. Postcompose with every Hom-product projection
and evaluate local maps to prove the displayed compatibility. The argument applies also
to zero complexes, identity arrows, nonmonomorphisms and unbounded complexes. -/
theorem ordinary_comparisons
    {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (R : Sheaf J CommRingCat.{u})
    [∀ U : C, (SheafOfModules.overFunctor.{u} (Rings R) U).Additive]
    [∀ (U V : C) (f : V ⟶ U), (SheafOfModules.overMap.{u} (Rings R) f).Additive] :
    ∃ (a : ∀ U : C,
      ordinary R ⋙ (SheafOfModules.overFunctor.{u} (Rings R) U).mapHomologicalComplex (.up ℤ) ≅
        (((SheafOfModules.overFunctor.{u} (Rings R) U).mapHomologicalComplex (.up ℤ)).op.prod
          ((SheafOfModules.overFunctor.{u} (Rings R) U).mapHomologicalComplex (.up ℤ))) ⋙
            ordinary (R.over U))
      (b : ∀ (U V : C) (f : V ⟶ U),
        ordinary (R.over U) ⋙
            (SheafOfModules.overMap.{u} (Rings R) f).mapHomologicalComplex (.up ℤ) ≅
          (((SheafOfModules.overMap.{u} (Rings R) f).mapHomologicalComplex (.up ℤ)).op.prod
            ((SheafOfModules.overMap.{u} (Rings R) f).mapHomologicalComplex (.up ℤ))) ⋙
              ordinary (R.over V)),
      ∀ (U V : C) (f : V ⟶ U),
        Compatible (ordinary R) (ordinary (R.over U)) (ordinary (R.over V))
          ((SheafOfModules.overFunctor.{u} (Rings R) U).mapHomologicalComplex (.up ℤ))
          ((SheafOfModules.overMap.{u} (Rings R) f).mapHomologicalComplex (.up ℤ))
          ((SheafOfModules.overFunctor.{u} (Rings R) V).mapHomologicalComplex (.up ℤ))
          (Functor.mapHomologicalComplexCompIso (SheafOfModules.overFunctorMap (Rings R) f)
            (.up ℤ)) (a U) (b U V f) (a V)  := by
  refine ⟨fun U ↦ (sliceComparisonData R U).iso, fun U V f ↦ (mapComparisonData R f).iso, ?_⟩
  intro U V f
  exact coherent_comparisons (ordinaryData R) (ordinaryData (R.over U)) (ordinaryData (R.over V))
    (SheafOfModules.overFunctor (Rings R) U) (SheafOfModules.overMap (Rings R) f)
    (SheafOfModules.overFunctor (Rings R) V)
    (SheafOfModules.overFunctorMap (Rings R) f)
    (fun A B ↦ (sliceFactor R U A B).hom)
    (fun A B ↦ (mapFactor R f A B).hom)
    (fun A B ↦ (sliceFactor R V A B).hom)
    (sliceComparisonData R U).iso (mapComparisonData R f).iso (sliceComparisonData R V).iso
    (sliceComparisonData R U).π (mapComparisonData R f).π (sliceComparisonData R V).π
    (factor_coherence J R f)

end CategoryTheory.RingedHomRestriction

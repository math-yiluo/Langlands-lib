/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Restriction of Hom complexes along equivalences of sites

The site-object, site-arrow and coefficient universes are independent. Restriction is
implemented without the redundant identity change of scalars. Source: Stacks 03A0, 03CH, 03DA, 03DG,
08J7 and 0A95 (auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
universe c d vc vd r s e ve
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.NativeRestriction

/-- The ring sheaf underlying a commutative ring sheaf, with its original site and coefficient
universes.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
abbrev NativeRings {E : Type e} [Category.{ve} E] {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    (R : Sheaf τ CommRingCat.{s}) :=
  (sheafCompose τ (forget₂ CommRingCat RingCat)).obj R
/-- Module sheaves over the given commutative ring sheaf, keeping the coefficient universe
independent of both site universes.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
abbrev NativeModules {E : Type e} [Category.{ve} E] {τ : GrothendieckTopology E}
    [τ.HasSheafCompose (forget₂ CommRingCat.{s} RingCat.{s})]
    (R : Sheaf τ CommRingCat.{s}) :=
  SheafOfModules.{s} (NativeRings.{s, e, ve} R)

set_option backward.isDefEq.respectTransparency false in
private theorem restriction_map_bijective
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) [F.IsEquivalence] (R : Dᵒᵖ ⥤ RingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} R) :
    Function.Bijective (fun f : M ⟶ N ↦ (PresheafOfModules.pushforward₀ F R).map f) := by
  let W := (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ AddCommGrpCat.{max c d vc vd r}).obj F.op
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def restrictionHomMap
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
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
    { toFun := fun φ ↦ (PresheafOfModules.pushforward₀
        (Over.post (X := X.unop) F) _).map φ
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

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
@[irreducible] private def restrictionHomIso
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
    (PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj
        (PresheafOfModules.homObj M N) ≅
      PresheafOfModules.homObj (R := F.op ⋙ R)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj M)
        ((PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)).obj N) := by
  let α := restrictionHomMap.{_, _, _, _, r} F R M N
  have ha (X : Cᵒᵖ) : IsIso (α.app X) := by
    let := hF X.unop
    rw [ConcreteCategory.isIso_iff_bijective]
    exact restriction_map_bijective.{_, _, _, _, r} (Over.post (X := X.unop) F) _ _ _
  exact PresheafOfModules.isoMk (fun X ↦ asIso (α.app X)) (fun _ _ f ↦ α.naturality f)

private theorem restrictionHomIso_hom
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    (F : C ⥤ D) (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (R : Dᵒᵖ ⥤ CommRingCat.{max c d vc vd r})
    (M N : PresheafOfModules.{max c d vc vd r} (R ⋙ forget₂ _ _)) :
    (restrictionHomIso.{_, _, _, _, r} F hF R M N).hom = restrictionHomMap.{_, _, _, _, r} F R M N
      := by
  unfold restrictionHomIso
  rfl

section Restriction
variable {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
  {K : GrothendieckTopology C} {J : GrothendieckTopology D}
  (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{max c d vc vd r})

/-- The commutative ring sheaf restricted along the continuous site functor.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
abbrev restrictedCommRing :=
  (F.sheafPushforwardContinuous CommRingCat K J).obj R

/-- Direct module restriction along a continuous site functor. Restrict the underlying module
presheaf and its sheaf proof. This construction keeps the underlying module objects unchanged
and omits the redundant identity restriction of scalars.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
def restrictModules :
    NativeModules.{max c d vc vd r, d, vd} R ⥤ NativeModules.{max c d vc vd r, c, vc}
      (restrictedCommRing.{_, _, _, _, r} (K := K) F R) :=
  { obj M :=
      { val := (PresheafOfModules.pushforward₀ F
          (R.obj ⋙ forget₂ CommRingCat RingCat)).obj M.val
        isSheaf := ((F.sheafPushforwardContinuous _ K J).obj ⟨_, M.isSheaf⟩).property }
    map f := ⟨(PresheafOfModules.pushforward₀ F
      (R.obj ⋙ forget₂ CommRingCat RingCat)).map f.val⟩ }

/-- Direct restriction is additive. Its map on each component is the original map, so it preserves
the sum of two morphisms componentwise.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
instance restrictModules_additive : (restrictModules.{_, _, _, _, r} (K := K) F R).Additive := by
  constructor
  intro M N f g
  ext X x
  rfl

/-- Direct restriction agrees with the standard ringed pushforward. At each object use the identity
restriction-of-scalars isomorphism; its naturality is the componentwise identity equation.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
def restrictModules_standardIso :
    restrictModules.{_, _, _, _, r} (K := K) F R ≅
      SheafOfModules.pushforward.{max c d vc vd r} (F := F)
        (𝟙 ((F.sheafPushforwardContinuous RingCat K J).obj
          (NativeRings.{max c d vc vd r, d, vd} R))) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun X ↦
      (ModuleCat.restrictScalarsId'App _ rfl
        (((PresheafOfModules.pushforward₀ F
          (R.obj ⋙ forget₂ CommRingCat RingCat)).obj M.val).obj X)).symm)
      (by intros; ext x; rfl)) (by intros; ext X x; rfl)

private def sheafHomIso (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    (M N : NativeModules.{max c d vc vd r, d, vd} R) :
    (restrictModules.{_, _, _, _, r} (K := K) F R).obj (SheafOfModules.homObj (R := R) M N) ≅
      SheafOfModules.homObj (R := restrictedCommRing.{_, _, _, _, r} (K := K) F R)
        ((restrictModules.{_, _, _, _, r} (K := K) F R).obj M)
        ((restrictModules.{_, _, _, _, r} (K := K) F R).obj N) :=
  { hom := ⟨restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val⟩
    inv := ⟨(restrictionHomIso.{_, _, _, _, r} F hF R.obj M.val N.val).inv⟩
    hom_inv_id := by
      apply SheafOfModules.hom_ext
      change restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val ≫ _ = _
      rw [← restrictionHomIso_hom.{_, _, _, _, r} F hF R.obj M.val N.val]
      exact Iso.hom_inv_id _
    inv_hom_id := by
      apply SheafOfModules.hom_ext
      change _ ≫ restrictionHomMap.{_, _, _, _, r} F R.obj M.val N.val = _
      rw [← restrictionHomIso_hom.{_, _, _, _, r} F hF R.obj M.val N.val]
      exact Iso.inv_hom_id _ }

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

-- Categorical comparisons elaborate several nested restriction and localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem sheafHomIso_naturality
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence)
    {M M' N N' : NativeModules.{max c d vc vd r, d, vd} R} (f : M' ⟶ M) (g : N ⟶ N') :
    (restrictModules.{_, _, _, _, r} (K := K) F R).map (SheafOfModules.homObjMap (R := R) f g) ≫
        (sheafHomIso.{_, _, _, _, r} F R hF M' N').hom =
      (sheafHomIso.{_, _, _, _, r} F R hF M N).hom ≫
        SheafOfModules.homObjMap (R := restrictedCommRing.{_, _, _, _, r} (K := K) F R)
          ((restrictModules.{_, _, _, _, r} (K := K) F R).map f)
          ((restrictModules.{_, _, _, _, r} (K := K) F R).map g) := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  apply PresheafOfModules.hom_ext
  intro W
  ext x
  rfl

private theorem restrictModules_products :
    PreservesLimitsOfShape (Discrete ℤ) (restrictModules.{_, _, _, _, r} (K := K) F R) := by
  let T := SheafOfModules.forget (NativeRings.{max c d vc vd r, c, vc} (restrictedCommRing.{_, _,
    _, _, r} (K := K) F R)) ⋙
    PresheafOfModules.toPresheaf _
  have : PreservesLimitsOfShape (Discrete ℤ) (restrictModules.{_, _, _, _, r} (K := K) F R ⋙ T) :=
    by
    change PreservesLimitsOfShape (Discrete ℤ)
      ((SheafOfModules.forget (NativeRings.{max c d vc vd r, d, vd} R) ⋙
        PresheafOfModules.toPresheaf _) ⋙
        (Functor.whiskeringLeft _ _ _).obj F.op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℤ) T :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves _ T

end Restriction

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

/-- Apply an additive module restriction degreewise to a cochain complex.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
abbrev complexMap
    {A B : Type*} [Category A] [Category B] [HasZeroMorphisms A] [HasZeroMorphisms B]
    (T : A ⥤ B) [T.PreservesZeroMorphisms] := T.mapHomologicalComplex (.up ℤ)

attribute [local irreducible] homComplexFunctor

-- Categorical comparisons elaborate several nested restriction and localization functors.
-- Projection formulas require reducing the local Hom-complex abbreviations.
set_option backward.isDefEq.respectTransparency true in
private theorem homComplexFromComparison
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (R : Sheaf J CommRingCat.{max c d vc vd r}) (S : Sheaf K CommRingCat.{max c d vc vd r})
    (T : NativeModules.{max c d vc vd r, c, vc} R ⥤ NativeModules.{max c d vc vd r, d, vd} S)
      [T.Additive]
    [PreservesLimitsOfShape (Discrete ℤ) T]
    (γ : ∀ M N : NativeModules.{max c d vc vd r, c, vc} R,
      T.obj (SheafOfModules.homObj (R := R) M N) ≅
        SheafOfModules.homObj (R := S) (T.obj M) (T.obj N))
    (hγ : ∀ {M M' N N' : NativeModules.{max c d vc vd r, c, vc} R} (f : M' ⟶ M) (g : N ⟶ N'),
      T.map (SheafOfModules.homObjMap (R := R) f g) ≫ (γ M' N').hom =
        (γ M N).hom ≫ SheafOfModules.homObjMap (R := S) (T.map f) (T.map g)) :
    ∀ L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ,
      Nonempty ((complexMap T).obj (homComplex (R := R) L M) ≅
        homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)) := by
  classical
  obtain ⟨π, hπ, dπ, nπ⟩ := homComplex_projections_exists (R := R)
  obtain ⟨τ, hτ, dτ, nτ⟩ := homComplex_projections_exists (R := S)
  have hi (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ) (n : ℤ) :
      ∃ a : T.obj ((homComplex (R := R) L M).X n) ≅
          (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).X n,
        ∀ p : ℤ, a.hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
          T.map (π L M n p (p + n) rfl) ≫
            (γ (L.X p) (M.X (p + n))).hom :=
    fanIso _ _
      (isLimitFanMkObjOfIsLimit T _ _ (hπ L M n).some)
      (hτ ((complexMap T).obj L) ((complexMap T).obj M) n).some
      (fun p ↦ γ (L.X p) (M.X (p + n)))
  dsimp only [homComplex] at hi
  obtain ⟨a, ha⟩ : ∃ a : ∀ (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ) (n
    : ℤ),
      T.obj ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n) ≅
        (((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
          M)).X n,
      ∀ L M n p, (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl =
        T.map (π L M n p (p + n) rfl) ≫
          (γ (L.X p) (M.X (p + n))).hom := by
    choose a ha using hi
    exact ⟨a, ha⟩
  have ha' (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
      (a L M n).hom ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) n p q hpq =
        T.map (π L M n p q hpq) ≫ (γ (L.X p) (M.X q)).hom := by
    subst q
    exact ha L M n p
  have comm (L M : CochainComplex (NativeModules.{max c d vc vd r, c, vc} R) ℤ)
      (n m : ℤ) (hnm : n + 1 = m) :
      (a L M n).hom ≫ (homComplex (R := S) ((complexMap T).obj L) ((complexMap T).obj M)).d n m =
        T.map ((homComplex (R := R) L M).d n m) ≫ (a L M m).hom := by
    apply (hτ ((complexMap T).obj L) ((complexMap T).obj M) m).some.hom_ext
    rintro ⟨p⟩
    change ((a L M n).hom ≫ _) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl =
      (T.map _ ≫ (a L M m).hom) ≫ τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl
    have hH := dπ L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := dτ ((complexMap T).obj L) ((complexMap T).obj M) n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    simp only [Units.smul_def] at hH hK
    dsimp only [homComplex]
    have hh := factor_differential (C := NativeModules.{max c d vc vd r, c, vc} R) (D :=
      NativeModules.{max c d vc vd r, d, vd} S) T
      ((((homComplexFunctor (R := R)).obj (op L)).obj M).d n m)
      ((((homComplexFunctor (R := S)).obj (op ((complexMap T).obj L))).obj ((complexMap T).obj
        M)).d n m)
      (π L M n p (p + n) rfl)
      (π L M n (p + 1) (p + m) (by omega))
      (π L M m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := R) (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := R) (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n p (p + n) rfl)
      (τ ((complexMap T).obj L) ((complexMap T).obj M) n (p + 1) (p + m) (by omega))
      (τ ((complexMap T).obj L) ((complexMap T).obj M) m p (p + m) rfl)
      (SheafOfModules.homObjMap (R := S) (𝟙 (((complexMap T).obj L).X p))
        (((complexMap T).obj M).d (p + n) (p + m)))
      (SheafOfModules.homObjMap (R := S) (((complexMap T).obj L).d p (p + 1))
        (𝟙 (((complexMap T).obj M).X (p + m))))
      (a L M n).hom (a L M m).hom
      (γ (L.X p) (M.X (p + n))).hom
      (γ (L.X (p + 1)) (M.X (p + m))).hom
      (γ (L.X p) (M.X (p + m))).hom (n.negOnePow : ℤ) hH hK
      (ha' L M n p (p + n) rfl)
      (ha' L M n (p + 1) (p + m) (by omega))
      (ha' L M m p (p + m) rfl)
    apply hh
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (𝟙 (L.X p)) (M.d (p + n) (p + m))
    · dsimp only [complexMap, Functor.mapHomologicalComplex]
      simpa only [Functor.map_id] using
        hγ (L.d p (p + 1)) (𝟙 (M.X (p + m)))
  intro L M
  exact ⟨HomologicalComplex.Hom.isoOfComponents (a L M) (comm L M)⟩

/-- Restriction along a site equivalence commutes with the sheaf Hom complex. Full faithfulness of
the induced slice restrictions identifies the sheaves of module homomorphisms. Products of these
comparisons give an isomorphism in each degree. Naturality with respect to precomposition and
postcomposition identifies the two terms of the Hom differential, so these degreewise
isomorphisms form a cochain isomorphism. All products have indices in the fixed coefficient
universe; no site or coefficient universe is identified.

Source: Stacks 03A0, 03CH, 03DA, 03DG, 08J7 and 0A95.
(auxiliary; not a blueprint node). -/
theorem homComplexRestriction
    {C : Type c} {D : Type d} [Category.{vc} C] [Category.{vd} D]
    {K : GrothendieckTopology C} {J : GrothendieckTopology D}
    (F : C ⥤ D) [Functor.IsContinuous F K J] (R : Sheaf J CommRingCat.{max c d vc vd r})
    (hF : ∀ X : C, (Over.post (X := X) F).IsEquivalence) :
    let T := restrictModules.{_, _, _, _, r} (K := K) F R
    let S := restrictedCommRing.{_, _, _, _, r} (K := K) F R
    let Tc := T.mapHomologicalComplex (.up ℤ)
    ∀ L M : CochainComplex (NativeModules.{max c d vc vd r, d, vd} R) ℤ,
      Nonempty (Tc.obj (homComplex (R := R) L M) ≅
        homComplex (R := S) (Tc.obj L) (Tc.obj M)) := by
  let := restrictModules_products.{_, _, _, _, r} (K := K) F R
  exact homComplexFromComparison.{_, _, _, _, r} R _ _ (sheafHomIso.{_, _, _, _, r} F R hF)
    (fun f g ↦ sheafHomIso_naturality.{_, _, _, _, r} F R hF f g)

end CategoryTheory.NativeRestriction

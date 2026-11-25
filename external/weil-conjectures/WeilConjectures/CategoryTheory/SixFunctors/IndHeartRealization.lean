/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.CategoryTheory.Limits.Indization.Category
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.CategoryTheory.Presentable.Finite
/-!
# Realizing ind-objects of a finitely presentable full subcategory

Source: blueprint main-20261015, proposition-ind-constructible-sheaves,
`sk-prop-ind-heart-full-faithfulness.proof.md`, paragraphs (2) and the statement's image clause.
(blueprint: det-ind-heart-full-faithfulness-realization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe v u u₁ u₂
open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Functor

namespace IndRealization
variable {C : Type u₁} [Category.{v} C] {D : Type u₂} [Category.{v} D]
  (F : C ⥤ D) [HasFilteredColimits D]

private abbrev nerve : D ⥤ Cᵒᵖ ⥤ Type v where
  obj Y := F.op ⋙ yoneda.obj Y
  map f := whiskerLeft F.op (yoneda.map f)

private abbrev obj (Z : Ind C) : D := colimit (Z.presentation.F ⋙ F)

private def leg {X : C} {Y : D} (f : F.obj X ⟶ Y) :
    yoneda.obj X ⟶ (nerve F).obj Y where
  app W := ↾fun g ↦ F.map g ≫ f
  naturality W W' g := by
    ext h
    change F.map (g.unop ≫ h) ≫ f = F.map g.unop ≫ F.map h ≫ f
    rw [F.map_comp, Category.assoc]

private def toNerve (Z : Ind C) {Y : D} (f : obj F Z ⟶ Y) :
    (Ind.inclusion C).obj Z ⟶ (nerve F).obj Y :=
  Z.presentation.isColimit.desc
    { pt := (nerve F).obj Y
      ι :=
        { app i := leg F (colimit.ι (Z.presentation.F ⋙ F) i ≫ f)
          naturality i j a := by
            ext W g
            change F.map (g ≫ Z.presentation.F.map a) ≫
              (colimit.ι (Z.presentation.F ⋙ F) j ≫ f) =
                F.map g ≫ (colimit.ι (Z.presentation.F ⋙ F) i ≫ f)
            rw [F.map_comp, Category.assoc]
            exact congrArg (fun t ↦ F.map g ≫ t) (colimit.w_assoc
              (Z.presentation.F ⋙ F) a f) } }

private def fromNerve (Z : Ind C) {Y : D}
    (g : (Ind.inclusion C).obj Z ⟶ (nerve F).obj Y) : obj F Z ⟶ Y :=
  colimit.desc (Z.presentation.F ⋙ F)
    { pt := Y
      ι :=
        { app i := (g.app (op (Z.presentation.F.obj i)))
            ((Z.presentation.ι.app i).app _ (𝟙 _))
          naturality i j a := by
            dsimp
            simp only [Category.comp_id]
            have hg := g.naturality_apply (Z.presentation.F.map a).op
              ((Z.presentation.ι.app j).app _ (𝟙 _))
            change F.map (Z.presentation.F.map a) ≫ _ = _
            dsimp [nerve] at hg
            rw [← hg]
            congr 1
            have hp := congrArg (fun t ↦ t.app (op (Z.presentation.F.obj i)) (𝟙 _))
              (Z.presentation.ι.naturality a)
            have hn := (Z.presentation.ι.app j).naturality_apply
              (Z.presentation.F.map a).op (𝟙 (Z.presentation.F.obj j))
            dsimp at hn hp
            simp only [Category.id_comp, Category.comp_id] at hn hp
            exact hn.symm.trans hp } }

private lemma toNerve_fac (Z : Ind C) {Y : D} (f : obj F Z ⟶ Y)
    (i : Z.presentation.I) :
    Z.presentation.ι.app i ≫ toNerve F Z f =
      leg F (colimit.ι (Z.presentation.F ⋙ F) i ≫ f) :=
  Z.presentation.isColimit.fac _ i

private def homEquiv (Z : Ind C) (Y : D) :
    (obj F Z ⟶ Y) ≃ ((Ind.inclusion C).obj Z ⟶ (nerve F).obj Y) where
  toFun := toNerve F Z
  invFun := fromNerve F Z
  left_inv f := by
    apply colimit.hom_ext
    intro i
    dsimp [fromNerve]
    rw [colimit.ι_desc]
    have h := congrArg
      (fun t : yoneda.obj (Z.presentation.F.obj i) ⟶ (nerve F).obj Y ↦
        t.app (op (Z.presentation.F.obj i)) (𝟙 _)) (toNerve_fac F Z f i)
    simpa [leg] using h
  right_inv g := by
    apply Z.presentation.isColimit.hom_ext
    intro i
    rw [toNerve_fac]
    ext W h
    dsimp [leg, fromNerve]
    rw [colimit.ι_desc]
    have hg := g.naturality_apply h.op ((Z.presentation.ι.app i).app _ (𝟙 _))
    have hn := (Z.presentation.ι.app i).naturality_apply h.op (𝟙 (Z.presentation.F.obj i))
    dsimp at hg hn ⊢
    simpa using hg.symm.trans
      (congrArg (fun t : ((Ind.inclusion C).obj Z).obj W ↦ (g.app W) t) hn.symm)

private lemma toNerve_comp (Z : Ind C) {Y Y' : D} (f : obj F Z ⟶ Y) (g : Y ⟶ Y') :
    toNerve F Z (f ≫ g) = toNerve F Z f ≫ (nerve F).map g := by
  apply Z.presentation.isColimit.hom_ext
  intro i
  change Z.presentation.ι.app i ≫ toNerve F Z (f ≫ g) =
    Z.presentation.ι.app i ≫ (toNerve F Z f ≫ (nerve F).map g)
  simp only [← Category.assoc, toNerve_fac]
  ext W h
  dsimp [leg]
  simp only [Category.assoc]

private def functor : Ind C ⥤ D where
  obj := obj F
  map {Z W} f := (homEquiv F Z (obj F W)).symm
    ((Ind.inclusion C).map f ≫ toNerve F W (𝟙 _))
  map_id Z := by
    apply (homEquiv F Z _).injective
    rw [Equiv.apply_symm_apply]
    simp
    rfl
  map_comp {Z W T} f g := by
    apply (homEquiv F Z _).injective
    rw [Equiv.apply_symm_apply]
    change _ = toNerve F Z (_ ≫ _)
    rw [toNerve_comp]
    change _ = (homEquiv F Z _) ((homEquiv F Z _).symm _) ≫ _
    rw [Equiv.apply_symm_apply, Category.assoc, ← toNerve_comp, Category.id_comp]
    change _ = (Ind.inclusion C).map f ≫
      (homEquiv F W _) ((homEquiv F W _).symm _)
    rw [Equiv.apply_symm_apply, Functor.map_comp, Category.assoc]

private lemma toNerve_map_comp {Z W : Ind C} (f : Z ⟶ W) {Y : D}
    (g : (functor F).obj W ⟶ Y) :
    toNerve F Z ((functor F).map f ≫ g) =
      (Ind.inclusion C).map f ≫ toNerve F W g := by
  rw [toNerve_comp]
  change (homEquiv F Z _) ((homEquiv F Z _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply, Category.assoc, ← toNerve_comp, Category.id_comp]

private def mappedCocone {J : Type v} [SmallCategory J] (T : J ⥤ Ind C)
    (s : Cocone (T ⋙ functor F)) : Cocone (T ⋙ Ind.inclusion C) where
  pt := (nerve F).obj s.pt
  ι :=
    { app j := toNerve F (T.obj j) (s.ι.app j)
      naturality i j a := by
        dsimp
        rw [Category.comp_id, ← toNerve_map_comp]
        congr 1
        exact s.w a }

private def preserves {J : Type v} [SmallCategory J] [IsFiltered J]
    (T : J ⥤ Ind C) {c : Cocone T} (hc : IsColimit c) :
    IsColimit ((functor F).mapCocone c) where
  desc s := (homEquiv F c.pt s.pt).symm
    ((isColimitOfPreserves (Ind.inclusion C) hc).desc (mappedCocone F T s))
  fac s j := by
    apply (homEquiv F (T.obj j) s.pt).injective
    change toNerve F (T.obj j) ((functor F).map (c.ι.app j) ≫ _) = _
    rw [toNerve_map_comp]
    change _ ≫ (homEquiv F c.pt _) ((homEquiv F c.pt _).symm _) = _
    rw [Equiv.apply_symm_apply]
    exact (isColimitOfPreserves (Ind.inclusion C) hc).fac _ j
  uniq s m hm := by
    change obj F c.pt ⟶ s.pt at m
    change ∀ j, (functor F).map (c.ι.app j) ≫ m = s.ι.app j at hm
    apply (homEquiv F c.pt s.pt).injective
    change toNerve F c.pt m = (homEquiv F c.pt _) ((homEquiv F c.pt _).symm _)
    rw [Equiv.apply_symm_apply]
    apply (isColimitOfPreserves (Ind.inclusion C) hc).hom_ext
    intro j
    change (Ind.inclusion C).map (c.ι.app j) ≫ _ = _
    calc
      _ = toNerve F (T.obj j) ((functor F).map (c.ι.app j) ≫ m) :=
        (toNerve_map_comp F (c.ι.app j) m).symm
      _ = toNerve F (T.obj j) (s.ι.app j) := by rw [hm]
      _ = _ := ((isColimitOfPreserves (Ind.inclusion C) hc).fac
        (mappedCocone F T s) j).symm

private def yonedaNerve [F.Full] [F.Faithful] : yoneda ≅ F ⋙ nerve F :=
  NatIso.ofComponents (fun X ↦
    NatIso.ofComponents (fun W ↦
      ((Functor.FullyFaithful.ofFullyFaithful F).homEquiv
        (X := W.unop) (Y := X)).toIso) (by
          intro W W' a
          ext g
          exact F.map_comp a.unop g)) (by
    intro X Y f
    ext W g
    exact F.map_comp g f)

omit [HasFilteredColimits D] in
private lemma nerve_preserves (hF : ∀ X, IsFinitelyPresentable.{v} (F.obj X))
    {J : Type v} [SmallCategory J] [IsFiltered J] :
    PreservesColimitsOfShape J (nerve F) := by
  apply preservesColimitsOfShape_of_evaluation
  intro X
  have := hF X.unop
  change PreservesColimitsOfShape J (coyoneda.obj (op (F.obj X.unop)))
  infer_instance

private def nerveCocone [F.Full] [F.Faithful] (Z : Ind C) :
    Cocone (Z.presentation.F ⋙ yoneda) :=
  (Cocone.precompose (isoWhiskerLeft Z.presentation.F (yonedaNerve F)).hom).obj
    ((nerve F).mapCocone (colimit.cocone (Z.presentation.F ⋙ F)))

private def nerveCoconeIsColimit [F.Full] [F.Faithful]
    (hF : ∀ X, IsFinitelyPresentable.{v} (F.obj X)) (Z : Ind C) :
    IsColimit (nerveCocone F Z) := by
  have := nerve_preserves F hF (J := Z.presentation.I)
  exact (IsColimit.precomposeHomEquiv
    (isoWhiskerLeft Z.presentation.F (yonedaNerve F)) _).symm
      (isColimitOfPreserves (nerve F) (colimit.isColimit _))

private lemma toNerve_id_isIso [F.Full] [F.Faithful]
    (hF : ∀ X, IsFinitelyPresentable.{v} (F.obj X)) (Z : Ind C) :
    IsIso (toNerve F Z (𝟙 _)) := by
  let f : (Cocone.mk _ Z.presentation.ι) ⟶ nerveCocone F Z :=
    { hom := toNerve F Z (𝟙 _)
      w i := by
        rw [toNerve_fac]
        ext W g
        simp [leg, nerveCocone, yonedaNerve, nerve] }
  have := Z.presentation.isColimit.hom_isIso (nerveCoconeIsColimit F hF Z) f
  exact (Cocone.forget _).map_isIso f

private def fullyFaithful [F.Full] [F.Faithful]
    (hF : ∀ X, IsFinitelyPresentable.{v} (F.obj X)) : (functor F).FullyFaithful := by
  letI (Z : Ind C) : IsIso (toNerve F Z (𝟙 _)) := toNerve_id_isIso F hF Z
  exact
    { preimage := fun {Z W} f ↦ (Ind.inclusion C).preimage
        (toNerve F Z f ≫ inv (toNerve F W (𝟙 _)))
      map_preimage := fun {Z W} f ↦ by
        apply (homEquiv F Z _).injective
        change (homEquiv F Z _) ((homEquiv F Z _).symm _) = _
        rw [Equiv.apply_symm_apply, Functor.map_preimage]
        simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
        rfl
      preimage_map := fun {Z W} f ↦ by
        apply (Ind.inclusion C).map_injective
        rw [Functor.map_preimage]
        have h := toNerve_map_comp F f (𝟙 _)
        rw [Category.comp_id] at h
        rw [h]
        change (Ind.inclusion C).map f ≫ toNerve F W (𝟙 (obj F W)) ≫
          inv (toNerve F W (𝟙 (obj F W))) = _
        simp only [IsIso.hom_inv_id, Category.comp_id] }

private def yonedaHom (X : C) (Y : D) :
    ((functor F).obj (Ind.yoneda.obj X) ⟶ Y) ≃ (F.obj X ⟶ Y) :=
  (homEquiv F (Ind.yoneda.obj X) Y).trans
    ((Iso.homCongr (Ind.yonedaCompInclusion.app X) (Iso.refl _)).trans yonedaEquiv)

private lemma yonedaHom_comp (X : C) {Y Y' : D}
    (f : (functor F).obj (Ind.yoneda.obj X) ⟶ Y) (g : Y ⟶ Y') :
    yonedaHom F X Y' (f ≫ g) = yonedaHom F X Y f ≫ g := by
  dsimp [yonedaHom, homEquiv]
  rw [toNerve_comp]
  rfl

private def yonedaObjIso (X : C) :
    (functor F).obj (Ind.yoneda.obj X) ≅ F.obj X where
  hom := (yonedaHom F X _).symm (𝟙 _)
  inv := yonedaHom F X _ (𝟙 _)
  hom_inv_id := by
    apply (yonedaHom F X _).injective
    rw [yonedaHom_comp, Equiv.apply_symm_apply, Category.id_comp]
  inv_hom_id := by
    have h := yonedaHom_comp F X (𝟙 _) ((yonedaHom F X _).symm (𝟙 _))
    simpa using h.symm

private lemma yonedaHom_naturality {X Y : C} (f : X ⟶ Y) {Z : D}
    (g : (functor F).obj (Ind.yoneda.obj Y) ⟶ Z) :
    yonedaHom F X Z ((functor F).map (Ind.yoneda.map f) ≫ g) =
      F.map f ≫ yonedaHom F Y Z g := by
  change obj F (Ind.yoneda.obj Y) ⟶ Z at g
  have hn := (Ind.yonedaCompInclusion (C := C)).inv.naturality f
  change yoneda.map f ≫ (Ind.yonedaCompInclusion.app Y).inv =
    (Ind.yonedaCompInclusion.app X).inv ≫ (Ind.inclusion C).map (Ind.yoneda.map f) at hn
  change yonedaEquiv ((Ind.yonedaCompInclusion.app X).inv ≫
    toNerve F _ ((functor F).map (Ind.yoneda.map f) ≫ g)) = _
  rw [toNerve_map_comp, ← Category.assoc, ← hn,
    Category.assoc, ← yonedaEquiv_naturality]
  rfl

private def yonedaIso : Ind.yoneda ⋙ functor F ≅ F :=
  NatIso.ofComponents (yonedaObjIso F) (by
    intro X Y f
    apply (yonedaHom F X (F.obj Y)).injective
    change yonedaHom F X _ ((functor F).map (Ind.yoneda.map f) ≫ _) =
      yonedaHom F X _ (_ ≫ F.map f)
    rw [yonedaHom_naturality, yonedaHom_comp]
    change F.map f ≫ (yonedaHom F Y _) ((yonedaHom F Y _).symm (𝟙 _)) =
      (yonedaHom F X _) ((yonedaHom F X _).symm (𝟙 _)) ≫ F.map f
    simp)

private instance : PreservesFilteredColimits (functor F) := by
  constructor
  intro J _ _
  constructor
  intro T
  exact ⟨fun hc ↦ ⟨preserves F T hc⟩⟩

private def realizedColimit {J : Type v} [SmallCategory J] [IsFiltered J]
    (T : J ⥤ C) :
    (functor F).obj (colimit (T ⋙ Ind.yoneda)) ≅ colimit (T ⋙ F) :=
  preservesColimitIso (functor F) (T ⋙ Ind.yoneda) ≪≫
    HasColimit.isoOfNatIso (isoWhiskerLeft T (yonedaIso F))

end IndRealization

open IndRealization
namespace CategoryTheory

private theorem realization_essImage {D : Type u₂} [Category.{v} D] [HasFilteredColimits D]
    (P : ObjectProperty D) (M : D) :
    (IndRealization.functor P.ι).essImage M ↔ ObjectProperty.ind.{v} P M := by
  constructor
  · rintro ⟨Z, ⟨e⟩⟩
    apply (ObjectProperty.ind.{v} P).prop_of_iso e
    refine ⟨Z.presentation.I, inferInstance, inferInstance, ?_, ?_⟩
    · exact
        { diag := Z.presentation.F ⋙ P.ι
          ι := (colimit.cocone (Z.presentation.F ⋙ P.ι)).ι
          isColimit := colimit.isColimit _ }
    · intro i
      exact (Z.presentation.F.obj i).2
  · rintro ⟨J, _, _, pres, h⟩
    let T : J ⥤ P.FullSubcategory := ObjectProperty.lift P pres.diag h
    refine ⟨colimit (T ⋙ Ind.yoneda), ⟨?_⟩⟩
    exact realizedColimit P.ι T ≪≫
      (colimit.isColimit pres.diag).coconePointUniqueUpToIso pres.isColimit

end CategoryTheory

namespace CategoryTheory
/-- The ind-category of a full subcategory of finitely presentable objects realizes
fully faithfully in the ambient category with filtered colimits.

Source: blueprint main-20261015, proposition-ind-constructible-sheaves,
`sk-prop-ind-heart-full-faithfulness.proof.md`, paragraph (2), and the essential-image
clause of its statement; Stacks 05PW and 002F.
(blueprint: det-ind-heart-full-faithfulness-realization)

Proof: work directly with Mathlib ind-objects and their chosen small filtered
presentations; the essential-smallness assumption is retained to match the source
and its coefficient-heart application. Write A = P.FullSubcategory and let
F : A ⥤ C be the inclusion. For every
ind-object Z choose its Mathlib presentation Z_i and put RZ = colim_i F(Z_i).
For any Y in C, the colimit universal property and Yoneda lemma identify maps
RZ → Y with natural transformations from Z's presheaf to Hom(F(-), Y). These
bijections define R on arrows by precomposition; uniqueness gives identities
and composition, so R is an actual functor. For an ind-object W, finite
presentability of every F(Z_i) identifies Hom(F(Z_i), RW) with the colimit of
Hom(F(Z_i), F(W_j)). Fullness of F identifies this diagram with Hom(Z_i,W_j).
Taking compatible families over i gives exactly Hom(Z,W). The construction of
R on arrows is this bijection, hence R is full and faithful.

The same universal property applied to a representable gives a natural
isomorphism Ind.yoneda ⋙ R ≅ F. For an arbitrary small filtered diagram T in A,
the universal-property Hom bijection identifies R(colim Ind.yoneda(T)) with
colim F(T), compatibly with every cocone leg, proving the presentation-colimit
clause. Every image object is a filtered colimit of P-objects, hence satisfies
P.ind; this property is closed under isomorphisms. Conversely, given a witness
for P.ind M, lift its diagram to A using the witness that each object satisfies
P, take its colimit after Ind.yoneda, and apply the preceding comparison to
obtain an isomorphism from its realization to M. Thus the essential image is
precisely P.ind. This argument allows the empty property and arbitrary filtered
categories with parallel arrows, and uses only diagrams in the hom universe. -/
theorem ind_realization_of_finitelyPresentable
    {C : Type u} [Category.{v} C] [HasFilteredColimits C]
    (P : ObjectProperty C) [EssentiallySmall.{v} P.FullSubcategory]
    (hP : ∀ X : P.FullSubcategory,
      IsFinitelyPresentable.{v} (X.1 : C)) :
    ∃ Φ : Ind P.FullSubcategory ⥤ C,
      Nonempty (Ind.yoneda ⋙ Φ ≅ P.ι) ∧
      (∀ Z : Ind P.FullSubcategory,
        Nonempty (IsColimit
          (Φ.mapCocone (colimit.cocone ((Ind.presentation Z).F ⋙ Ind.yoneda))))) ∧
      Φ.Full ∧ Φ.Faithful ∧
      (∀ M : C, Φ.essImage M ↔ ObjectProperty.ind.{v} P M) := by
  let Φ := IndRealization.functor P.ι
  let hΦ := IndRealization.fullyFaithful P.ι hP
  refine ⟨Φ, ⟨IndRealization.yonedaIso P.ι⟩, ?_, hΦ.full, hΦ.faithful, ?_⟩
  · intro Z
    exact ⟨IndRealization.preserves P.ι _ (colimit.isColimit _)⟩
  · intro M
    exact realization_essImage P M
end CategoryTheory

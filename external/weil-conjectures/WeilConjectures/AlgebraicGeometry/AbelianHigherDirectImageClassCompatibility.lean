/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Adjunctions

public import WeilConjectures.AlgebraicGeometry.AbelianHigherDirectImageMap
import WeilConjectures.AlgebraicGeometry.AbelianPullbackSingleComposition
import WeilConjectures.AlgebraicGeometry.AbelianDerivedDirectImageTransitionShift

/-! # Pullback compatibility of the canonical derived-Hom class map

Source: Stacks Project, Tags 03Q8 and 09Z1.
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

private theorem adjunct_transition
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E) (θ : L' ⟶ L ⋙ P)
    {X : C} {K : D} {K' : E} (z : L.obj X ⟶ K) (t : P.obj K ⟶ K') :
    adj.homEquiv X K z ≫ adj.transitionThrough adj' P θ K K' t =
      adj'.homEquiv X K' (θ.app X ≫ P.map z ≫ t) := by
  unfold Adjunction.transitionThrough
  rw [adj.homEquiv_unit, adj'.homEquiv_unit]
  rw [Category.assoc, ← adj'.unit_naturality_assoc,
    ← adj'.unit_naturality_assoc, ← R'.map_comp, ← R'.map_comp]
  apply congrArg (fun f ↦ adj'.unit.app X ≫ R'.map f)
  rw [θ.naturality_assoc, θ.naturality_assoc]
  simp only [Functor.comp_map]
  have hc : L.map (adj.unit.app X) ≫ L.map (R.map z) ≫ adj.counit.app K = z := by
    erw [adj.counit_naturality z, ← Category.assoc, adj.left_triangle_components,
      Category.id_comp]
  rw [← P.map_comp_assoc, ← P.map_comp_assoc, Category.assoc, hc]


private theorem transitionThrough_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L : C ⥤ D} {R : D ⥤ C} {L' M : C ⥤ E} {R' : E ⥤ C}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (P : D ⥤ E)
    (e : L' ≅ M) (e' : M ≅ L ⋙ P) (K : D) {B K' : E}
    (t : P.obj K ⟶ B) (u : B ⟶ K') :
    adj.transitionThrough adj' P (e ≪≫ e').hom K K' (t ≫ u) =
      adj'.unit.app (R.obj K) ≫ R'.map
        (e.hom.app (R.obj K) ≫ e'.hom.app (R.obj K) ≫
          P.map (adj.counit.app K) ≫ t ≫ u) := by
  simp only [Adjunction.transitionThrough, Iso.trans_hom, NatTrans.comp_app, Category.assoc]

private theorem map_shifted_triangle
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    (H₀ Hₙ : C ⥤ D) (n : ℤ) (σ : shiftFunctor C n ⋙ H₀ ≅ Hₙ)
    {B Z Z' X X' : C} {A : D} (s : A ⟶ H₀.obj B)
    (f : B ⟶ Z) (r : Z ⟶ X⟦n⟧) (g : B ⟶ Z') (r' : Z' ⟶ X'⟦n⟧)
    (T : X ⟶ X') (h : f ≫ r ≫ (shiftFunctor C n).map T = g ≫ r') :
    s ≫ H₀.map f ≫ H₀.map r ≫ σ.hom.app X ≫ Hₙ.map T =
      s ≫ H₀.map g ≫ H₀.map r' ≫ σ.hom.app X' := by
  have hn := σ.hom.naturality T
  simp only [Functor.comp_map] at hn
  rw [← hn, ← H₀.map_comp_assoc, ← H₀.map_comp_assoc]
  rw [Category.assoc f r, h, H₀.map_comp, Category.assoc]

private theorem map_shifted_triangle_iso
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ]
    (H₀ Hₙ : C ⥤ D) (n : ℤ) (σ : shiftFunctor C n ⋙ H₀ ≅ Hₙ)
    {B Z Z' X X' : C} {A : D} (s : A ⟶ H₀.obj B)
    (f : B ⟶ Z) (r : Z ≅ X⟦n⟧) (g : B ⟶ Z') (r' : Z' ≅ X'⟦n⟧)
    (c : H₀.obj Z ≅ Hₙ.obj X) (c' : H₀.obj Z' ≅ Hₙ.obj X')
    (hc : c = H₀.mapIso r ≪≫ σ.app X) (hc' : c' = H₀.mapIso r' ≪≫ σ.app X')
    (T : X ⟶ X') (h : f ≫ r.hom ≫ (shiftFunctor C n).map T = g ≫ r'.hom) :
    (s ≫ H₀.map f ≫ c.hom) ≫ Hₙ.map T = s ≫ H₀.map g ≫ c'.hom := by
  rw [hc, hc']
  simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc] using
    map_shifted_triangle H₀ Hₙ n σ s f r.hom g r'.hom T h

private theorem eval_sheaf_composition
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A B D : Sheaf J AddCommGrpCat} (f : A ⟶ B) (g : B ⟶ D) (r : A ⟶ D)
    (h : f ≫ g = r) (U : Cᵒᵖ) (e : A.obj.obj U) :
    (g.hom.app U).hom ((f.hom.app U).hom e) = (r.hom.app U).hom e := by
  simpa only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] using congrArg (fun f ↦ (f.hom.app U).hom e) h

namespace AlgebraicGeometry.Etale

/-- The free abelian sheaf on an etale representable, constructed by sheafification. -/
noncomputable abbrev abelianComparisonFree (S : Scheme.{v}) :=
  uliftYoneda.{v + 1} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}

/-- Shift compatibility identifies zeroth homology of the shifted direct image with
its degree-p homology. Both factors are the specified canonical comparisons. -/
noncomputable def abelianComparisonShift {S Y : Scheme.{v}} (h : Y ⟶ S) (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (DerivedCategory.Plus.homologyFunctor _ 0).obj
        (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
          (((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
        (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).mapIso
      ((R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).app
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≪≫
    ((DerivedCategory.Plus.homologyFunctor _ 0).shiftIso (p : ℤ) 0 (p : ℤ)
      (add_zero (p : ℤ))).app _

/-- Send a raw class to a section by derived adjunction, zeroth homology, shift
comparison, and evaluation at the identity generator. This constructs the map;
it makes no choice from the mere existence of an isomorphism. -/
noncomputable def abelianHigherDirectImageClass {S Y : Scheme.{v}} (h : Y ⟶ S)
    (p : ℕ) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{v + 1}]).obj ((abelianComparisonFree S).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).obj
      (R+((h)_*[AddCommGrpCat.{v + 1}]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F))).obj.obj (op U) :=
  (((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app _ ≫
      (DerivedCategory.Plus.homologyFunctor _ 0).map
        ((upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus.homEquiv _ _
          ((((h)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app
            ((abelianComparisonFree S).obj U) ≫ z)) ≫
      (abelianComparisonShift h p F).hom).hom.app (op U)).hom
    (((toSheafify S.smallEtaleTopology
      (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 U))))

/-- The explicit class map commutes with pullback of a raw class and the canonical
higher-direct-image transition. Source: Stacks Project, Tag 03Q8 (the canonical
sectionwise comparison), Tag 09Z1 (compatibility of comparison maps).
(blueprint: lem-sbc-abelian-higher-direct-image-class-compatibility).

Proof: Write the adjunct of z as the derived unit followed by the direct image
of the single-functor comparison and z. Expand the higher-image transition as
its defining derived unit, pullback-composition comparison, counit, and coefficient
map. Naturality of the derived unit moves z through the pullback. The triangle
identity cancels the counit with the unit. The coherence of the exact pullback
single-functor comparison and the pullback-composition comparison identifies
the remaining source factor with the single of upperStarComp. Naturality of the
shift comparison moves the shifted coefficient map to the right and identifies
the result with the adjunct of the displayed pulled-back class. Applying zeroth
homology, its single-functor comparison, and the shift-to-degree-p comparison
preserves this equality. Finally evaluate at the identity generator. These are
identities of actual adjunctions and functors, valid for all schemes and all
nonnegative degrees; no geometric finiteness assumptions enter. -/
theorem abelianHigherDirectImageClass_pullback {S Y Y' : Scheme.{v}}
    (a : Y' ⟶ Y) (h : Y ⟶ S) (h' : Y' ⟶ S) (w : a ≫ h = h') (p : ℕ)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (F' : Sheaf Y'.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ((a)^*[AddCommGrpCat.{v + 1}]).obj F ⟶ F') (U : S.Etale)
    (z : (DerivedCategory.Plus.singleFunctor _ 0).obj
      (((h)^*[AddCommGrpCat.{v + 1}]).obj ((abelianComparisonFree S).obj U)) ⟶
        ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(p : ℤ)⟧) :
    (abelianHigherDirectImageMap a h h' w p F F' φ).hom.app (op U)
        (abelianHigherDirectImageClass h p F U z) =
      abelianHigherDirectImageClass h' p F' U
        ((DerivedCategory.Plus.singleFunctor _ 0).map
            ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app _) ≫
          (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
          D+((a)^*[AddCommGrpCat.{v + 1}]).map z ≫
          (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app
            ((DerivedCategory.Plus.singleFunctor _ 0).obj F) ≫
          (shiftFunctor _ (p : ℤ)).map
            ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
              (DerivedCategory.Plus.singleFunctor _ 0).map φ)) := by
  -- Eliminate equality transport before comparing the concrete derived adjunctions.
  subst h'
  let h' := a ≫ h
  have w : a ≫ h = h' := rfl
  let A := (abelianComparisonFree S).obj U
  let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
  let K' := (DerivedCategory.Plus.singleFunctor _ 0).obj F'
  let t := (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F ≫
    (DerivedCategory.Plus.singleFunctor _ 0).map φ
  let T := abelianDerivedDirectImageTransition a h h' w K K' t
  let θ := (eqToIso (congrArg
      (fun f : Y' ⟶ S => ((f)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
      w.symm) ≪≫ upperStarPlusComp AddCommGrpCat.{v + 1} a h).hom
  let adj := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h).derivedPlus
  let adj' := (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} h').derivedPlus
  let x := (((h)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ z
  let b := (DerivedCategory.Plus.singleFunctor _ 0).map
      ((upperStarComp AddCommGrpCat.{v + 1} a h h' w.symm).hom.app A) ≫
    (((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).inv.app _ ≫
    D+((a)^*[AddCommGrpCat.{v + 1}]).map z ≫
    (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K ≫
    (shiftFunctor _ (p : ℤ)).map t
  have hs := abelianPullbackSingleComposition a h h' w A
  have hb : θ.app ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≫
      D+((a)^*[AddCommGrpCat.{v + 1}]).map x ≫
      (D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K ≫
      (shiftFunctor _ (p : ℤ)).map t =
    (((h')^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ b := by
    dsimp only [θ, x, b, Iso.trans_hom, NatTrans.comp_app]
    simp only [Functor.map_comp, Category.assoc] at hs ⊢
    rw [← reassoc_of% hs]
  have hd : adj.homEquiv _ _ x ≫
      (R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K ≫
      (shiftFunctor _ (p : ℤ)).map T =
    adj'.homEquiv _ _
        ((((h')^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ b) ≫
      (R+((h')_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K' := by
    rw [← abelianDerivedDirectImageTransition_shift a h h' w K K' t (p : ℤ)]
    have hr := adjunct_transition adj adj' D+((a)^*[AddCommGrpCat.{v + 1}]) θ x
      ((D+((a)^*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K ≫
        (shiftFunctor _ (p : ℤ)).map t)
    rw [hb] at hr
    change adj.homEquiv _ _ x ≫ abelianDerivedDirectImageTransition a h h' w
      (K⟦(p : ℤ)⟧) (K'⟦(p : ℤ)⟧) _ = _ at hr
    simpa only [Category.assoc] using congrArg (fun f ↦ f ≫
      (R+((h')_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).hom.app K') hr
  let H₀ := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) 0
  let Hₚ := DerivedCategory.Plus.homologyFunctor
    (Sheaf S.smallEtaleTopology AddCommGrpCat.{v + 1}) (p : ℤ)
  have hm :
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        H₀.map (adj.homEquiv _ _ x) ≫ (abelianComparisonShift h p F).hom) ≫ Hₚ.map T =
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        H₀.map (adj'.homEquiv _ _
          ((((h')^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
            b)) ≫ (abelianComparisonShift h' p F').hom := by
    let σ : shiftFunctor _ (p : ℤ) ⋙ H₀ ≅ Hₚ :=
      H₀.shiftIso (p : ℤ) 0 (p : ℤ) (add_zero _)
    exact map_shifted_triangle_iso H₀ Hₚ (p : ℤ) σ
      ((DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A)
      (adj.homEquiv _ _ x)
      (((R+((h)_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).app K))
      (adj'.homEquiv _ _
        ((((h')^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫ b))
      (((R+((h')_*[AddCommGrpCat.{v + 1}]).commShiftIso (p : ℤ)).app K'))
      (abelianComparisonShift h p F) (abelianComparisonShift h' p F') rfl rfl T hd
  have ht : Hₚ.map T = abelianHigherDirectImageMap a h h' w p F F' φ := by
    exact congrArg Hₚ.map (transitionThrough_comp adj adj'
      D+((a)^*[AddCommGrpCat.{v + 1}])
      (eqToIso (congrArg
        (fun f : Y' ⟶ S => ((f)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlus)
        w.symm)) (upperStarPlusComp AddCommGrpCat.{v + 1} a h) K
      ((((a)^*[AddCommGrpCat.{v + 1}]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
      ((DerivedCategory.Plus.singleFunctor _ 0).map φ))
  let e := (((toSheafify S.smallEtaleTopology
    (uliftYoneda.{v + 1}.obj U ⋙ AddCommGrpCat.free)).app (op U)).hom
      (FreeAbelianGroup.of (ULift.up (𝟙 U))))
  rw [ht] at hm
  have he := eval_sheaf_composition _ _ _ hm (op U) e
  exact he

end AlgebraicGeometry.Etale

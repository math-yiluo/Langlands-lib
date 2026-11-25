/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
public import WeilConjectures.AlgebraicGeometry.PinnedPullbackCompositionShifts
import all WeilConjectures.AlgebraicGeometry.AffineSpectrumCompositionCounitSquare

/-! # Counit comparison for one open leg
Source: Stacks Project, Tags 08DW and 0D5S. -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
private theorem mapFactorizationCancel
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B E H : C} (a : A ⟶ B) (b : B ⟶ E) (l : A ⟶ H)
    (i : H ⟶ E) (v : E ⟶ H) (ho : a ≫ b = l ≫ i) (hi : i ≫ v = 𝟙 H) :
    F.map a ≫ F.map b ≫ F.map v = F.map l := by
  simp only [← F.map_comp]
  rw [← Category.assoc, ho, Category.assoc, hi, Category.comp_id]

private theorem mappedHomotopyInvHom
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] {F R : C ⥤ D} [F.Additive] [R.Additive]
    (e : F ≅ R) (P : HomotopyCategory C (.up ℤ))
    (q : HomotopyCategory D (.up ℤ) ⥤ E) :
    q.map ((NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app P) ≫
      q.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) = 𝟙 _ := by
  rw [← q.map_comp, ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp,
    e.inv_hom_id, NatTrans.mapHomotopyCategory_id, NatTrans.id_app, q.map_id]

variable [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
  (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]

/-- Termwise comparison for restricting the source before tensor pullback.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-source-counit-triangle). -/
def openPinnedHomotopySourceCompositionIso
    {X : Scheme.{u}} (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme) :
    (Scheme.Modules.tensorPullback (j ≫ U.ι)).mapHomotopyCategory (.up ℤ) ≅
      (schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) ⋙
        (Scheme.Modules.tensorPullback j).mapHomotopyCategory (.up ℤ) := by
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  exact (Functor.mapHomotopyCategoryCompIso
    (Functor.isoWhiskerRight (openPinnedTensorOpenIso X U).symm _ ≪≫
      (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm)
    (.up ℤ)).symm

-- Keep the selected pullback data abstract while comparing its canonical maps.
attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
attribute [local instance_reducible] Scheme.Modules TopCat.Sheaf
attribute [local implicit_reducible] DerivedCategory
  HomotopyCategory DerivedCategory.Q DerivedCategory.Qh

omit [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive] in
private theorem homotopyCompositionComparison
    {C D E : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    [Category E] [Preadditive E]
    {F R : C ⥤ D} {G : D ⥤ E} {H : C ⥤ E}
    [F.Additive] [R.Additive] [G.Additive] [H.Additive]
    (e : F ≅ R) (a : F ⋙ G ≅ H) (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P ≫
        (Functor.mapHomotopyCategoryCompIso
          (Functor.isoWhiskerRight e.symm G ≪≫ a) (.up ℤ)).inv.app P =
      (G.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  change (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso a (.up ℤ)).hom.app K) ≫
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((Functor.mapHomologicalComplexCompIso
        (Functor.isoWhiskerRight e.symm G ≪≫ a) (.up ℤ)).inv.app K) =
    (HomotopyCategory.quotient E (.up ℤ)).map
      ((G.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K))
  rw [← Functor.map_comp]
  congr 1
  ext n
  simp [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    NatTrans.mapHomologicalComplex]

private theorem compositionCounit
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) (.up ℤ)) :
    (pinnedPullbackComposition.{u, w} f g).hom.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u, w} (f ≫ g)).app P =
      (derivedPullback f).map ((pinnedPullbackCounit.{u, w} g).app P) ≫
        (pinnedPullbackCounit.{u, w} f).app
          ((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ) |>.obj P) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso
            (Scheme.Modules.tensorPullbackCompositionIso f g (f ≫ g) rfl).symm
            (.up ℤ)).hom.app P) := by
  classical
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) (f ≫ g)
  have := hL
  have hc := (Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))).1 f g
  have he := congrArg (fun t ↦ t.app (DerivedCategory.Qh.obj P) ≫
    (pinnedPullbackCounit (f ≫ g)).app P) hc
  simp only [Functor.leftDerived_fac_app, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.id_comp] at he
  have hm := congrArg (fun a :
      Scheme.Modules.tensorPullback g ⋙ Scheme.Modules.tensorPullback f ≅
        Scheme.Modules.tensorPullback (f ≫ g) ↦
      (DerivedCategory.Qh
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).map
          ((Functor.mapHomotopyCategoryCompIso a (.up ℤ)).hom.app P))
    (SingleComplexBaseChange.tensor_composition_symm f g)
  exact he.trans (congrArg (fun v ↦
    (derivedPullback f).map ((pinnedPullbackCounit g).app P) ≫
      (pinnedPullbackCounit f).app
        (((Scheme.Modules.tensorPullback g).mapHomotopyCategory (.up ℤ)).obj P) ≫ v)
    hm.symm)


private theorem openCounit
    (X : Scheme.{u}) (U : X.Opens)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (singleComplexOpenPullbackIso X U).inv.app (DerivedCategory.Qh.obj P) ≫
        (pinnedPullbackCounit.{u, w} U.ι).app P =
      (schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (openPinnedTensorOpenIso X U).inv (.up ℤ)).app P) := by
  classical
  let T : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤
      SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace) :=
    Scheme.Modules.tensorPullback U.ι
  let e : schemeOpenRestriction X U ≅ T := (openPinnedTensorOpenIso X U).symm
  have : PreservesFiniteLimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteLimits X U
  have : PreservesFiniteColimits (schemeOpenRestriction X U) :=
    schemeOpenRestriction_preservesFiniteColimits X U
  have : PreservesFiniteLimits T := preservesFiniteLimits_of_natIso e
  have : PreservesFiniteColimits T := preservesFiniteColimits_of_natIso e
  have hL := (Classical.choose (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w}))) U.ι
  have := hL
  have : T.mapDerivedCategory.IsLeftDerivedFunctor T.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ T.mapDerivedCategoryFactorsh
  have he := Functor.mapDerivedCategoryNatIso_fach e P
  dsimp only [singleComplexOpenPullbackIso, Iso.trans_inv, NatTrans.comp_app]
  have hθ : Scheme.Modules.overFunctorEquiv U ≪≫
      ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction U.ι)).leftAdjointUniq
        (Scheme.Modules.pullbackPushforwardAdjunction U.ι) ≪≫
          (Scheme.Modules.restrictFunctorIsoPullback U.ι).symm).symm = e := by
    simp only [e, openPinnedTensorOpenIso, Iso.trans_symm,
      Iso.symm_symm_eq, Iso.trans_assoc]
  rw [hθ]
  simp only [Iso.symm_inv, Category.assoc, Functor.leftDerivedUnique,
    Functor.leftDerivedNatIso_inv, Functor.leftDerivedNatTrans_app,
    Iso.refl_inv, NatTrans.id_app, Category.comp_id]
  exact he

omit [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
  [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive] in
private theorem sourceTriangleAlgebra
    {C : Type*} [Category C] {A B C₁ D E F G H : C}
    (a : A ⟶ B) (b : B ⟶ C₁) (c : C₁ ⟶ D) (d : D ⟶ E)
    (e : B ⟶ F) (f : F ⟶ G) (g : G ⟶ D)
    (h : G ⟶ E) (i : F ⟶ H) (l : A ⟶ H) (m : H ⟶ E)
    (hbc : b ≫ c = e ≫ f ≫ g) (hgd : g ≫ d = h)
    (hfh : f ≫ h = i ≫ m) (haei : a ≫ e ≫ i = l) :
    a ≫ b ≫ c ≫ d = l ≫ m := by
  calc
    a ≫ b ≫ c ≫ d = a ≫ (b ≫ c) ≫ d := by simp only [Category.assoc]
    _ = a ≫ (e ≫ f ≫ g) ≫ d := by rw [hbc]
    _ = a ≫ e ≫ f ≫ (g ≫ d) := by simp only [Category.assoc]
    _ = a ≫ e ≫ (f ≫ h) := by rw [hgd]
    _ = a ≫ e ≫ (i ≫ m) := by rw [hfh]
    _ = (a ≫ e ≫ i) ≫ m := by simp only [Category.assoc]
    _ = l ≫ m := by rw [haei]

-- The final calculation uses these constructions only through their interfaces.
attribute [local irreducible] singleComplexOpenPullbackIso openPinnedTensorOpenIso

-- Elaborating the four equations compares several selected localization functors.
/-- The source-open leg of the derived counit composition calculation.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-open-pinned-source-counit-triangle).
Proof: factor the selected composition comparison followed by the composite
counit into the counit of U inclusion, then the counit of j, then the
underived composition comparison. Cancel that last comparison against its
inverse in the displayed source comparison. Naturality of the counit for j
moves the underived open tensor comparison to its source. The factorization
of leftDerivedUnique for the open inclusion replaces the counit for U and
the open tensor comparison by the open derived comparison and the exact
restriction factor. Cancel the inverse open derived comparison. Every step
is natural in P and requires no target open or commuting square. -/
theorem open_pinned_source_counit_triangle
    {X : Scheme.{u}} (U : X.Opens) {Y : Scheme.{u}} (j : Y ⟶ U.toScheme)
    (P : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    (derivedPullback j).map ((singleComplexOpenPullbackIso X U).inv.app
        (DerivedCategory.Qh.obj P)) ≫
      (pinnedPullbackComposition.{u, w} j U.ι).hom.app (DerivedCategory.Qh.obj P) ≫
      (pinnedPullbackCounit.{u, w} (j ≫ U.ι)).app P ≫
      DerivedCategory.Qh.map ((openPinnedHomotopySourceCompositionIso U j).hom.app P) =
    (derivedPullback j).map ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P) ≫
      (pinnedPullbackCounit.{u, w} j).app
        ((schemeOpenRestriction X U).mapHomotopyCategory (.up ℤ) |>.obj P) := by
  have : (schemeOpenRestriction X U).Additive := schemeOpenRestriction_additive X U
  let e := openPinnedTensorOpenIso X U
  let q := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings Y.toRingedSpace))
  let v := (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P
  let vi := (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app P
  have hc := compositionCounit.{u, w} j U.ι P
  have ht := homotopyCompositionComparison e
    (Scheme.Modules.tensorPullbackCompositionIso j U.ι (j ≫ U.ι) rfl).symm P
  have hg := congrArg q.map ht
  simp only [q.map_comp] at hg
  have hn := (pinnedPullbackCounit.{u, w} j).naturality v
  let qU := DerivedCategory.Qh
    (C := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
  have hiQ := mappedHomotopyInvHom e P qU
  have hs := mapFactorizationCancel (derivedPullback j)
    ((singleComplexOpenPullbackIso X U).inv.app (DerivedCategory.Qh.obj P))
    ((pinnedPullbackCounit U.ι).app P)
    ((schemeOpenRestriction X U).mapDerivedCategoryFactorsh.hom.app P)
    (qU.map vi) (qU.map v) (openCounit X U P) hiQ
  exact sourceTriangleAlgebra _ _ _ _ _ _ _ _ _ _ _ hc hg hn.symm hs

end AlgebraicGeometry

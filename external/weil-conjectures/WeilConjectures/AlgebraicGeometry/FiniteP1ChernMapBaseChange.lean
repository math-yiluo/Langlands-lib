/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import all WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj

/-! # Base change of the projective-line Chern map

This is the geometric Chern-square part of the adjunct base-change argument.
(auxiliary; not a blueprint node)
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

-- Reuse the proposition instances already stored in the ordinary derived category.
-- Elaborate every helper interface with these same canonical localization arguments.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem rootMap_pullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (upperStar AddCommGrpCat.{u + 1} f).map (ordinaryFiniteRootMap A N hA Y) ≫
        (moduleAbelianUpperStarComparison A f).app _ ≫
        (moduleAbelianForget A X).map (t.line f hY).hom =
      (t.roots f hY).hom ≫ ordinaryFiniteRootMap A N hA X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  ext W z
  exact (t.line_normalization f hY W 1 z)

private theorem roots_eq_canonical (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    (t.roots f hY).hom = Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N f := by
  apply (cancel_mono (kernel.ι (N • 𝟙 X.gmSheaf))).1
  exact (t.roots_normalization f hY).symm.trans
    (Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf_ι N f).symm

private theorem p1_pic_pullback {S' S : Scheme.{u}} (f : S' ⟶ S) :
    Scheme.Pic.map (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
        (ordinaryFiniteP1PicardClass S) = ordinaryFiniteP1PicardClass S' := by
  unfold ordinaryFiniteP1PicardClass
  apply (Scheme.Pic.eq_ofIsInvertible_iff _ _).2
  exact ⟨fromSkeletonToSkeletonIso _ ≪≫
    (Scheme.Modules.pullback (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).mapIso
      (Scheme.Pic.ofIsInvertibleIso (ProjectiveSpace.twist (ULift.{u} (Fin 2)) S 1)) ≪≫
    ProjectiveSpace.pullbackMapTwistIso (ULift.{u} (Fin 2)) f 1⟩

private theorem forget_lowerStar_map (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)} (a : F ⟶ G) :
    (moduleAbelianForget A Y).map ((lowerStar (ModuleCat.{u + 1} A) f).map a) =
      (lowerStar AddCommGrpCat.{u + 1} f).map ((moduleAbelianForget A X).map a) := by
  rfl

private theorem integralGenerator_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar AddCommGrpCat.{u + 1} f).map (ordinaryFiniteIntegralGenerator A Y) ≫
        (moduleAbelianUpperStarComparison A f).app _ ≫
        (moduleAbelianForget A X).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
            (ModuleCat.of A A)).hom =
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).hom ≫
        ordinaryFiniteIntegralGenerator A X := by
  apply (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _ |>.injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    Adjunction.homEquiv_naturality_right]
  dsimp only [moduleAbelianUpperStarComparison]
  erw [Equiv.apply_symm_apply]
  have h := coefficient_unit A f
  simpa only [supportedConstantUnit, supportedIntegralUnit, supportedIntegralGenerator,
    Adjunction.homEquiv_unit, Functor.map_comp, forget_lowerStar_map, Category.assoc,
    moduleAbelianForget] using h

private theorem class_ext_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Q' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : (upperStar (ModuleCat.{u + 1} A) f).obj Q ⟶ Q') (n : ℕ)
    (x : Ext (ordinaryFiniteConstant A Y) Q n) :
    ordinaryFiniteExtClassCore (moduleAbelianForget A X)
      (ordinaryFiniteIntegralGenerator A X) Q' n
      (Ext.mk₀CompMk₀
        ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).inv.app
          (ModuleCat.of A A))
        (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) f)) a) =
      Sheaf.H.map ((moduleAbelianUpperStarComparison A f).app Q ≫
        (moduleAbelianForget A X).map a) n
        (cohomologyMap f _ n (ordinaryFiniteExtClassCore (moduleAbelianForget A Y)
          (ordinaryFiniteIntegralGenerator A Y) Q n x)) := by
  unfold ordinaryFiniteExtClassCore
  let M := upperStar (ModuleCat.{u + 1} A) f
  let U := upperStar AddCommGrpCat.{u + 1} f
  let G := moduleAbelianForget A Y
  let G' := moduleAbelianForget A X
  let e := moduleAbelianUpperStarIso A f
  let c := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) f).app
    (ModuleCat.of A A)
  let z := (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).app
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  let : PreservesFiniteLimits (G ⋙ U) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (G ⋙ U) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteLimits (M ⋙ G') := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (M ⋙ G') := comp_preservesFiniteColimits _ _
  have hx : (x.mapExactFunctor M).mapExactFunctor G' =
      Ext.mk₀CompMk₀ (e.inv.app _) ((x.mapExactFunctor G).mapExactFunctor U)
        (e.hom.app Q) := by
    rw [Ext.mapExactFunctor_mapExactFunctor, Ext.mapExactFunctor_mapExactFunctor]
    exact Ext.mapExactFunctor_eq_mk₀CompMk₀_of_iso e x
  have hgen : ordinaryFiniteIntegralGenerator A X ≫ G'.map c.inv ≫ e.inv.app _ =
      z.inv ≫ U.map (ordinaryFiniteIntegralGenerator A Y) := by
    apply (cancel_mono (e.hom.app _ ≫ G'.map c.hom)).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← G'.map_comp,
      Iso.inv_hom_id, G'.map_id]
    change ordinaryFiniteIntegralGenerator A X = z.inv ≫
      (U.map (ordinaryFiniteIntegralGenerator A Y) ≫ e.hom.app _ ≫ G'.map c.hom)
    have hg := integralGenerator_pullback A f
    change U.map (ordinaryFiniteIntegralGenerator A Y) ≫ e.hom.app _ ≫ G'.map c.hom =
      z.hom ≫ ordinaryFiniteIntegralGenerator A X at hg
    rw [hg]
    simp only [Iso.inv_hom_id_assoc]
  change (Ext.mk₀ (ordinaryFiniteIntegralGenerator A X)).comp
    ((Ext.mk₀CompMk₀ c.inv (x.mapExactFunctor M) a).mapExactFunctor G') (zero_add n) = _
  rw [Ext.mapExactFunctor_mk₀CompMk₀, hx, Ext.mk₀CompMk₀_mk₀CompMk₀,
    Ext.mk₀_comp_mk₀CompMk₀, hgen]
  rw [Sheaf.H.map_apply, cohomologyMap_apply, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_mk₀]
  simp only [Ext.mk₀CompMk₀, Ext.mk₀_comp_mk₀_assoc,
    Ext.comp_assoc_of_third_deg_zero]
  rfl

private theorem cached_ext_conjugation (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) {M' M Q Q' : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (n : ℕ) (a : M' ⟶ M) (x : Ext M Q n) (b : Q ⟶ Q') :
    ordinaryFiniteExtHomEquiv A T M' Q' n (Ext.mk₀CompMk₀ a x b) =
      (ordinaryFiniteSingleFunctor A T).map a ≫
        ordinaryFiniteExtHomEquiv A T M Q n x ≫
          (shiftFunctor (DerivedCategoryModule A T) (n : ℤ)).map
            ((ordinaryFiniteSingleFunctor A T).map b) := by
  simp only [ordinaryFiniteExtHomEquiv_eq, ordinaryFiniteSingleFunctor_eq,
    Ext.mk₀CompMk₀, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

private theorem cached_ext_exact_map (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (n : ℕ) (x : Ext M Q n) :
    ordinaryFiniteExtHomEquiv A X _ _ n
        (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) f)) =
      (ordinaryFiniteSingleExactPullbackIso A f).inv.app M ≫
        ShiftedHom.map (ordinaryFiniteExtHomEquiv A Y M Q n x)
          (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≫
        ((ordinaryFiniteSingleExactPullbackIso A f).hom.app Q)⟦(n : ℤ)⟧' := by
  simp only [ordinaryFiniteExtHomEquiv_eq, ordinaryFiniteSingleFunctor_eq,
    ordinaryFiniteSingleExactPullbackIso_eq]
  exact Ext.mapExactFunctor_hom (upperStar (ModuleCat.{u + 1} A) f) x

private theorem cached_ext_pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (n : ℕ) (x : Ext M Q n) :
    letI : (ordinaryFinitePullback A f).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
    (ordinaryFinitePullback A f).map (ordinaryFiniteExtHomEquiv A Y M Q n x) ≫
        ((ordinaryFinitePullback A f).commShiftIso (n : ℤ)).hom.app _ ≫
          ((ordinaryFiniteSinglePullbackIso A f).hom.app Q)⟦(n : ℤ)⟧' =
      (ordinaryFiniteSinglePullbackIso A f).hom.app M ≫
        ordinaryFiniteExtHomEquiv A X
          ((upperStar (ModuleCat.{u + 1} A) f).obj M)
          ((upperStar (ModuleCat.{u + 1} A) f).obj Q) n
          (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) f)) := by
  let : (ordinaryFinitePullback A f).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f
  let F := upperStar (ModuleCat.{u + 1} A) f
  let ε : ordinaryFinitePullback A f ≅ F.mapDerivedCategory :=
    leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f
  have h := cached_ext_exact_map A f M Q n x
  have hcs : ((ordinaryFinitePullback A f).commShiftIso (n : ℤ)).hom.app
      ((ordinaryFiniteSingleFunctor A Y).obj Q) =
      ε.hom.app _ ≫ (F.mapDerivedCategory.commShiftIso (n : ℤ)).hom.app _ ≫
        (ε.inv.app _)⟦(n : ℤ)⟧' :=
    Functor.CommShift.ofIso_commShiftIso_hom_app _ _ _ _
  rw [hcs, h]
  unfold ordinaryFiniteSinglePullbackIso
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  have hε := ε.hom.naturality (ordinaryFiniteExtHomEquiv A Y M Q n x)
  rw [reassoc_of% hε]
  erw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  simp only [ShiftedHom.map, Category.assoc]
  rw [Iso.hom_inv_id_app_assoc]

attribute [local irreducible] ordinaryFiniteRootMap Sheaf.H.map cohomologyMap

private theorem kummer_boundary_map_pullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (B : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (B' : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (r : Y.rootsOfUnitySheaf N ⟶ B) (r' : X.rootsOfUnitySheaf N ⟶ B')
    (b : (upperStar AddCommGrpCat.{u + 1} f).obj B ⟶ B')
    (hr : (upperStar AddCommGrpCat.{u + 1} f).map r ≫ b =
      Scheme.upperStarRootsOfUnitySheafToRootsOfUnitySheaf N f ≫ r')
    (L : Y.Pic) (L' : X.Pic) (hL : Scheme.Pic.map f L = L') :
    Sheaf.H.map b 2 (cohomologyMap f B 2
      (Sheaf.H.map r 2 (Y.kummerδ₁ N hY
        (Scheme.Pic.toCohomologicalPicardGroup Y L)))) =
      Sheaf.H.map r' 2 (X.kummerδ₁ N hX
        (Scheme.Pic.toCohomologicalPicardGroup X L')) := by
  rw [cohomologyMap_map]
  erw [← Sheaf.H.map_comp_apply, hr, Sheaf.H.map_comp_apply]
  change Sheaf.H.map r' 2 (Scheme.rootsOfUnityCohomologyMap f N 2 _) = _
  rw [Scheme.rootsOfUnityCohomologyMap_kummerδ₁ _ _ hY hX,
    Scheme.gmCohomologyMap_toCohomologicalPicardGroup, hL]

private theorem kummer_class_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (L : Y.Pic) (L' : X.Pic) (hL : Scheme.Pic.map f L = L') :
    Sheaf.H.map ((moduleAbelianUpperStarComparison A f).app _ ≫
        (moduleAbelianForget A X).map (t.line f hY).hom) 2
      (cohomologyMap f _ 2 (ordinaryFiniteKummerClass A N hA Y hY L)) =
      ordinaryFiniteKummerClass A N hA X hX L' := by
  have hr := rootMap_pullback A N hA t f hY
  rw [roots_eq_canonical] at hr
  unfold ordinaryFiniteKummerClass
  exact kummer_boundary_map_pullback f N hY hX _ _ _ _ _ hr L L' hL

attribute [local irreducible] ordinaryFiniteUnitPullback
  ordinaryFiniteShiftedLinePullback ordinaryFiniteIntegralGenerator
  Scheme.finiteEtaleTateLine
  ordinaryFiniteSinglePullbackIso ordinaryFiniteSingleExactPullbackIso
  ordinaryFiniteExtHomEquiv ordinaryFiniteKummerClass

private theorem conjugate_comparison
    {D : Type*} [Category D] (T : D ⥤ D)
    {A₀ A₁ A₂ B₀ B₁ B₂ C : D}
    (α : A₀ ≅ A₁) (r : A₁ ≅ A₂) (β : B₀ ≅ B₁) (l : B₁ ≅ B₂)
    (σ : C ≅ T.obj B₀) (m : A₀ ⟶ C) (y : A₁ ⟶ T.obj B₁)
    (h : m ≫ σ.hom ≫ T.map β.hom = α.hom ≫ y) :
    (α ≪≫ r).inv ≫ m ≫ (σ ≪≫ T.mapIso (β ≪≫ l)).hom =
      r.inv ≫ y ≫ T.map l.hom := by
  simp only [Iso.trans_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp]
  calc
    _ = r.inv ≫ α.inv ≫ (m ≫ σ.hom ≫ T.map β.hom) ≫ T.map l.hom := by
      simp only [Category.assoc]
    _ = _ := by rw [h]; simp only [Category.assoc, Iso.inv_hom_id_assoc]

private theorem cached_ext_pullback_conj
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (M Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    {M' Q' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (a : (upperStar (ModuleCat.{u + 1} A) g).obj M ≅ M')
    (b : (upperStar (ModuleCat.{u + 1} A) g).obj Q ≅ Q')
    (n : ℕ) (x : Ext M Q n) :
    letI : (ordinaryFinitePullback A g).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) g
    ((ordinaryFiniteSinglePullbackIso A g).app M ≪≫
        (ordinaryFiniteSingleFunctor A X).mapIso a).inv ≫
      (ordinaryFinitePullback A g).map (ordinaryFiniteExtHomEquiv A Y M Q n x) ≫
      (((ordinaryFinitePullback A g).commShiftIso (n : ℤ)).app
          ((ordinaryFiniteSingleFunctor A Y).obj Q) ≪≫
        (shiftFunctor (DerivedCategoryModule A X) (n : ℤ)).mapIso
          ((ordinaryFiniteSinglePullbackIso A g).app Q ≪≫
            (ordinaryFiniteSingleFunctor A X).mapIso b)).hom =
      ordinaryFiniteExtHomEquiv A X M' Q' n
        (Ext.mk₀CompMk₀ a.inv
          (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)) b.hom) := by
  let : (ordinaryFinitePullback A g).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) g
  let E := ordinaryFiniteExtHomEquiv A Y M Q n
  let α := (ordinaryFiniteSinglePullbackIso A g).app M
  let β := (ordinaryFiniteSinglePullbackIso A g).app Q
  let r := (ordinaryFiniteSingleFunctor A X).mapIso a
  let l := (ordinaryFiniteSingleFunctor A X).mapIso b
  let σ := ((ordinaryFinitePullback A g).commShiftIso (n : ℤ)).app
    ((ordinaryFiniteSingleFunctor A Y).obj Q)
  let T := shiftFunctor (DerivedCategoryModule A X) (n : ℤ)
  have hd := cached_ext_pullback A g M Q n x
  have hc := cached_ext_conjugation A X n a.inv
    (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)) b.hom
  exact (conjugate_comparison T α r β l σ
    ((ordinaryFinitePullback A g).map (E x)) _ hd).trans hc.symm

private theorem class_pullback_of_equiv
    {U : Type*} {V : Type*} {C : Type*} {D : Type*} {K : Type*} {L : Type*}
    (e : U ≃ C) (e' : V ≃ D) (p : U → V) (q : C → D)
    (a : C → K) (b : D → L) (a' : U → K) (b' : V → L) (h : K → L)
    (hq : ∀ x, q (e x) = e' (p x))
    (ha : ∀ x, a (e x) = a' x) (hb : ∀ x, b (e' x) = b' x)
    (hp : ∀ x, b' (p x) = h (a' x)) (c : C) :
    b (q c) = h (a c) := by
  obtain ⟨x, rfl⟩ := e.surjective c
  rw [hq, hb, hp, ha]

private theorem class_pullback
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (Q : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (Q' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (a : (upperStar (ModuleCat.{u + 1} A) g).obj Q ≅ Q') (n : ℕ)
    (c : ordinaryFiniteUnit A Y ⟶ ((ordinaryFiniteSingleFunctor A Y).obj Q)⟦(n : ℤ)⟧) :
    letI : (ordinaryFinitePullback A g).CommShift ℤ :=
      commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) g
    ordinaryFiniteClass A X Q' n
        ((ordinaryFiniteUnitPullback A g).inv ≫ (ordinaryFinitePullback A g).map c ≫
          (((ordinaryFinitePullback A g).commShiftIso (n : ℤ)).app
              ((ordinaryFiniteSingleFunctor A Y).obj Q) ≪≫
            (shiftFunctor (DerivedCategoryModule A X) (n : ℤ)).mapIso
              ((ordinaryFiniteSinglePullbackIso A g).app Q ≪≫
                (ordinaryFiniteSingleFunctor A X).mapIso a)).hom) =
      Sheaf.H.map ((moduleAbelianUpperStarComparison A g).app Q ≫
        (moduleAbelianForget A X).map a.hom) n
        (cohomologyMap g _ n (ordinaryFiniteClass A Y Q n c)) := by
  let : (ordinaryFinitePullback A g).CommShift ℤ :=
    commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) g
  rw [ordinaryFiniteUnitPullback_eq]
  let E := ordinaryFiniteExtHomEquiv A Y (ordinaryFiniteConstant A Y) Q n
  let E' := ordinaryFiniteExtHomEquiv A X (ordinaryFiniteConstant A X) Q' n
  let e := (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} A) g).app
    (ModuleCat.of A A)
  let p := fun x : Ext (ordinaryFiniteConstant A Y) Q n ↦
    Ext.mk₀CompMk₀ e.inv
      (x.mapExactFunctor (upperStar (ModuleCat.{u + 1} A) g)) a.hom
  let norm := fun z : ordinaryFiniteUnit A Y ⟶
      ((ordinaryFiniteSingleFunctor A Y).obj Q)⟦(n : ℤ)⟧ ↦
    ((ordinaryFiniteSinglePullbackIso A g).app _ ≪≫
        (ordinaryFiniteSingleFunctor A X).mapIso e).inv ≫
      (ordinaryFinitePullback A g).map z ≫
        (((ordinaryFinitePullback A g).commShiftIso (n : ℤ)).app
            ((ordinaryFiniteSingleFunctor A Y).obj Q) ≪≫
          (shiftFunctor (DerivedCategoryModule A X) (n : ℤ)).mapIso
            ((ordinaryFiniteSinglePullbackIso A g).app Q ≪≫
              (ordinaryFiniteSingleFunctor A X).mapIso a)).hom
  exact class_pullback_of_equiv E E' p norm
    (ordinaryFiniteClass A Y Q n) (ordinaryFiniteClass A X Q' n)
    (ordinaryFiniteExtClassCore (moduleAbelianForget A Y)
      (ordinaryFiniteIntegralGenerator A Y) Q n)
    (ordinaryFiniteExtClassCore (moduleAbelianForget A X)
      (ordinaryFiniteIntegralGenerator A X) Q' n)
    (fun z ↦ Sheaf.H.map ((moduleAbelianUpperStarComparison A g).app Q ≫
      (moduleAbelianForget A X).map a.hom) n (cohomologyMap g _ n z))
    (cached_ext_pullback_conj A g (ordinaryFiniteConstant A Y) Q e a n)
    (ordinaryFiniteClass_extHomEquiv A Y Q n)
    (ordinaryFiniteClass_extHomEquiv A X Q' n)
    (class_ext_pullback A g Q Q' a.hom n) c

private theorem class_chern_pullback
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (c : ordinaryFiniteUnit A Y ⟶ (ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧) :
    ordinaryFiniteClass A X (Scheme.finiteEtaleTateLine X N A hA) 2
        ((ordinaryFiniteUnitPullback A g).inv ≫ (ordinaryFinitePullback A g).map c ≫
          (ordinaryFiniteShiftedLinePullback A N hA t g hY).hom) =
      Sheaf.H.map ((moduleAbelianUpperStarComparison A g).app _ ≫
        (moduleAbelianForget A X).map (t.line g hY).hom) 2
        (cohomologyMap g _ 2
          (ordinaryFiniteClass A Y (Scheme.finiteEtaleTateLine Y N A hA) 2 c)) := by
  rw [ordinaryFiniteShiftedLinePullback_eq]
  exact class_pullback A g _ _ (t.line g hY) 2 c

private theorem chern_square_of_class
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤)))
    (c : ordinaryFiniteUnit A Y ⟶ (ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)
    (d : ordinaryFiniteUnit A X ⟶ (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    (hc : Sheaf.H.map ((moduleAbelianUpperStarComparison A g).app _ ≫
        (moduleAbelianForget A X).map (t.line g hY).hom) 2
      (cohomologyMap g _ 2
        (ordinaryFiniteClass A Y (Scheme.finiteEtaleTateLine Y N A hA) 2 c)) =
      ordinaryFiniteClass A X (Scheme.finiteEtaleTateLine X N A hA) 2 d) :
    (ordinaryFinitePullback A g).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t g hY).hom =
      (ordinaryFiniteUnitPullback A g).hom ≫ d := by
  have hn : (ordinaryFiniteUnitPullback A g).inv ≫
      (ordinaryFinitePullback A g).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t g hY).hom = d :=
    (ordinaryFiniteClass_bijective_arbitraryBase A X
      (Scheme.finiteEtaleTateLine X N A hA) 2).1
      ((class_chern_pullback A N hA t g hY c).trans hc)
  calc
    _ = (ordinaryFiniteUnitPullback A g).hom ≫
        ((ordinaryFiniteUnitPullback A g).inv ≫ (ordinaryFinitePullback A g).map c ≫
          (ordinaryFiniteShiftedLinePullback A N hA t g hY).hom) := by
      simp only [Iso.hom_inv_id_assoc]
    _ = _ := congrArg (fun z ↦ (ordinaryFiniteUnitPullback A g).hom ≫ z) hn

private theorem chern_square_of_kummer
    (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA) {X Y : Scheme.{u}}
    (g : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (hX : IsUnit (N : Γ(X, ⊤)))
    (L : Y.Pic) (L' : X.Pic) (hL : Scheme.Pic.map g L = L')
    (c : ordinaryFiniteUnit A Y ⟶ (ordinaryFiniteLine A N hA Y)⟦(2 : ℤ)⟧)
    (d : ordinaryFiniteUnit A X ⟶ (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteClass A Y (Scheme.finiteEtaleTateLine Y N A hA) 2 c =
      ordinaryFiniteKummerClass A N hA Y hY L)
    (hd : ordinaryFiniteClass A X (Scheme.finiteEtaleTateLine X N A hA) 2 d =
      ordinaryFiniteKummerClass A N hA X hX L') :
    (ordinaryFinitePullback A g).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t g hY).hom =
      (ordinaryFiniteUnitPullback A g).hom ≫ d := by
  apply chern_square_of_class A N hA t g hY c d
  calc
    _ = Sheaf.H.map ((moduleAbelianUpperStarComparison A g).app _ ≫
        (moduleAbelianForget A X).map (t.line g hY).hom) 2
        (cohomologyMap g _ 2 (ordinaryFiniteKummerClass A N hA Y hY L)) :=
      congrArg (fun z ↦ Sheaf.H.map
        ((moduleAbelianUpperStarComparison A g).app _ ≫
          (moduleAbelianForget A X).map (t.line g hY).hom) 2
          (cohomologyMap g _ 2 z)) hc
    _ = _ := kummer_class_pullback A N hA t g hY hX L L' hL
    _ = _ := hd.symm

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace

-- The original interface retains hN; this naturality proof works without positivity.
set_option linter.unusedVariables false in
/-- The normalized projective-line Chern maps satisfy the inverse-image square.
Source: the base-change step in blueprint `lemma-cohomology-projective-line-trace`, the
arbitrary-scheme Kummer and Picard pullback identities, and the pullback isomorphism for O(1).
(auxiliary; not a blueprint node)

The normalized roots comparison is the canonical one, since its composite with the
kernel inclusion is specified. The coefficient-line normalization at 1 makes the roots
map commute with pullback and forgetting scalars. The integral generator and exact-functor
Ext comparison identify the class of a pulled-back derived arrow with the pullback of its
cohomology class. Naturality of the Kummer boundary and Picard cohomology, together with
pullback of O(1), identify that class with the specified class over the new base.
Arbitrary-base injectivity of `ordinaryFiniteClass` then identifies the arrows. -/
theorem ordinaryFiniteP1_chern_map_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {S' S : Scheme.{u}} (f : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) c)
    (hc' : ordinaryFiniteP1ChernSpec A N hA S'
      ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
        hS'.map (ProjectiveLine S' ↘ S').appTop.hom) c') :
    (ordinaryFinitePullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)
          ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
            hS.map (ProjectiveLine S ↘ S).appTop.hom)).hom =
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) f)).hom ≫ c' := by
  let P := ProjectiveLine S
  let P' := ProjectiveLine S'
  let g := ProjectiveSpace.map (ULift.{u} (Fin 2)) f
  let hP : IsUnit (N : Γ(P, ⊤)) :=
    (map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
      hS.map (ProjectiveLine S ↘ S).appTop.hom
  let hP' : IsUnit (N : Γ(P', ⊤)) :=
    (map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
      hS'.map (ProjectiveLine S' ↘ S').appTop.hom
  exact chern_square_of_kummer A N hA t g hP hP' _ _ (p1_pic_pullback f) c c'
    ((ordinaryFiniteP1ChernSpec_iff A N hA S hP c).1 hc)
    ((ordinaryFiniteP1ChernSpec_iff A N hA S' hP' c').1 hc')

end AlgebraicGeometry.Etale

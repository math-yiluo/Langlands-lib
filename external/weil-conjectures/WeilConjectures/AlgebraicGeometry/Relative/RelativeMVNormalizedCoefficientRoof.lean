/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainData
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVDirectImageSquareLocalization

/-! # Localization of a roof of normalized coefficient representatives

## References

* Stacks Project, Tags 08HY and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option cleanup.letToHave false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry

private lemma normalized_localization_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {I L E : C} {A B : D} (r : I ⟶ L) (e : L ≅ E) (p : I ⟶ E)
    (q : A ⟶ B) (ηI : A ⟶ F.obj I) (ηL : B ⟶ F.obj L)
    (hn : q ≫ ηL = ηI ≫ F.map r) (hr : r ≫ e.hom = p) :
    q ≫ ηL ≫ F.map e.hom = ηI ≫ F.map p := by
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, hr]

private lemma normalized_roof_square_transport
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : C ⥤ E) (H : E ⥤ D) (δ : F ⟶ G ⋙ H)
    {J K : C} {A B T P : D} {Y : E}
    (c : B ≅ A) (m : B ⟶ T) (d : T ⟶ F.obj K)
    (l : B ⟶ P) (p : P ⟶ F.obj J) (n : A ⟶ H.obj Y)
    (b : Y ⟶ G.obj J) (e : J ⟶ K)
    (hfs : m ≫ d = l ≫ p ≫ F.map e)
    (hunit : l ≫ p ≫ δ.app J = c.hom ≫ n ≫ H.map b) :
    (c.inv ≫ m) ≫ d ≫ δ.app K = n ≫ H.map (b ≫ G.map e) := by
  have hd := δ.naturality e
  dsimp only [Functor.comp_map] at hd
  calc
    (c.inv ≫ m) ≫ d ≫ δ.app K = c.inv ≫ (m ≫ d) ≫ δ.app K := by
      simp only [Category.assoc]
    _ = c.inv ≫ l ≫ p ≫ F.map e ≫ δ.app K := by
      rw [hfs]
      simp only [Category.assoc]
    _ = c.inv ≫ l ≫ p ≫ δ.app J ≫ H.map (G.map e) := by rw [hd]
    _ = c.inv ≫ (l ≫ p ≫ δ.app J) ≫ H.map (G.map e) := by
      simp only [Category.assoc]
    _ = n ≫ H.map (b ≫ G.map e) := by
      rw [hunit]
      simp only [Category.assoc, c.inv_hom_id_assoc, H.map_comp]

private lemma normalized_roof_of_comparison
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B T A' B' : D} {Y Y' : C}
    (u : A ⟶ B) (v : T ⟶ B) [IsIso v] (η : T ⟶ F.obj Y)
    (a : A ≅ A') (b : Y ≅ Y') (d : B ≅ B')
    (β : A' ⟶ B') (δ : B' ⟶ F.obj Y')
    (hu : u ≫ d.hom = a.hom ≫ β)
    (hv : v ≫ d.hom ≫ δ = η ≫ F.map b.hom) :
    u ≫ inv v ≫ η = a.hom ≫ β ≫ δ ≫ F.map b.inv := by
  have hvinv : inv v ≫ η = d.hom ≫ δ ≫ F.map b.inv := by
    apply (cancel_epi v).mp
    simp only [IsIso.hom_inv_id_assoc]
    have he := congrArg (fun t ↦ t ≫ F.map b.inv) hv
    simp only [Category.assoc, ← F.map_comp, b.hom_inv_id, F.map_id,
      Category.comp_id] at he
    exact he.symm
  rw [hvinv, ← Category.assoc, ← Category.assoc, hu]
  simp only [Category.assoc]

set_option linter.all false in
/-- A normalized coefficient roof localizes to the corresponding direct-image
square mate. -/
theorem relativeMV_normalized_coefficient_roof
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (h : g' ≫ f = f' ≫ g)
    (E : schemeDerivedCategory X) (E' : schemeDerivedCategory X')
    (I L : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (J : CochainComplex (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) ℤ)
    [I.IsKInjective] [J.IsKInjective] [L.IsKInjective]
    (eI : DerivedCategory.Q.obj I ≅ E) (eJ : DerivedCategory.Q.obj J ≅ E')
    (eL : DerivedCategory.Q.obj L ≅ (schemeDerivedDirectImage g').obj E')
    (β : E ⟶ (schemeDerivedDirectImage g').obj E')
    (r : I ⟶ L)
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj J ⟶ L)
    (hr : DerivedCategory.Q.map r = eI.hom ≫ β ≫ eL.inv)
    (hs : DerivedCategory.Q.map s = (schemeMVDirectImageLocalization g').app J ≫
      (schemeDerivedDirectImage g').map eJ.hom ≫ eL.inv) :
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let c := Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g h) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm
    let v := c.inv.app J ≫ Ff.map s
    ∀ hv : IsIso (DerivedCategory.Q.map v),
    letI := hv
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) h.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    let a := (RingedSpace.derivedModuleDirectImageKInjectiveIso
        f.toLRSHom.toShHom I).symm ≪≫ (schemeDerivedDirectImage f).mapIso eI
    let b := (RingedSpace.derivedModuleDirectImageKInjectiveIso
        f'.toLRSHom.toShHom J).symm ≪≫ (schemeDerivedDirectImage f').mapIso eJ
    DerivedCategory.Q.map (Ff.map r) ≫ inv (DerivedCategory.Q.map v) ≫
        (schemeMVDirectImageLocalization g).app (Ff'.obj J) =
      a.hom ≫ (schemeDerivedDirectImage f).map β ≫ δ.app E' ≫
        (schemeDerivedDirectImage g).map b.inv := by
  classical
  extract_lets (descend := false) Ff Ff' c v
  intro hv
  have := hv
  extract_lets (descend := false) κ δ a b
  let d := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f.toLRSHom.toShHom L).symm ≪≫ (schemeDerivedDirectImage f).mapIso eL
  have hnr : DerivedCategory.Q.map r ≫ eL.hom = eI.hom ≫ β := by
    rw [hr]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hns : DerivedCategory.Q.map s ≫ eL.hom =
      (schemeMVDirectImageLocalization g').app J ≫
        (schemeDerivedDirectImage g').map eJ.hom := by
    rw [hs]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := (schemeMVDirectImageLocalization f).naturality r
  dsimp only [Functor.comp_map] at hn
  have hu : DerivedCategory.Q.map (Ff.map r) ≫ d.hom =
      a.hom ≫ (schemeDerivedDirectImage f).map β := by
    dsimp only [d, a, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
    rw [← schemeMVDirectImageLocalization_app f L,
      ← schemeMVDirectImageLocalization_app f I]
    have ht := normalized_localization_naturality (schemeDerivedDirectImage f)
      (DerivedCategory.Q.map r) eL (eI.hom ≫ β) (DerivedCategory.Q.map (Ff.map r))
      ((schemeMVDirectImageLocalization f).app I)
      ((schemeMVDirectImageLocalization f).app L) hn hnr
    simpa only [Functor.map_comp, Category.assoc] using ht
  have hn := (schemeMVDirectImageLocalization f).naturality s
  dsimp only [Functor.comp_map] at hn
  have hfs : DerivedCategory.Q.map (Ff.map s) ≫
      (schemeMVDirectImageLocalization f).app L ≫
      (schemeDerivedDirectImage f).map eL.hom =
    (schemeMVDirectImageLocalization f).app
        (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj J) ≫
      (schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J) ≫
      (schemeDerivedDirectImage f).map ((schemeDerivedDirectImage g').map eJ.hom) := by
    have ht := normalized_localization_naturality (schemeDerivedDirectImage f)
      (DerivedCategory.Q.map s) eL _ (DerivedCategory.Q.map (Ff.map s))
      ((schemeMVDirectImageLocalization f).app _)
      ((schemeMVDirectImageLocalization f).app L) hn hns
    simpa only [Functor.map_comp] using ht
  have hunit := relativeMV_direct_image_square_localization f f' g g' h J
  have hvn : DerivedCategory.Q.map v ≫ d.hom ≫ δ.app E' =
      (schemeMVDirectImageLocalization g).app (Ff'.obj J) ≫
        (schemeDerivedDirectImage g).map b.hom := by
    have ht := normalized_roof_square_transport
      (schemeDerivedDirectImage g' ⋙ schemeDerivedDirectImage f)
      (schemeDerivedDirectImage f') (schemeDerivedDirectImage g) δ
      (DerivedCategory.Q.mapIso (c.app J)) (DerivedCategory.Q.map (Ff.map s))
      ((schemeMVDirectImageLocalization f).app L ≫ (schemeDerivedDirectImage f).map eL.hom)
      ((schemeMVDirectImageLocalization f).app
        (((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
          (.up ℤ)).obj J))
      ((schemeDerivedDirectImage f).map ((schemeMVDirectImageLocalization g').app J))
      ((schemeMVDirectImageLocalization g).app (Ff'.obj J))
      ((schemeMVDirectImageLocalization f').app J) eJ.hom hfs hunit
    simpa only [v, d, b, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      Functor.mapIso_inv, Iso.app_inv, Functor.map_comp,
      schemeMVDirectImageLocalization_app f L, schemeMVDirectImageLocalization_app f' J]
      using ht
  exact normalized_roof_of_comparison (schemeDerivedDirectImage g)
    (DerivedCategory.Q.map (Ff.map r)) (DerivedCategory.Q.map v)
    ((schemeMVDirectImageLocalization g).app (Ff'.obj J)) a b d
    ((schemeDerivedDirectImage f).map β) (δ.app E') hu hvn

end AlgebraicGeometry

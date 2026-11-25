/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.RelativeMVMaps
public import WeilConjectures.AlgebraicGeometry.MayerVietorisImageChainMap
public import WeilConjectures.AlgebraicGeometry.DirectImageSquareUnitTransport
import WeilConjectures.AlgebraicGeometry.Relative.RelativeMVNormalizedCoefficientRoof
import WeilConjectures.AlgebraicGeometry.DerivedMayerVietorisImageResolutionComparisonIntersection
import WeilConjectures.AlgebraicGeometry.DerivedBaseChangeOpenTranspose
import WeilConjectures.AlgebraicGeometry.RelativeMVInverseOpenMate
/-! # Comparison of a normalized roof for one open

## References

* Stacks Project, Tags 08BV, 08FE, 08HY and 0D5T
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits CochainComplex
namespace AlgebraicGeometry
private lemma mate_transpose_to
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (α : L₂ ⟶ L₁)
    {M : C} {K : D} (β : M ⟶ R₁.obj K) (δ : L₂.obj M ⟶ K)
    (h : α.app M ≫ L₁.map β ≫ a₁.counit.app K = δ) :
    β ≫ (conjugateEquiv a₁ a₂ α).app K = a₂.homEquiv M K δ := by
  apply (a₂.homEquiv M K).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  rw [conjugateEquiv_counit, ← Category.assoc, α.naturality, Category.assoc]
  have hδ : L₂.map ((a₂.homEquiv M K) δ) ≫ a₂.counit.app K = δ := by
    simpa only [Adjunction.homEquiv_symm_apply] using
      (a₂.homEquiv M K).symm_apply_apply δ
  exact h.trans hδ.symm

private lemma square_conjugate_transpose
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {R : C₁ ⥤ C₀} {G : C₀ ⥤ C₂} {T : C₂ ⥤ C₀}
    {F' : C₂ ⥤ C₃} {R' : C₃ ⥤ C₂} {G' : C₁ ⥤ C₃} {T' : C₃ ⥤ C₁}
    (af : F ⊣ R) (ag : G ⊣ T) (af' : F' ⊣ R') (ag' : G' ⊣ T')
    (α : G ⋙ F' ≅ F ⋙ G') {K : C₁} {K' : C₃} (φ : G'.obj K ⟶ K') :
    ag.homEquiv _ _ (af'.homEquiv _ _
        (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ)) =
      R.map (ag'.homEquiv _ _ φ) ≫
        (conjugateEquiv (af.comp ag') (ag.comp af') α.hom).app K' := by
  have h := mate_transpose_to (af.comp ag') (ag.comp af') α.hom
    (R.map (ag'.homEquiv _ _ φ))
    (α.hom.app (R.obj K) ≫ G'.map (af.counit.app K) ≫ φ) ?_
  · rw [Adjunction.comp_homEquiv] at h
    exact h.symm
  · simp only [Functor.comp_map, Adjunction.comp_counit_app]
    have hn := af.counit.naturality (ag'.homEquiv _ _ φ)
    dsimp only [Functor.comp_map, Functor.id_map] at hn
    rw [← G'.map_comp_assoc, hn]
    simp only [G'.map_comp, Category.assoc]
    have he : G'.map (ag'.homEquiv _ _ φ) ≫ ag'.counit.app K' = φ := by
      simpa only [Adjunction.homEquiv_symm_apply] using
        (ag'.homEquiv _ _).symm_apply_apply φ
    rw [he]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.isDefEq.lazyProjDelta false
set_option backward.isDefEq.lazyWhnfCore false
set_option cleanup.letToHave false
attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorUnit DerivedCategory.Qh
set_option linter.all false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem global_arrow_transpose
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : CategoryTheory.IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') :
    let κ := relativeMVComp f' g ≪≫
      eqToIso (congrArg (fun t ↦ derivedPullback.{u, w} t) hpull.w.symm) ≪≫
      (relativeMVComp g' f).symm
    let δ := conjugateEquiv ((relativeMVAdj f).comp (relativeMVAdj g'))
      ((relativeMVAdj g).comp (relativeMVAdj f')) κ.hom
    (relativeMVAdj g).homEquiv _ _
        (relativeMVGlobalArrow f f' g g' hpull K K' φ).hom =
      (schemeDerivedDirectImage f).map ((relativeMVAdj g').homEquiv _ _ φ) ≫
        δ.app K' := by
  intro κ δ
  have he : schemeDerivedBaseChangeMap f f' g g' hpull.w K =
      (relativeMVAdj f').homEquiv _ _
        (κ.hom.app ((schemeDerivedDirectImage f).obj K) ≫
          (derivedPullback g').map ((relativeMVAdj f).counit.app K)) := by
    simp +instances only [schemeDerivedBaseChangeMap, relativeMVAdj, relativeMVComp, κ,
      Iso.trans_hom, Iso.symm_hom, Iso.app_hom, NatTrans.comp_app,
      eqToIso.hom, eqToHom_app, Category.assoc]
    rfl
  dsimp only [relativeMVGlobalArrow, Arrow.mk, Arrow.hom]
  rw [he]
  rw [← (relativeMVAdj f').homEquiv_naturality_right]
  simpa +instances only [Category.assoc, δ, Arrow.right] using
    square_conjugate_transpose (relativeMVAdj f) (relativeMVAdj g)
      (relativeMVAdj f') (relativeMVAdj g') κ φ

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
private lemma openImage_isKInjective (X : Scheme.{u}) (W : X.Opens)
    (I : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    [I.IsKInjective] : (schemeOpenModuleImageComplex X W I).IsKInjective := by
  have : (Scheme.Modules.pushforward W.ι).Additive :=
    Functor.additive_of_preserves_binary_products _
  have := isKInjective_schemeOpenRestriction X W I
  have := (schemeOpenModuleAdjunction X W).preservesKInjectiveComplexes
  change CochainComplex.IsKInjective
    (((Scheme.Modules.pushforward W.ι).mapHomologicalComplex (.up ℤ)).obj
      (((schemeOpenRestriction X W).mapHomologicalComplex (.up ℤ)).obj I))
  infer_instance

attribute [local instance] openImage_isKInjective
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem open_resolution_numerator
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (β : K ⟶ (schemeDerivedDirectImage g').obj K')
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫ β ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (W : X.Opens) :
    let I := schemeMVResolution X K
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let H := schemeMVDerivedRestriction X W ⋙ schemeDerivedDirectImage W.ι
    let a := schemeOpenModuleImageComplexComparison X W I (schemeMVAdjunction X W) ≪≫
      H.mapIso (schemeMVResolutionIso X K)
    let b := schemeOpenModuleImageComplexComparison X W L (schemeMVAdjunction X W) ≪≫
      H.mapIso (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))
    DerivedCategory.Q.map (((schemeOpenModuleImage X W).mapHomologicalComplex (.up ℤ)).map r)
      = a.hom ≫ H.map β ≫ b.inv := by
  extract_lets (descend := false) I L H a b
  have hn := schemeMVOpenImageLocalization_naturality X W r
  rw [schemeMVOpenImageLocalization_eq X W I,
    schemeMVOpenImageLocalization_eq X W L, hr] at hn
  have hh := congrArg (fun t ↦ t ≫
    (schemeOpenModuleImageComplexComparison X W L (schemeMVAdjunction X W)).inv) hn
  simpa only [a, b, Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, H, Functor.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    using hh

private lemma map_iso_cancel_left
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B : C} {T U : D} (a : A ≅ B) (e : F.obj A ≅ T)
    (r : T ⟶ U) (t : F.obj B ⟶ U)
    (h : F.map a.inv ≫ e.hom ≫ r = t) :
    r = e.inv ≫ F.map a.hom ≫ t := by
  rw [← h, ← F.map_comp_assoc, a.hom_inv_id, F.map_id, Category.id_comp,
    e.inv_hom_id_assoc]

private theorem open_resolution_denominator_intersection
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K' : schemeDerivedCategory X')
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (U V : X.Opens) :
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let W := U ⊓ V
    let W' := (g' ⁻¹ᵁ U) ⊓ (g' ⁻¹ᵁ V)
    let H := schemeMVDerivedRestriction X W ⋙ schemeDerivedDirectImage W.ι
    let H' := schemeMVDerivedRestriction X' W' ⋙ schemeDerivedDirectImage W'.ι
    let a := schemeOpenModuleImageComplexComparison X' W' J
      (schemeMVAdjunction X' W') ≪≫ H'.mapIso (schemeMVResolutionIso X' K')
    let b := schemeOpenModuleImageComplexComparison X W L (schemeMVAdjunction X W) ≪≫
      H.mapIso (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))
    DerivedCategory.Q.map (schemeMVImageComponent g' W J L s) =
      (schemeMVDirectImageLocalization g').app (schemeOpenModuleImageComplex X' W' J) ≫
      (schemeDerivedDirectImage g').map a.hom ≫ (schemeMVOpenComparison g' W K').hom ≫
      b.inv := by
  extract_lets (descend := false) J L W W' H H' a b
  have hf : (RingedSpace.derivedModuleDirectImageKInjectiveIso
      g'.toLRSHom.toShHom J).hom ≫ DerivedCategory.Q.map s ≫
        (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).hom =
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom := by
    rw [hs, schemeMVDirectImageLocalization_app g' J]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.hom_inv_id_assoc]
  have hn : (schemeDerivedDirectImage g').map a.inv ≫
      (RingedSpace.derivedModuleDirectImageKInjectiveIso
        g'.toLRSHom.toShHom (schemeOpenModuleImageComplex X' W' J)).hom ≫
      DerivedCategory.Q.map (schemeMVImageComponent g' W J L s) =
      (schemeMVOpenComparison g' W K').hom ≫ b.inv := by
    have hcomp := schemeMV_image_resolution_comparison_intersection X' X g' U V K' s hf
    -- Normalize the comparisons and third chain-map component before matching the theorem.
    simpa only [a, b, H, H', J, L, W, W', Iso.trans_inv, Functor.mapIso_inv,
      schemeMVImageChainMap, ShortComplex.homMk] using hcomp
  rw [schemeMVDirectImageLocalization_app g'
    (schemeOpenModuleImageComplex X' W' J)]
  exact map_iso_cancel_left (schemeDerivedDirectImage g') a
    (RingedSpace.derivedModuleDirectImageKInjectiveIso
      g'.toLRSHom.toShHom (schemeOpenModuleImageComplex X' W' J))
    (DerivedCategory.Q.map (schemeMVImageComponent g' W J L s))
    ((schemeMVOpenComparison g' W K').hom ≫ b.inv) hn

private theorem open_resolution_denominator
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X X' : Scheme.{u}} (g' : X' ⟶ X)
    (K' : schemeDerivedCategory X')
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (W : X.Opens) :
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let W' := g' ⁻¹ᵁ W
    let H := schemeMVDerivedRestriction X W ⋙ schemeDerivedDirectImage W.ι
    let H' := schemeMVDerivedRestriction X' W' ⋙ schemeDerivedDirectImage W'.ι
    let a := schemeOpenModuleImageComplexComparison X' W' J
      (schemeMVAdjunction X' W') ≪≫ H'.mapIso (schemeMVResolutionIso X' K')
    let b := schemeOpenModuleImageComplexComparison X W L (schemeMVAdjunction X W) ≪≫
      H.mapIso (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))
    DerivedCategory.Q.map (schemeMVImageComponent g' W J L s) =
      (schemeMVDirectImageLocalization g').app (schemeOpenModuleImageComplex X' W' J) ≫
      (schemeDerivedDirectImage g').map a.hom ≫ (schemeMVOpenComparison g' W K').hom ≫
      b.inv := by
  let P : X.Opens → Prop := fun T =>
    let J := schemeMVResolution X' K'
    let L := schemeMVResolution X ((schemeDerivedDirectImage g').obj K')
    let T' := g' ⁻¹ᵁ T
    let H := schemeMVDerivedRestriction X T ⋙ schemeDerivedDirectImage T.ι
    let H' := schemeMVDerivedRestriction X' T' ⋙ schemeDerivedDirectImage T'.ι
    let a := schemeOpenModuleImageComplexComparison X' T' J
      (schemeMVAdjunction X' T') ≪≫ H'.mapIso (schemeMVResolutionIso X' K')
    let b := schemeOpenModuleImageComplexComparison X T L (schemeMVAdjunction X T) ≪≫
      H.mapIso (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))
    DerivedCategory.Q.map (schemeMVImageComponent g' T J L s) =
      (schemeMVDirectImageLocalization g').app (schemeOpenModuleImageComplex X' T' J) ≫
      (schemeDerivedDirectImage g').map a.hom ≫ (schemeMVOpenComparison g' T K').hom ≫ b.inv
  exact Eq.mp (congrArg P (inf_idem W))
    (open_resolution_denominator_intersection g' K' s hs W W)

/-- A normalized direct-image roof on one open realizes the prescribed local
base-change arrow. -/
theorem relativeMV_resolved_open_roof_comparison
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (hpull : IsPullback g' f' f g)
    (K : schemeDerivedCategory X) (K' : schemeDerivedCategory X')
    (φ : (derivedPullback g').obj K ⟶ K') (W : X.Opens)
    (r : schemeMVResolution X K ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (s : ((RingedSpace.moduleDirectImage g'.toLRSHom.toShHom).mapHomologicalComplex
        (.up ℤ)).obj (schemeMVResolution X' K') ⟶
      schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    (hr : DerivedCategory.Q.map r = (schemeMVResolutionIso X K).hom ≫
      (relativeMVAdj g').homEquiv _ _ φ ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv)
    (hs : DerivedCategory.Q.map s =
      (schemeMVDirectImageLocalization g').app (schemeMVResolution X' K') ≫
      (schemeDerivedDirectImage g').map (schemeMVResolutionIso X' K').hom ≫
      (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K')).inv) :
    let I := schemeOpenModuleImageComplex X W (schemeMVResolution X K)
    let J := schemeOpenModuleImageComplex X' (g' ⁻¹ᵁ W) (schemeMVResolution X' K')
    let _L := schemeOpenModuleImageComplex X W
      (schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
    let Ff := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let Ff' := (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom).mapHomologicalComplex (.up ℤ)
    let c := Functor.mapHomologicalComplexCompIso
        (directImageSquareIso g' f f' g hpull.w) (.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (RingedSpace.moduleDirectImage f'.toLRSHom.toShHom ⋙
          RingedSpace.moduleDirectImage g.toLRSHom.toShHom)) (.up ℤ)).symm
    let rW := ((schemeOpenModuleImage X W).mapHomologicalComplex (.up ℤ)).map r
    let sW := schemeMVImageComponent g' W (schemeMVResolution X' K')
      (schemeMVResolution X ((schemeDerivedDirectImage g').obj K')) s
    let v := c.inv.app J ≫ Ff.map sW
    ∀ hv : IsIso (DerivedCategory.Q.map v), letI := hv
    ∃ (e : (derivedPullback g).obj (DerivedCategory.Q.obj (Ff.obj I)) ≅
        (relativeMVLocalArrow f f' g g' hpull K K' φ W).left)
      (e' : DerivedCategory.Q.obj (Ff'.obj J) ≅
        (relativeMVLocalArrow f f' g g' hpull K K' φ W).right),
      DerivedCategory.Q.map (Ff.map rW) ≫ inv (DerivedCategory.Q.map v) ≫
        (schemeMVDirectImageLocalization g).app (Ff'.obj J) =
      (relativeMVAdj g).homEquiv _ _
        (e.hom ≫ (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom ≫ e'.inv) := by
  classical
  extract_lets (descend := false) I J L Ff Ff' c rW sW v
  intro hv
  have := hv
  let H := schemeMVDerivedRestriction X W ⋙ schemeDerivedDirectImage W.ι
  let H' := schemeMVDerivedRestriction X' (g' ⁻¹ᵁ W) ⋙
    schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι
  let cmp := schemeMVOpenComparison g' W K'
  let β := (relativeMVAdj g').homEquiv _ _ φ
  let βW := H.map β ≫ cmp.inv
  let eI := schemeOpenModuleImageComplexComparison X W (schemeMVResolution X K)
    (schemeMVAdjunction X W) ≪≫ H.mapIso (schemeMVResolutionIso X K)
  let eJ := schemeOpenModuleImageComplexComparison X' (g' ⁻¹ᵁ W)
    (schemeMVResolution X' K') (schemeMVAdjunction X' (g' ⁻¹ᵁ W)) ≪≫
    H'.mapIso (schemeMVResolutionIso X' K')
  let eL := (schemeOpenModuleImageComplexComparison X W
      (schemeMVResolution X ((schemeDerivedDirectImage g').obj K'))
      (schemeMVAdjunction X W) ≪≫
    H.mapIso (schemeMVResolutionIso X ((schemeDerivedDirectImage g').obj K'))) ≪≫ cmp.symm
  have hrW : DerivedCategory.Q.map rW = eI.hom ≫ βW ≫ eL.inv := by
    have hh := open_resolution_numerator g' K K' β r hr W
    simpa only [eI, eL, βW, Iso.trans_inv, Iso.symm_inv, Category.assoc,
      Iso.inv_hom_id_assoc] using hh
  have hsW : DerivedCategory.Q.map sW = (schemeMVDirectImageLocalization g').app J ≫
      (schemeDerivedDirectImage g').map eJ.hom ≫ eL.inv := by
    have hh := open_resolution_denominator g' K' s hs W
    simpa only [eL, Iso.trans_inv, Iso.symm_inv, Category.assoc] using hh
  let t := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f.toLRSHom.toShHom I).symm ≪≫ (schemeDerivedDirectImage f).mapIso eI
  let t' := (RingedSpace.derivedModuleDirectImageKInjectiveIso
    f'.toLRSHom.toShHom J).symm ≪≫ (schemeDerivedDirectImage f').mapIso eJ
  let e := (derivedPullback g).mapIso t ≪≫
    (derivedPullback g).mapIso (relativeMVExactOpenIso f W K)
  let e' := t' ≪≫ relativeMVInverseOpenIso g' f' W K'
  refine ⟨e, e', ?_⟩
  let φW := schemeDerivedBaseChangeMap W.ι (g' ⁻¹ᵁ W).ι g'
      (g'.resLE W (g' ⁻¹ᵁ W) le_rfl) (Scheme.Hom.resLE_comp_ι g' le_rfl)
      ((schemeOpenRestriction X W).mapDerivedCategory.obj K) ≫
    (schemeDerivedDirectImage (g' ⁻¹ᵁ W).ι).map
      ((mvPullbackOpenRestrictionIso g' W).inv.app K ≫
        (schemeOpenRestriction X' (g' ⁻¹ᵁ W)).mapDerivedCategory.map φ)
  have hβ : (relativeMVAdj g').homEquiv _ _ φW = βW :=
    derivedBaseChange_open_transpose g' W K K' φ
  have hglobal := global_arrow_transpose f f' g g' hpull (H.obj K) (H'.obj K') φW
  dsimp only at hglobal
  change (relativeMVAdj g').homEquiv (H.obj K) (H'.obj K') φW = βW at hβ
  simp only [hβ] at hglobal
  have hcoeff := relativeMV_normalized_coefficient_roof f f' g g' hpull.w
    (H.obj K) (H'.obj K') I L J eI eJ eL βW rW sW hrW hsW hv
  have htransport : e.hom ≫ (relativeMVLocalArrow f f' g g' hpull K K' φ W).hom ≫
      e'.inv = (derivedPullback g).map t.hom ≫
        mvBaseChangeOpenMap f f' g g' hpull.w K K' φ W ≫ t'.inv := by
    simp only [e, e', Iso.trans_hom, Iso.trans_inv, Functor.mapIso_hom, Category.assoc]
    have hh := relativeMVInverseOpenIso_mate f f' g g' hpull K K' φ W
    have hh' := congrArg (fun q ↦ (derivedPullback g).map t.hom ≫ q ≫
      (relativeMVInverseOpenIso g' f' W K').inv ≫ t'.inv) hh
    simpa only [Category.assoc, Functor.mapIso_hom, Iso.hom_inv_id_assoc] using hh'.symm
  rw [htransport, (relativeMVAdj g).homEquiv_naturality_left,
    (relativeMVAdj g).homEquiv_naturality_right]
  change _ = t.hom ≫ (relativeMVAdj g).homEquiv _ _
    (relativeMVGlobalArrow f f' g g' hpull (H.obj K) (H'.obj K') φW).hom ≫
      (schemeDerivedDirectImage g).map t'.inv
  rw [hglobal]
  simpa only [t, t', Category.assoc] using hcoeff

end AlgebraicGeometry

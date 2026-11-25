/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ResolutionOpenComparisonMap
import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage

/-! # Restriction naturality of raw section cohomology

Source: Stacks Project, Tags 01E1, 01E2 and 01E4.
(blueprint: lem-pc-resolution-open-restriction-natural). -/

@[expose] public section
universe u
set_option autoImplicit false
open CategoryTheory Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] enoughInjectives

private theorem homology_restriction_transport
    {C : Type*} [Category C] [Abelian C]
    (A A' : ShortComplex AddCommGrpCat.{u}) (B : ShortComplex C)
    (E E' : C ⥤ AddCommGrpCat.{u})
    [E.PreservesZeroMorphisms] [E.PreservesHomology]
    [E'.PreservesZeroMorphisms] [E'.PreservesHomology]
    (φ : A ⟶ A') (e : A ⟶ B.map E) (e' : A' ⟶ B.map E') (τ : E ⟶ E')
    (h : φ ≫ e' = e ≫ B.mapNatTrans τ) :
    ShortComplex.homologyMap φ ≫ ShortComplex.homologyMap e' ≫
        (B.mapHomologyIso E').hom =
      ShortComplex.homologyMap e ≫ (B.mapHomologyIso E).hom ≫ τ.app B.homology := by
  have hm := congrArg (fun g ↦ ShortComplex.homologyMap g) h
  rw [ShortComplex.homologyMap_comp, ShortComplex.homologyMap_comp,
    ShortComplex.homologyMap_mapNatTrans] at hm
  have hm' := congrArg (fun g ↦ g ≫ (B.mapHomologyIso E').hom) hm
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hm'


/-- The fixed comparison is natural for inverse images of smaller base opens.
Source: Stacks Project, Tags 01E1, 01E2 (Equation 20.7.1.1) and 01E4.
(blueprint: lem-pc-resolution-open-restriction-natural).

Proof: Compute both top-open and U-open cohomology using the given injective
resolution R.resolution on Y. Map R.comparison through U-open sections, then
identify sections by restrictAppIso and hU. Applying homology and the exact
evaluation comparison gives an isomorphism from U-open cohomology to P(V);
its inverse defines d. For the top-open isomorphism use R.sections, so its
inverse is precisely resolutionOpenComparison. Naturality of R.comparison
with respect to top-to-U restriction, together with R.components, makes the
section-complex square commute degreewise. Apply homology to this square and
use InjectiveResolution.rightDerived_app_eq for the section restriction
natural transformation. Naturality of mapHomologyIso identifies the lower
map with P's restriction. Cancel both comparison inverses to obtain the
claimed equation. No further restriction of injectives is needed, since
openModuleCohomology is already the derived functor of U-open sections on Y.
The calculation follows rawOpenIso_restriction in SectionCohomologyUntwistedComparisons,
with R.components in place of its specially constructed resolution.
Empty V or U, V=W, and degree zero use the same functors and cancellation;
there are no scalar, affineness, compactness or quasi-coherence assumptions. -/
theorem resolution_open_restriction_natural {X T : Scheme.{u}}
    (f : X ⟶ T) (F : X.Modules) (I : InjectiveResolution F) (q : ℕ)
    (W : T.Opens) (R : RestrictedResolutionSections I (f ⁻¹ᵁ W))
    (V : T.Opens) (hVW : V ≤ W) (U : (f ⁻¹ᵁ W).toScheme.Opens)
    (hU : (f ⁻¹ᵁ W).ι ''ᵁ U = f ⁻¹ᵁ V) :
    let K := ((pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
    let P := sectionCohomologyPresheaf K q
    let Y := (f ⁻¹ᵁ W).toScheme
    let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
    let c := resolutionOpenComparison f F I q W R
    ∃ d : P.obj (op V) ≃+
      (RingedSpace.openModuleCohomology Y.toRingedSpace q U).obj G,
      ∀ x : P.obj (op W),
        (RingedSpace.openModuleCohomologyRestriction Y.toRingedSpace q
          (homOfLE (le_top : U ≤ ⊤))).app G (c x) =
            d ((P.map (homOfLE hVW).op).hom x) := by
  dsimp only
  let Y := (f ⁻¹ᵁ W).toScheme
  let G := (restrictFunctor (f ⁻¹ᵁ W).ι).obj F
  let J := R.resolution
  let ST := RingedSpace.openModuleSections Y.toRingedSpace ⊤
  let SU := RingedSpace.openModuleSections Y.toRingedSpace U
  let : ST.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace ⊤
  let : SU.Additive := RingedSpace.openModuleSections_additive Y.toRingedSpace U
  let RF := restrictFunctor (f ⁻¹ᵁ W).ι
  let : RF.Additive := ⟨by intros; rfl⟩
  let A := ((SheafOfModules.forget T.ringCatSheaf).mapHomologicalComplex (.up ℕ)).obj
    (((pushforward f).mapHomologicalComplex (.up ℕ)).obj I.cocomplex)
  let ET := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op W)
  let EU := PresheafOfModules.toPresheaf T.ringCatSheaf.obj ⋙
    (CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).obj (op V)
  let : (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V)).Additive :=
    RingedSpace.openModuleSections_additive X.toRingedSpace (f ⁻¹ᵁ V)
  let eSU : RF ⋙ SU ≅ RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ V) :=
    NatIso.ofComponents (fun M ↦ restrictAppIso (f ⁻¹ᵁ W).ι M U ≪≫
      M.presheaf.mapIso (eqToIso hU.symm).op) (by
        intro M N g
        dsimp
        simp only [Category.assoc]
        rw [← Category.assoc]
        have hg : Hom.app (RF.map g) U ≫ (restrictAppIso (f ⁻¹ᵁ W).ι N U).hom =
            (restrictAppIso (f ⁻¹ᵁ W).ι M U).hom ≫ Hom.app g ((f ⁻¹ᵁ W).ι ''ᵁ U) := by
          ext z
          rfl
        erw [hg]
        rw [Category.assoc]
        congr 1
        exact (g.mapPresheaf.naturality _).symm)
  let eCT : (ST.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (ET.mapHomologicalComplex (.up ℕ)).obj A := R.sections
  let eCU : (SU.mapHomologicalComplex (.up ℕ)).obj J.cocomplex ≅
      (EU.mapHomologicalComplex (.up ℕ)).obj A :=
    (SU.mapHomologicalComplex (.up ℕ)).mapIso R.comparison ≪≫
      (NatIso.mapHomologicalComplex eSU (.up ℕ)).app I.cocomplex
  let α : ST ⟶ SU :=
    Functor.whiskerLeft (SheafOfModules.forget Y.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf Y.ringCatSheaf.obj)
      ((CategoryTheory.evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).map
        (homOfLE (le_top : U ≤ ⊤)).op)
  let τ : ET ⟶ EU := Functor.whiskerLeft
    (PresheafOfModules.toPresheaf T.ringCatSheaf.obj)
    ((CategoryTheory.evaluation T.Opensᵒᵖ AddCommGrpCat.{u}).map (homOfLE hVW).op)
  let φ := (NatTrans.mapHomologicalComplex α (.up ℕ)).app J.cocomplex
  have hc : φ ≫ eCU.hom = eCT.hom ≫
      (NatTrans.mapHomologicalComplex τ (.up ℕ)).app A := by
    apply HomologicalComplex.hom_ext
    intro n
    dsimp [φ, eCU, eCT, eSU]
    rw [R.components]
    ext x
    have hg := ConcreteCategory.congr_hom
      ((R.comparison.hom.f n).mapPresheaf.naturality
        (homOfLE (le_top : U ≤ ⊤)).op) x
    change Hom.app (R.comparison.hom.f n) U
      ((J.cocomplex.X n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x) =
      (((restrictFunctor (f ⁻¹ᵁ W).ι).obj (I.cocomplex.X n)).presheaf.map
        (homOfLE (le_top : U ≤ ⊤)).op) (Hom.app (R.comparison.hom.f n) ⊤ x) at hg
    change (I.cocomplex.X n).presheaf.map (eqToHom hU.symm).op
      ((restrictAppIso (f ⁻¹ᵁ W).ι (I.cocomplex.X n) U).hom
        (Hom.app (R.comparison.hom.f n) U
          ((J.cocomplex.X n).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op x))) =
      (I.cocomplex.X n).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map (homOfLE hVW)).op
        ((I.cocomplex.X n).presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top.symm).op
          ((restrictAppIso (f ⁻¹ᵁ W).ι (I.cocomplex.X n) ⊤).hom
            (Hom.app (R.comparison.hom.f n) ⊤ x)))
    rw [hg]
    change (I.cocomplex.X n).presheaf.map (eqToHom hU.symm).op
      ((I.cocomplex.X n).presheaf.map
        (homOfLE (Scheme.Hom.image_mono (f ⁻¹ᵁ W).ι (le_top : U ≤ ⊤))).op
          (Hom.app (R.comparison.hom.f n) ⊤ x)) =
      (I.cocomplex.X n).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map (homOfLE hVW)).op
        ((I.cocomplex.X n).presheaf.map (eqToHom (f ⁻¹ᵁ W).ι_image_top.symm).op
          (Hom.app (R.comparison.hom.f n) ⊤ x))
    simp only [← Functor.map_comp_apply, ← op_comp]
    congr 2
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) q
  let dIso := J.isoRightDerivedObj SU q ≪≫ H.mapIso eCU ≪≫
    (A.sc q).mapHomologyIso EU
  refine ⟨dIso.symm.addCommGroupIsoToAddEquiv, ?_⟩
  intro x
  apply dIso.addCommGroupIsoToAddEquiv.injective
  change dIso.addCommGroupIsoToAddEquiv _ =
    dIso.addCommGroupIsoToAddEquiv (dIso.addCommGroupIsoToAddEquiv.symm _)
  rw [AddEquiv.apply_symm_apply]
  have hc' := congrArg
    ((HomologicalComplex.shortComplexFunctor AddCommGrpCat.{u} (.up ℕ) q).map) hc
  simp only [Functor.map_comp] at hc'
  have hh := homology_restriction_transport
    (((ST.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc q)
    (((SU.mapHomologicalComplex (.up ℕ)).obj J.cocomplex).sc q) (A.sc q) ET EU
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map φ)
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map eCT.hom)
    ((HomologicalComplex.shortComplexFunctor _ (.up ℕ) q).map eCU.hom) τ hc'
  have hn := J.rightDerived_app_eq α q
  have heq : (NatTrans.rightDerived α q).app G ≫ (J.isoRightDerivedObj SU q).hom =
      (J.isoRightDerivedObj ST q).hom ≫ H.map φ := by
    rw [hn]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rfl
  have hh' : H.map φ ≫ H.map eCU.hom ≫ ((A.sc q).mapHomologyIso EU).hom =
      H.map eCT.hom ≫ ((A.sc q).mapHomologyIso ET).hom ≫ τ.app (A.homology q) := hh
  have heq' := congrArg
    (fun g ↦ g ≫ H.map eCU.hom ≫ ((A.sc q).mapHomologyIso EU).hom) heq
  simp only [Category.assoc] at heq'
  rw [hh'] at heq'
  have hz := ConcreteCategory.congr_hom heq' (resolutionOpenComparison f F I q W R x)
  change dIso.hom _ = _
  change dIso.hom _ = (τ.app (A.homology q)) x
  have ht : ((J.isoRightDerivedObj ST q).hom ≫ H.map eCT.hom ≫
      ((A.sc q).mapHomologyIso ET).hom) (resolutionOpenComparison f F I q W R x) = x := by
    exact (resolutionOpenComparison f F I q W R).symm_apply_apply x
  change dIso.hom _ = (τ.app (A.homology q))
    (((J.isoRightDerivedObj ST q).hom ≫ H.map eCT.hom ≫
      ((A.sc q).mapHomologyIso ET).hom) (resolutionOpenComparison f F I q W R x)) at hz
  rw [ht] at hz
  exact hz


end AlgebraicGeometry.Scheme.Modules

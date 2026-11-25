/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleResolutionSectionCanonicalComparison
import WeilConjectures.AlgebraicGeometry.EtaleOpenFreeSheafUnitCoherence
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorExtension
import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
import WeilConjectures.AlgebraicGeometry.EtaleOpenObjectCohomologyMap

/-!
# Canonical restriction on resolution-section cocycles

Source: Stacks Project, Tags 0A50 and 03F3; the free-sheaf sections adjunction
and the exact inverse-image composition comparison.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the free-representable map is restriction of sections.
This is naturality of the sheafification and free-abelian adjunctions, followed
by naturality of the universe-lifted Yoneda equivalence. -/
private lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f) := by
  change EtaleOpenComparison.freeSectionsEquiv A F.obj
    ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (uliftYoneda.map a)) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change uliftYonedaEquiv (((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _)
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (uliftYoneda.map a) ≫
      ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _ f))) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

set_option backward.isDefEq.respectTransparency false in
/-- Cocycle-level restriction identity underlying the canonical open comparison.
Source: Stacks Project, Tags 0A50 and 03F3; normalized Hom-cocycle calculation.
(blueprint: lem-weil-pbc-etale-resolution-section-canonical-open-to-open-cycle)

The proof expands the two `open_cocycle` normalization identities, rewrites the
Ext class of the restricted cocycle using `InjectiveResolution.mk₀_comp_extMk`,
and applies the identity-generator coherence and exact inverse-image composition
comparison. This is the cocycle calculation before passing to arbitrary homology
classes via surjectivity of `homologyπ`.
-/
theorem resolutionSection_canonical_open_to_open_cycle {X : Scheme.{u}}
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution G) (c : ResolutionSectionCanonicalComparison G I)
    (A B : X.Opens) (h : A ≤ B) (q : ℕ)
    (z : (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).cycles q) :
    let K := (((etaleSectionFunctor (Scheme.Etale.mk A.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)
    let L := (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex)
    let φ := etaleSectionMap
      (MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι _) :
        Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι) I.cocomplex
    c.openEquiv A q (K.homologyπ q ((HomologicalComplex.cyclesMap φ q) z)) =
      openCohomologyRestriction h G q (c.openEquiv B q (L.homologyπ q z)) := by
  classical
  dsimp only
  let K := (((etaleSectionFunctor (Scheme.Etale.mk A.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let L := (((etaleSectionFunctor (Scheme.Etale.mk B.ι)).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex)
  let a : Scheme.Etale.mk A.ι ⟶ Scheme.Etale.mk B.ι :=
    MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h)
  let φ := etaleSectionMap a I.cocomplex
  let f := (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
    (Scheme.Etale.mk B.ι) (I.cocomplex.X q)).symm ((L.iCycles q) z)
  have hf : f ≫ I.cocomplex.d q (q + 1) = 0 := by
    apply (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology
      (Scheme.Etale.mk B.ι) (I.cocomplex.X (q + 1))).injective
    rw [EtaleOpenComparison.sectionsEquiv_naturality]
    simp only [f, AddEquiv.apply_symm_apply, map_zero]
    change L.d q (q + 1) ((L.iCycles q) z) = 0
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.iCycles_d]
    rfl
  have hfa : ((etaleOpenFreeSheaf X).map a ≫ f) ≫ I.cocomplex.d q (q + 1) = 0 := by
    simp only [Category.assoc, hf, comp_zero]
  have hz : K.iCycles q ((HomologicalComplex.cyclesMap φ q) z) =
      EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology (Scheme.Etale.mk A.ι)
        (I.cocomplex.X q) ((etaleOpenFreeSheaf X).map a ≫ f) := by
    rw [sectionsEquiv_precomp]
    simp only [f, AddEquiv.apply_symm_apply]
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i,
      ConcreteCategory.comp_apply]
    rfl
  rw [c.open_cocycle A q _ hfa _ hz,
    c.open_cocycle B q f hf z (by simp only [f, AddEquiv.apply_symm_apply]; rfl)]
  rw [← I.mk₀_comp_extMk f (q + 1) rfl hf ((etaleOpenFreeSheaf X).map a)]
  let x := I.extMk f (q + 1) rfl hf
  let FA := upperStar AddCommGrpCat.{u + 1} A.ι
  let FB := upperStar AddCommGrpCat.{u + 1} B.ι
  let T := upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)
  let e := upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) B.ι
    A.ι (X.homOfLE_ι h).symm
  change (Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit A)).comp
    (((Abelian.Ext.mk₀ ((etaleOpenFreeSheaf X).map a)).comp x
      (zero_add q)).mapExactFunctor FA) (zero_add q) =
    ((Abelian.Ext.mk₀
      ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (X.homOfLE h)).inv.app
        (AddCommGrpCat.of (ULift ℤ)))).comp
      (((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit B)).comp
        (x.mapExactFunctor FB) (zero_add q)).mapExactFunctor T)
      (zero_add q)).comp (Abelian.Ext.mk₀ (e.inv.app G)) (add_zero q)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀_assoc]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  have hc := Abelian.Ext.mapExactFunctor_comp_mk₀_eq_sheaf FB T FA e x
  have hc' := congrArg (fun y ↦
    ((Abelian.Ext.mk₀ (etaleOpenFreeSheafUnit A ≫
      FA.map ((etaleOpenFreeSheaf X).map a))).comp y (zero_add q)).comp
        (Abelian.Ext.mk₀ (e.inv.app G)) (add_zero q)) hc
  simp only [Abelian.Ext.comp_assoc_of_third_deg_zero,
    Abelian.Ext.mk₀_comp_mk₀_assoc] at hc'
  simp only [Abelian.Ext.mk₀_comp_mk₀, Iso.hom_inv_id_app, Abelian.Ext.comp_mk₀_id,
    Category.assoc] at hc'
  erw [show etaleOpenFreeSheafUnit A ≫
      FA.map ((etaleOpenFreeSheaf X).map a) ≫
        e.hom.app ((etaleOpenFreeSheaf X).obj (Scheme.Etale.mk B.ι)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
        (X.homOfLE h)).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
      T.map (etaleOpenFreeSheafUnit B) from
        etaleOpenFreeSheafUnit_coherence B A h] at hc'
  exact hc'

end AlgebraicGeometry.Etale

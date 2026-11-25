/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import WeilConjectures.AlgebraicGeometry.DerivedDirectImagePreservesQCoh
import WeilConjectures.AlgebraicGeometry.KInjectiveMayerVietorisPresentation
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction

/-! # Derived Mayer--Vietoris for a qcqs scheme

Source: Stacks Project, Cohomology, Tag 08BV; Derived Categories of Schemes, Tag 08D5
(blueprint: lem-pc-derived-mayer-vietoris-triangle).
-/

@[expose] public section

universe u₁ w₁

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048

private theorem qcoh_overEquiv (X : Scheme.{u₁}) (U : X.Opens)
    (M : SheafOfModules.{u₁} ((moduleRings X.toRingedSpace).over U)) [M.IsQuasicoherent] :
    ((Scheme.Modules.overEquiv U).functor.obj M).IsQuasicoherent := by
  have : ∀ W, (Over.post (X := W) U.overEquivalence.symm.functor).IsContinuous
      ((Opens.grothendieckTopology ↥U).over W)
      (((Opens.grothendieckTopology X).over U).over _) := fun W ↦
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.symm.functor _ _).overPost W)
  apply SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    (U.overEquivalence.symm.functor) _
    (U.sheafOfModulesEquivOverUnit (moduleRings X.toRingedSpace))

private theorem qcoh_openRestriction (X : Scheme.{u₁}) (U : X.Opens)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings U.toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    schemeDerivedQCohProperty U.toScheme
      ((schemeOpenRestriction X U).mapDerivedCategory.obj E) := by
  classical
  let F := schemeOpenRestriction X U
  let K := DerivedCategory.Q.objPreimage E
  let e : DerivedCategory.Q.obj K ≅ E := DerivedCategory.Q.objObjPreimageIso E
  intro n
  let comparison :
      (DerivedCategory.homologyFunctor _ n).obj (F.mapDerivedCategory.obj E) ≅
        F.obj ((DerivedCategory.homologyFunctor _ n).obj E) :=
    (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategory.mapIso e.symm) ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso (F.mapDerivedCategoryFactors.app K) ≪≫
      (DerivedCategory.homologyFunctorFactors _ n).app _ ≪≫
      (F.mapHomologicalComplexHomologyIso (.up ℤ) n).app K ≪≫
      F.mapIso ((DerivedCategory.homologyFunctorFactors _ n).symm.app K ≪≫
        (DerivedCategory.homologyFunctor _ n).mapIso e)
  have := hE n
  have := SheafOfModules.isQuasicoherent_over
    ((DerivedCategory.homologyFunctor _ n).obj E) U
  have hF := qcoh_overEquiv X U (((DerivedCategory.homologyFunctor _ n).obj E).over U)
  exact (SheafOfModules.isQuasicoherent
    (moduleRings U.toScheme.toRingedSpace)).prop_of_iso comparison.symm hF

/-- A two-open cover gives the direct-image Mayer--Vietoris distinguished triangle.
Source: Stacks Project, Tags 08BV and 08D5
(blueprint: lem-pc-derived-mayer-vietoris-triangle).

Proof:
1. Choose a K-injective resolution with injective terms
   (prop-pur-kinjective-resolutions-exist). Its restrictions remain K-injective
   (lem-sc-derived-k-injective-restrict-open), and compute the derived direct images
   (lemma-coherent-base-change-invertible-sheaves).
2. The sheaf gluing axiom gives exactness at the first two terms of the sectionwise
   sequence. Injectivity gives surjectivity of the difference of restriction maps
   (lem-sc-ringed-space-injective-restriction-surjective). This holds in every degree.
3. Apply the non-split short-exact-sequence triangle
   (lem-weil-pbc-complex-ses-triangle), and transport along the resolution isomorphism.
   The first map is the pair of units and the second is the difference of restrictions.
4. Restriction preserves quasi-coherent cohomology. Each open immersion is qcqs, so
   lem-pc-derived-direct-image-preserves-qcoh places the three direct-image terms in
   D_QCoh. Their biproduct and the triangle therefore lie in that full subcategory. -/
theorem schemeDerived_mayerVietoris_triangle
    (X : Scheme.{u₁}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsCompact (V : Set X))
    (hcover : U ⊔ V = ⊤)
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings V.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings (U ⊓ V).toScheme.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E) :
    ∃ (adjU : (schemeOpenRestriction X U).mapDerivedCategory ⊣ schemeDerivedDirectImage U.ι)
      (adjV : (schemeOpenRestriction X V).mapDerivedCategory ⊣ schemeDerivedDirectImage V.ι)
      (adjUV : (schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory ⊣
        schemeDerivedDirectImage (U ⊓ V).ι)
      (δ : (schemeDerivedDirectImage (U ⊓ V).ι).obj
        ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E) ⟶ E⟦(1 : ℤ)⟧),
      Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV E)))
        δ ∈ distTriang (schemeDerivedCategory X) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage U.ι).obj
          ((schemeOpenRestriction X U).mapDerivedCategory.obj E)) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction X V).mapDerivedCategory.obj E)) ∧
      schemeDerivedQCohProperty X
        ((schemeDerivedDirectImage (U ⊓ V).ι).obj
          ((schemeOpenRestriction X (U ⊓ V)).mapDerivedCategory.obj E)) := by
  classical
  let A := SheafOfModules.{u₁} (moduleRings X.toRingedSpace)
  let K := DerivedCategory.Q.objPreimage E
  let I := (CochainComplex.kInjectiveResolutionFunctor.{u₁} A).obj K
  let s : K ⟶ I := (CochainComplex.toKInjectiveResolution.{u₁} A).app K
  have hs : QuasiIso s :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u₁} A K).2
  let e : DerivedCategory.Q.obj I ≅ E :=
    (asIso (DerivedCategory.Q.map s)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso E
  let adj (W : X.Opens)
      [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings W.toScheme.toRingedSpace))] :
      (schemeOpenRestriction X W).mapDerivedCategory ⊣ schemeDerivedDirectImage W.ι :=
    let a : schemeOpenRestriction X W ⊣
        RingedSpace.moduleDirectImage W.ι.toLRSHom.toShHom :=
      (Scheme.Modules.restrictAdjunction W.ι).ofNatIsoLeft
        (Scheme.Modules.overFunctorEquiv W).symm
    a.mapDerivedCategoryRightDerivedAdjunction
  let adjU := adj U
  let adjV := adj V
  let adjUV := adj (U ⊓ V)
  obtain ⟨B, C, f, g, hz, eB, eC, hS, hf, hg⟩ :=
    schemeKInjective_mayerVietoris_presentation X U V hcover I
      (fun n ↦ inferInstance) E e adjU adjV adjUV
  let δ := eC.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e.hom⟦(1 : ℤ)⟧'
  have htri : Triangle.mk (biprod.lift (adjU.unit.app E) (adjV.unit.app E))
        (biprod.desc
          (schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_left) adjU adjUV E)
          (-(schemeDerivedOpenDirectImageRestriction X (homOfLE inf_le_right) adjV adjUV E))) δ ∈
      distTriang (schemeDerivedCategory X) := by
    apply isomorphic_distinguished _ (DerivedCategory.triangleOfSES_distinguished hS)
    refine (Triangle.isoMk _ _ e eB eC hf hg ?_).symm
    change DerivedCategory.triangleOfSESδ hS ≫ e.hom⟦(1 : ℤ)⟧' =
      eC.hom ≫ (eC.inv ≫ DerivedCategory.triangleOfSESδ hS ≫ e.hom⟦(1 : ℤ)⟧')
    simp only [Iso.hom_inv_id_assoc]
  have hq (W : X.Opens) (hW : IsCompact (W : Set X))
      [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings W.toScheme.toRingedSpace))] :
      schemeDerivedQCohProperty X ((schemeDerivedDirectImage W.ι).obj
        ((schemeOpenRestriction X W).mapDerivedCategory.obj E)) := by
    let : CompactSpace W := isCompact_iff_compactSpace.mp hW
    exact schemeDerivedDirectImage_preserves_QCoh W.ι _ (qcoh_openRestriction X W E hE)
  exact ⟨adjU, adjV, adjUV, δ, htri, hq U hU, hq V hV,
    hq (U ⊓ V) (by
      simpa only [Opens.coe_inf] using
        QuasiSeparatedSpace.inter_isCompact (U : Set X) (V : Set X) U.isOpen hU V.isOpen hV)⟩

end AlgebraicGeometry

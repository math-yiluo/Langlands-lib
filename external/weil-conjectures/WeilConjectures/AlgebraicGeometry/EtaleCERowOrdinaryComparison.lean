/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import WeilConjectures.AlgebraicGeometry.EtaleRowSectionsExtend

/-! # Explicit ordinary cohomology comparisons for CE rows

Source: Stacks Project, Tags 06XR, 01F8 and 015J.
(blueprint: lem-weil-pbc-ce-row-ordinary-naturality).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Evaluate Ext cocycles on an arbitrary injective row at 1, then remove the extension
by zero. All maps are constructed from the specified resolution.
Source: Stacks Project, Tags 06XR and 01F8.
(blueprint: lem-weil-pbc-ce-row-ordinary-naturality). -/
noncomputable def ceRowOrdinaryIso (X : Scheme.{uNatural})
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (R : InjectiveResolution G) (p : ℕ) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R.cocomplex).homology p ≅
      AddCommGrpCat.of (Sheaf.H G p) :=
  (HomologicalComplex.extendHomologyIso
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R.cocomplex) ComplexShape.embeddingUpNat
        (j := p) (j' := (p : ℤ)) rfl).symm ≪≫
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{uNatural + 1}
    (ComplexShape.up ℤ) (p : ℤ)).mapIso
      (HomologicalComplex.mapExtendIso R.cocomplex ComplexShape.embeddingUpNat
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})).symm ≪≫
  (SheafPullbackResolution.classSectionsIso X R.cochainComplex (p : ℤ)).symm ≪≫
  R.extAddEquivCohomologyClass.toAddCommGrpIso.symm

/-- Apply the sections pullback unit and a comparison of nonnegative rows.
Source: Stacks Project, Tag 015K.
(blueprint: lem-weil-pbc-ce-row-ordinary-naturality). -/
noncomputable def ceRowSectionsMap {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J ⟶ J') :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J' :=
  (NatTrans.mapHomologicalComplex (ceSectionsUnit f) (ComplexShape.up ℕ)).app J ≫
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ

/-- Regard a prescribed augmented CE row as its injective resolution.
Source: Stacks Project, Tag 015J.
(blueprint: lem-weil-pbc-ce-row-ordinary-naturality). -/
def cePresentationRow {X : Scheme.{uNatural}}
    {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}
    (D : EtaleTermwiseHypercohomology X K) (q : ℤ) : InjectiveResolution (K.obj.X q) where
  cocomplex := D.I.X q
  ι := D.a.f q
  injective := D.terms q
  quasiIso := D.rows q

set_option backward.isDefEq.respectTransparency false in
/-- The explicit row comparison computes pullback followed by a coefficient map.
Source: Stacks Project, Tag 01F8, equations 01F9 and 01FA; Tags 06XR and 08J6.
(blueprint: lem-weil-pbc-ce-row-ordinary-naturality).

Proof. Extend the rows and their comparison by zero. The map-extend isomorphism
identifies the extended sections-unit map with the sections map on the extended
rows. Represent an Ext class by a cocycle from the constant integer sheaf into R.
Apply inverse image, the constant-sheaf comparison and the extended row comparison.
The augmentation equation identifies the resulting Ext class with pullback followed
by v: the injective target computes Ext, and augmentation-compatible comparison maps
are homotopic. Evaluation at 1 commutes with inverse image and postcomposition, so
this cocycle map is precisely ceRowSectionsMap. Descend to homology and transport
through the map-extend and extend-homology isomorphisms. This gives the displayed
square with ceRowOrdinaryIso, including p = 0, zero rows and empty schemes. -/
theorem ceRowOrdinaryIso_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (R : InjectiveResolution G) (R' : InjectiveResolution G')
    (v : (upperStar AddCommGrpCat.{uNatural + 1} f).obj G ⟶ G')
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj R.cocomplex ⟶ R'.cocomplex)
    (hφ : (upperStar AddCommGrpCat.{uNatural + 1} f).map
        ((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G).inv ≫ R.ι.f 0) ≫
          φ.f 0 =
      v ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 G').inv ≫ R'.ι.f 0)
    (p : ℕ) :
    HomologicalComplex.homologyMap (ceRowSectionsMap f φ) p ≫
        (ceRowOrdinaryIso Y G' R' p).hom =
      (ceRowOrdinaryIso X G R p).hom ≫
        AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) := by
  let ψ := ceExtendedRowMap f φ
  have hψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map R.ι' ≫ ψ =
      (HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.up ℤ) 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map v ≫ R'.ι' := by
    apply (cancel_epi ((HomologicalComplex.singleMapHomologicalComplex
      (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.up ℤ) 0).inv.app G)).1
    apply HomologicalComplex.from_single_hom_ext
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f]
    dsimp only [ψ, ceExtendedRowMap]
    simp only [HomologicalComplex.comp_f]
    rw [R.ι'_f_zero, R'.ι'_f_zero]
    erw [HomologicalComplex.extendMap_f φ ComplexShape.embeddingUpNat (i := 0) rfl]
    dsimp [HomologicalComplex.mapExtendIso, HomologicalComplex.Hom.isoOfComponents]
    erw [HomologicalComplex.mapExtendX_hom_eq R.cocomplex
      (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.embeddingUpNat.r_f 0)]
    simp only [InjectiveResolution.cochainComplexXIso, HomologicalComplex.extendXIso,
      HomologicalComplex.extend.XIso, eqToIso, HomologicalComplex.singleMapHomologicalComplex,
      NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app,
      HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
      CochainComplex.singleFunctor,
      HomologicalComplex.single_map_f_self, eqToHom_map, Functor.map_comp,
      Category.assoc, eqToHom_refl, Category.id_comp, Category.comp_id]
    simp only [↓reduceDIte, Category.id_comp, ← Category.assoc, eqToHom_trans,
      eqToHom_refl]
    simp [HomologicalComplex.extend, HomologicalComplex.extend.X]
    have hh : (upperStar AddCommGrpCat.{uNatural + 1} f).map (R.ι.f 0) ≫ φ.f 0 =
        v ≫ R'.ι.f 0 := by
      simpa [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
        HomologicalComplex.single] using hφ
    simpa only [Category.assoc, InjectiveResolution.cochainComplexXIso,
      HomologicalComplex.extendXIso, HomologicalComplex.extend.XIso, eqToIso] using!
      congrArg (fun z ↦ z ≫ (R'.cochainComplexXIso 0 0 rfl).inv) hh
  have hi := ceIntegerSectionsIso_naturality f G G' R R' v ψ hψ p
  have hs := congrArg (fun k ↦ HomologicalComplex.homologyMap k (p : ℤ))
    (ceRowSectionsMap_extend f φ)
  simp only [HomologicalComplex.homologyMap_comp] at hs
  have he : HomologicalComplex.homologyMap (ceRowSectionsMap f φ) p ≫
      (HomologicalComplex.extendHomologyIso
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R'.cocomplex)
        ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl).inv =
    (HomologicalComplex.extendHomologyIso
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R.cocomplex)
        ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl).inv ≫
      HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap (ceRowSectionsMap f φ)
          ComplexShape.embeddingUpNat) (p : ℤ) := by
    rw [← cancel_epi (HomologicalComplex.extendHomologyIso
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj R.cocomplex)
      ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl).hom]
    simp only [Iso.hom_inv_id_assoc]
    erw [← HomologicalComplex.extendHomologyIso_hom_naturality_assoc
      (ceRowSectionsMap f φ) ComplexShape.embeddingUpNat (j := p) (j' := (p : ℤ)) rfl]
    simp only [Iso.hom_inv_id, Category.comp_id]
  dsimp only [ceRowOrdinaryIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom]
  simp only [HomologicalComplex.homologyFunctor_map, Category.assoc]
  rw [reassoc_of% he]
  erw [← reassoc_of% hs]
  erw [hi]


end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import WeilConjectures.AlgebraicGeometry.EtaleRowExtHomologySquare
import WeilConjectures.AlgebraicGeometry.EtaleRowSectionsEvaluationSquare

/-! # Ordinary comparison before removing extension by zero

Source: Stacks Project, Tags 06XR, 01F8 and 08J6.
(blueprint: lem-weil-pbc-row-integer-sections).
-/

@[expose] public section

universe uNatural v w w'
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Abelian
namespace AlgebraicGeometry.Etale
open Scheme

/-- Apply the sections unit and an integer-indexed comparison.
Source: Stacks Project, Tag 015K; evaluation maps in Tags 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-integer-sections). -/
noncomputable def ceIntegerSectionsMap {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J ⟶ J') :
    ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J ⟶
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj J' :=
  (NatTrans.mapHomologicalComplex (ceSectionsUnit f) (ComplexShape.up ℤ)).app J ≫
    ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ

/-- Extend a supplied row map, commuting inverse image with extension by zero.
Source: Stacks Project, Tags 015J and 015K.
(blueprint: lem-weil-pbc-row-integer-sections). -/
noncomputable def ceExtendedRowMap {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {J : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    {J' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℕ}
    (φ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj J ⟶ J') :
    ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (J.extend ComplexShape.embeddingUpNat) ⟶
      J'.extend ComplexShape.embeddingUpNat :=
  (J.mapExtendIso ComplexShape.embeddingUpNat
    (upperStar AddCommGrpCat.{uNatural + 1} f)).hom ≫
    HomologicalComplex.extendMap φ ComplexShape.embeddingUpNat

set_option backward.isDefEq.respectTransparency false in
private lemma map_square {C : Type w} {D : Type w'}
    [Category.{v} C] [Category.{v} D] (F : C ⥤ D)
    {A B A' B' : C} {c : A ⟶ A'} {s : A ⟶ B} {s' : A' ⟶ B'} {b : B ⟶ B'}
    (h : c ≫ s' = s ≫ b) : F.map c ≫ F.map s' = F.map s ≫ F.map b := by
  rw [← F.map_comp, h, F.map_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The integer-indexed sections map computes the coefficient and pullback map on Ext.
Source: Stacks Project, Tags 06XR, 01F8 (equations 01F9 and 01FA) and 08J6.
(blueprint: lem-weil-pbc-row-integer-sections).

Proof. Represent an Ext class by a cocycle from the constant integer sheaf into R.
Apply the exact inverse-image functor, precompose with the inverse constant-sheaf
comparison, and postcompose with ψ. The augmentation equality makes the two roofs
agree after postcomposition with v, by ext_mapExactFunctor_coefficient_cocycle.
CohomologyClass.mk and Cocycle.fromSingleMk are surjective, so the equality descends
from cocycles to Hom-complex homology. Evaluation at 1 commutes with postcomposition.
The constant-sheaf transpose identifies evaluation after inverse image with the
sections unit; the terminal-sections comparison identifies that unit with ceSectionsUnit.
Thus complexSectionsIso intertwines homPullbackMap with ceIntegerSectionsMap. Apply
homology, then cancel the Ext/resolution and classSections isomorphisms to obtain the
square below. This argument makes no comparison with nonnegative sections homology;
that extension-by-zero transport is a separate step. Degree zero, zero sheaves, zero
comparisons and empty schemes obey the same cocycle calculation. -/
theorem ceIntegerSectionsIso_naturality {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (G' : Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    (R : InjectiveResolution G) (R' : InjectiveResolution G')
    (v : (upperStar AddCommGrpCat.{uNatural + 1} f).obj G ⟶ G')
    (ψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj R.cochainComplex ⟶ R'.cochainComplex)
    (hψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
        (ComplexShape.up ℤ)).map R.ι' ≫ ψ =
      (HomologicalComplex.singleMapHomologicalComplex
        (upperStar AddCommGrpCat.{uNatural + 1} f) (ComplexShape.up ℤ) 0).hom.app G ≫
      (CochainComplex.singleFunctor _ 0).map v ≫ R'.ι')
    (p : ℕ) :
    HomologicalComplex.homologyMap (ceIntegerSectionsMap f ψ) (p : ℤ) ≫
        (SheafPullbackResolution.classSectionsIso Y R'.cochainComplex (p : ℤ)).inv ≫
        (R'.extAddEquivCohomologyClass
      (X := SheafPullbackResolution.ZSheaf Y) (n := p)).toAddCommGrpIso.inv =
      (SheafPullbackResolution.classSectionsIso X R.cochainComplex (p : ℤ)).inv ≫
        (R.extAddEquivCohomologyClass
      (X := SheafPullbackResolution.ZSheaf X) (n := p)).toAddCommGrpIso.inv ≫
        AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) := by
  let L := upperStar AddCommGrpCat.{uNatural + 1} f
  let α := (upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
    (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ))
  let c := SheafPullbackResolution.homPullbackMap L α
    R.cochainComplex R'.cochainComplex ψ
  have hc := ceComplexSectionsSquare f (K := R.cochainComplex)
    (K' := R'.cochainComplex) ψ
  change c ≫ (SheafPullbackResolution.complexSectionsIso Y R'.cochainComplex).hom =
    (SheafPullbackResolution.complexSectionsIso X R.cochainComplex).hom ≫
      ceIntegerSectionsMap f ψ at hc
  have hh := map_square
    (HomologicalComplex.homologyFunctor AddCommGrpCat (.up ℤ) (p : ℤ)) hc
  simp only [HomologicalComplex.homologyFunctor_map] at hh
  have he := ceExtHomologySquare f G G' R R' v ψ hψ p
  have hf :
      R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (SheafPullbackResolution.classSectionsIso X R.cochainComplex (p : ℤ)).hom ≫
        HomologicalComplex.homologyMap (ceIntegerSectionsMap f ψ) (p : ℤ) =
      AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) ≫
        R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
        (SheafPullbackResolution.classSectionsIso Y R'.cochainComplex (p : ℤ)).hom := by
    change R.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
      (leftHomologyData _ R.cochainComplex (p : ℤ)).homologyIso.inv ≫
      HomologicalComplex.homologyMap
        (SheafPullbackResolution.complexSectionsIso X R.cochainComplex).hom (p : ℤ) ≫
      HomologicalComplex.homologyMap (ceIntegerSectionsMap f ψ) (p : ℤ) =
        AddCommGrpCat.ofHom ((Sheaf.H.map v p).comp (cohomologyMap f G p)) ≫
          R'.extAddEquivCohomologyClass.toAddCommGrpIso.hom ≫
          (leftHomologyData _ R'.cochainComplex (p : ℤ)).homologyIso.inv ≫
          HomologicalComplex.homologyMap
            (SheafPullbackResolution.complexSectionsIso Y R'.cochainComplex).hom (p : ℤ)
    erw [← hh]
    simpa only [Category.assoc] using congrArg
      (fun z ↦ z ≫ HomologicalComplex.homologyMap
        (SheafPullbackResolution.complexSectionsIso Y R'.cochainComplex).hom (p : ℤ)) he
  rw [Iso.eq_inv_comp, ← Category.assoc, Iso.eq_inv_comp]
  simp only [← Category.assoc]
  rw [Iso.comp_inv_eq, Iso.comp_inv_eq]
  simpa only [Category.assoc] using hf

end AlgebraicGeometry.Etale

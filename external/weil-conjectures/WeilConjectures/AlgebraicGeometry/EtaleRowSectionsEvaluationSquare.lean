/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ExtPullbackHomComplex
public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.AlgebraicGeometry.SheafHExtResolutionSectionsIso
import WeilConjectures.AlgebraicGeometry.ConstantSheafPullbackTranspose

/-! # Evaluation square for integer-indexed sections

Source: Stacks Project, Tags 015K, 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-sections-evaluation-square).
-/
@[expose] public section
universe uNatural
open CategoryTheory CategoryTheory.Limits CochainComplex HomComplex Abelian
namespace AlgebraicGeometry.Etale
open Scheme

/-- Evaluation of the integer Hom complex commutes with pullback and sections.
Source: Stacks Project, Tags 015K, 01F9 and 01FA.
(blueprint: lem-weil-pbc-row-sections-evaluation-square).

Proof. Set L = f inverse image and α equal to the inverse constant-sheaf
comparison. Expand complexSectionsIso in degree n on an arbitrary cochain a.
The inverse fromSingleEquiv converts it into a morphism from the constant integer
sheaf into K in degree n. The definition of homPullbackMap sends it to
fromSingleMk (α;L(fromSingleEquiv a);ψ in degree n). Applying evaluation cancels
fromSingleMk with fromSingleEquiv. Naturality of the adjunction hom equivalence
then moves postcomposition by ψ outside sectionsEquiv. The constant-sheaf
pullback transpose identifies evaluation of α;L(fromSingleEquiv a) with the
adjunction unit on global sections. Naturality of ΓNatIsoSheafSections and the
formula for lowerStarCompGlobalSectionsIso identify this unit with ceSectionsUnit.
Thus both sides have the same value on every degree-n cochain. Extensionality
of group morphisms and complex maps gives the square. Nothing here uses
injectivity, a resolution augmentation, or a nonnegative degree. Zero complexes,
zero maps, negative degrees and empty schemes obey the same component formulas. -/
theorem ceComplexSectionsSquare {X Y : Scheme.{uNatural}} (f : Y ⟶ X)
    {K : CochainComplex (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    {K' : CochainComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) ℤ}
    (ψ : ((upperStar AddCommGrpCat.{uNatural + 1} f).mapHomologicalComplex
      (.up ℤ)).obj K ⟶ K') :
    SheafPullbackResolution.homPullbackMap (upperStar AddCommGrpCat.{uNatural + 1} f)
        ((upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
          (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ))) K K' ψ ≫
        (SheafPullbackResolution.complexSectionsIso Y K').hom =
      (SheafPullbackResolution.complexSectionsIso X K).hom ≫
        ((NatTrans.mapHomologicalComplex (ceSectionsUnit f) (.up ℤ)).app K ≫
          ((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
            (.up ℤ)).map ψ) := by
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let Γ' := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
  let L := upperStar AddCommGrpCat.{uNatural + 1} f
  let α := (upperStarConstantSheafIso AddCommGrpCat.{uNatural + 1} f).inv.app
    (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ))
  have htranspose (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
      (a : SheafPullbackResolution.ZSheaf X ⟶ F) :
      SheafPullbackResolution.sectionsEquiv Y (L.obj F) (α ≫ L.map a) =
        ((ceSectionsUnit f).app F) (SheafPullbackResolution.sectionsEquiv X F a) := by
    have h := constantSheaf_pullback_transpose f
      (AddCommGrpCat.of (ULift.{uNatural + 1} ℤ)) F a
    dsimp only [SheafPullbackResolution.sectionsEquiv, AddEquiv.trans_apply,
      Adjunction.homAddEquiv_apply]
    rw [h]
    have hunit :
        ((Functor.leftUnitor Γ).inv ≫
          Functor.whiskerRight (upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit
            Γ ≫ (Functor.associator _ _ _).hom ≫
          Functor.whiskerLeft L
            (lowerStarCompGlobalSectionsIso AddCommGrpCat.{uNatural + 1} f).hom).app F =
        (ceSectionsUnit f).app F := by
      dsimp only [Γ, L]
      simp only [ceSectionsUnit, lowerStarCompGlobalSectionsIso, Iso.trans_hom,
        Iso.symm_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
        Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.associator_hom_app,
        Functor.whiskerLeft_app, Category.id_comp]
      rw [← Category.assoc]
      have hn := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}
          terminalIsTerminal).hom.naturality
          ((upperStarLowerStarAdjunction AddCommGrpCat.{uNatural + 1} f).unit.app F)
      simp only [Functor.comp_obj, Functor.id_obj] at hn
      rw [hn, Category.assoc]
    rw [hunit]
    rfl
  ext n a
  obtain ⟨a, rfl⟩ := Cochain.fromSingleMk_surjective a n (zero_add n)
  change SheafPullbackResolution.sectionsEquiv Y (K'.X n)
      (Cochain.fromSingleEquiv (zero_add n)
        (Cochain.fromSingleMk
          (α ≫ L.map (Cochain.fromSingleEquiv (zero_add n)
            (Cochain.fromSingleMk a (zero_add n))) ≫ ψ.f n) (zero_add n))) =
    Γ'.map (ψ.f n) (((ceSectionsUnit f).app (K.X n))
      (SheafPullbackResolution.sectionsEquiv X (K.X n)
        (Cochain.fromSingleEquiv (zero_add n) (Cochain.fromSingleMk a (zero_add n)))))
  simp only [Cochain.fromSingleEquiv_fromSingleMk]
  rw [← Category.assoc]
  dsimp only [SheafPullbackResolution.sectionsEquiv, AddEquiv.trans_apply,
    Adjunction.homAddEquiv_apply]
  rw [Adjunction.homEquiv_naturality_right]
  change Γ'.map (ψ.f n)
      (SheafPullbackResolution.sectionsEquiv Y (L.obj (K.X n)) (α ≫ L.map a)) = _
  rw [htranspose]
  rfl

end AlgebraicGeometry.Etale

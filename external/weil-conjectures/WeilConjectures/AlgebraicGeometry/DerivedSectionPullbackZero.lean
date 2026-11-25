/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RawRestrictedCohomologyComparisonMap
import WeilConjectures.AlgebraicGeometry.DerivedSectionSingleUnit

/-! # Degree-zero derived section pullback

Source: Stacks Project, Tags 07A6 and 0D6F.
(blueprint: lem-sbc-derived-section-pullback-zero).
-/

@[expose] public section


universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale.RawRestrictedComparison

private theorem map_zero_comparison {C D : Type*} [Category* C] [Category* D]
    (H : C ⥤ D) (J : D ⥤ C) (e : J ⋙ H ≅ 𝟭 D) {A B : D} {K K' : C}
    (z : H.obj K ≅ A) (z' : H.obj K' ≅ B) (u : J.obj A ⟶ K) (v : J.obj B ⟶ K')
    (t : K ⟶ K') (s : A ⟶ B)
    (hu : H.map u ≫ z.hom = e.hom.app A)
    (hv : H.map v ≫ z'.hom = e.hom.app B) (h : u ≫ t = J.map s ≫ v) :
    H.map t ≫ z'.hom = z.hom ≫ s := by
  have he : H.map u = e.hom.app A ≫ z.inv := by
    apply (cancel_mono z.hom).mp
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hu
  have : IsIso (H.map u) := by rw [he]; infer_instance
  apply (cancel_epi (H.map u)).mp
  rw [reassoc_of% hu]
  have hh := congrArg (fun f ↦ H.map f ≫ z'.hom) h
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [hv] at hh
  exact hh.trans (e.hom.naturality s)

/-- Degree-zero derived section pullback before any restriction-triangle comparison.
Source: Stacks Project, Tag 07A6, derived adjunction, and the defining composite
unit of the Leray comparison.
(blueprint: lem-sbc-derived-section-pullback-zero).

Proof: Put R = W^* G. Compare the source with R[0] by the exact inverse-image
single comparison. Naturality of the derived unit moves that comparison through
pullback. Resolve R and f^*R by bounded-below injective resolutions and lift the
underived adjunction unit to the resolutions. The derived unit is characterized
by its composite with the right-derived unit, so the lifted morphism computes
it. The Leray comparison is characterized by its composite unit, hence its
composite with that morphism is the lift of the ordinary section pullback.
In degree zero the augmentations identify the kernels of the first differentials
with the original sheaves, because sections are left exact. These are exactly
the homologyRightDerivedFunctorObjSingleFunctorIso and rightDerivedZeroIsoSelf
comparisons in the formula. Cancel the resolution augmentations and the exact
single comparisons to obtain the stated equation. No pullback of sections is
inverted; the argument works for empty schemes and arbitrary sheaves. -/
theorem derivedSectionPullback_zero {Y X : Scheme.{v}} (W : Y.Etale)
    (f : X ⟶ W.left) (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (let τ : rightDerivedGlobalSections AddCommGrpCat.{v + 1} W.left ⟶
        D(upperStar AddCommGrpCat.{v + 1} f) ⋙
          rightDerivedGlobalSections AddCommGrpCat.{v + 1} X :=
      Functor.whiskerRight
        (mapDerivedUpperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).unit
        (rightDerivedGlobalSections AddCommGrpCat.{v + 1} W.left) ≫
      Functor.whiskerLeft D(upperStar AddCommGrpCat.{v + 1} f)
        (Functor.rightDerivedFunctorCompIso'
          (lowerStar AddCommGrpCat.{v + 1} f)
          (Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1})
          (Functor.isoWhiskerLeft (lowerStar AddCommGrpCat.{v + 1} f)
              (Sheaf.ΓNatIsoSheafSections W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
                terminalIsTerminal) ≪≫
            lowerStarCompSheafSectionsTerminalIso AddCommGrpCat.{v + 1} f ≪≫
            (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{v + 1}
              terminalIsTerminal).symm)).hom
    let L := upperStar AddCommGrpCat.{v + 1} W.hom
    let Q := upperStar AddCommGrpCat.{v + 1} f
    let R := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{v + 1}
    let b := L.mapDerivedCategory.mapIso
        ((DerivedCategory.Plus.singleFunctorιIso _ 0).app G) ≪≫
      (L.mapDerivedCategorySingleFunctor 0).app G
    let c := Q.mapDerivedCategory.map b.hom ≫
      (Q.mapDerivedCategorySingleFunctor 0).hom.app (L.obj G)
    let z := R.homologyRightDerivedFunctorObjSingleFunctorIso (Q.obj (L.obj G)) 0 ≪≫
      R.rightDerivedZeroIsoSelf.app (Q.obj (L.obj G))
    (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (τ.app
          (L.mapDerivedCategory.obj
            (DerivedCategory.Plus.ι.obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) ≫
      (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0).map
        (R.rightDerivedFunctor.map c) ≫ z.hom =
      (zeroIso W G).hom ≫ globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f (L.obj G)) := by
  extract_lets τ L Q R b c z
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} 0
  let F := Sheaf.Γ W.left.smallEtaleTopology AddCommGrpCat.{v + 1}
  let M := L.obj G
  let zF := F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
    F.rightDerivedZeroIsoSelf.app M
  let s := globalSectionsUpperStarMap AddCommGrpCat.{v + 1} f M
  have hs := derivedSectionPullback_single_unit f M
  change F.rightDerivedSingleUnit M ≫ τ.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
    R.rightDerivedFunctor.map ((Q.mapDerivedCategorySingleFunctor 0).hom.app M) =
    (DerivedCategory.singleFunctor AddCommGrpCat.{v + 1} 0).map s ≫
      R.rightDerivedSingleUnit (Q.obj M) at hs
  have hF := F.rightDerivedSingleUnit_zero M
  have hR := R.rightDerivedSingleUnit_zero (Q.obj M)
  change H.map (F.rightDerivedSingleUnit M) ≫ zF.hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{v + 1} 0).hom.app
      (F.obj M) at hF
  change H.map (R.rightDerivedSingleUnit (Q.obj M)) ≫ z.hom =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{v + 1} 0).hom.app
      (R.obj (Q.obj M)) at hR
  have hs0 := map_zero_comparison H
    (DerivedCategory.singleFunctor AddCommGrpCat.{v + 1} 0)
    (DerivedCategory.singleFunctorCompHomologyFunctorIso AddCommGrpCat.{v + 1} 0)
    zF z (F.rightDerivedSingleUnit M) (R.rightDerivedSingleUnit (Q.obj M))
    (τ.app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
      R.rightDerivedFunctor.map ((Q.mapDerivedCategorySingleFunctor 0).hom.app M))
    s hF hR hs
  simp only [Functor.map_comp, Category.assoc] at hs0
  change H.map (τ.app _) ≫ H.map (R.rightDerivedFunctor.map c) ≫ z.hom =
    (zeroIso W G).hom ≫ s
  dsimp only [c]
  simp only [Functor.map_comp, Category.assoc]
  have hnH := (Functor.whiskerRight τ H).naturality b.hom
  dsimp only [Functor.comp_map, Functor.whiskerRight_app] at hnH
  erw [← reassoc_of% hnH]
  exact (congrArg (fun t ↦ H.map (F.rightDerivedFunctor.map b.hom) ≫ t) hs0).trans
    (Category.assoc (H.map (F.rightDerivedFunctor.map b.hom)) zF.hom s).symm

end AlgebraicGeometry.Etale.RawRestrictedComparison

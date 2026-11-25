/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.InjectiveExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.StrictLocalSectionsUnitLeray

/-! # Derived exchange and Leray before taking homology

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-derived-exchange-leray).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The derived exchange computation on the global sections of the pulled-back
underived direct-image complex. No neighbourhood section restriction occurs.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and the
adjunction factorization in `Adjunction.derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-weil-pbc-strict-local-derived-exchange-leray).

Proof: put M = ιJ and L = f_*M. In the bounded-below homotopy category apply
`Adjunction.derivedPlus_mateEquiv_app_fac` with `squareUpperStarIso`; its square
compatibility is `pullbackSquareComparison_hom_app_factorsh`. Invert the derived
f_* unit at M, which is invertible since M is a bounded-below complex of
injectives. Transport along q and the quotient/localization comparison: the
inverse source identification is exactly `sourceInjectiveDirectImageIso.inv`.
Apply exact global sections on the strict-local base. Expand the Leray
isomorphism. Naturality of the right-derived sections unit and the
factorization of the derived composition isomorphism identify the direct-image
unit at p^*M followed by Leray with the sections unit at p^*M, preceded by the
underived pushforward-sections isomorphism. Transport by p^*q.inv. The result is
the displayed derived-category identity. Only the direct-image unit at
M is inverted; the sections unit at p^*M is retained. Hence the formula does not
require p^*M acyclic, and includes zero complexes. -/
theorem strictLocalDerivedExchange_leray {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s)
    let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let b := Functor.whiskerRight
        (baseChangeMap AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase s)).toCommSq) G ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictLocalizationToBase s)))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictLocalizationToBase s))).hom
    have := strictHenselization_globalSections_preservesFiniteColimits s
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictLocalizationToBase s))
    let Y := pullback f (Scheme.strictLocalizationToBase s)
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictLocalizationToBase s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let T := P.mapDerivedCategoryPlus.obj K
    let V := F.rightDerivedFunctorPlus.obj T
    let ℓ := DerivedCategory.Plus.ι.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app V) ≫
      G.rightDerivedFunctorPlusCompatibility.hom.app V ≫
      G.rightDerivedFunctor.map (F.rightDerivedFunctorPlusCompatibility.hom.app T) ≫
      (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictLocalizationToBase s))).hom.app T.obj
    G.mapDerivedCategoryFactors.inv.app C ≫
      G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.inv.app L ≫
        U.mapDerivedCategory.map (sourceInjectiveDirectImageIso f K J q).inv) ≫
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictLocalizationToBase s)).toCommSq).hom)).app K)) ≫
      ℓ =
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex b (.up ℤ)).app M) ≫
      (DerivedCategory.quotientCompQhIso AddCommGrpCat.{v + 1}).inv.app
        (((Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).mapHomologicalComplex
          (.up ℤ)).obj D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        ((DerivedCategory.quotientCompQhIso _).hom.app D) ≫
      (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{v + 1}).rightDerivedFunctor.map
        (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    dsimp (config := { failIfUnchanged := false }) only
    have := strictHenselization_globalSections_preservesFiniteColimits s
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictLocalizationToBase s)
    let G := Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let P := upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictLocalizationToBase s))
    let F := lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictLocalizationToBase s))
    let D := (P.mapHomologicalComplex (.up ℤ)).obj M
    let a : (U.mapHomologicalComplex (.up ℤ)).obj L ⟶
        (F.mapHomologicalComplex (.up ℤ)).obj D := (NatTrans.mapHomologicalComplex
      (baseChangeMap AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f (Scheme.strictLocalizationToBase s)).toCommSq)
      (.up ℤ)).app M
    have he := congrArg G.mapDerivedCategory.map (injectiveExchange_representative f s K J q)
    simp only [G.mapDerivedCategory.map_comp] at he
    erw [G.mapDerivedCategory.map_comp, Category.assoc]
    erw [reassoc_of% he]
    have hn := G.mapDerivedCategoryFactors.inv.naturality a
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    have hl := strictLocalSections_unit_leray s
      (pullback.snd f (Scheme.strictLocalizationToBase s)) D
      (P.mapDerivedCategoryPlus.obj K)
      (P.mapDerivedCategoryFactors.inv.app M ≫ P.mapDerivedCategory.map q.inv)
    dsimp (config := { failIfUnchanged := false }) only at hl
    have hl' := congrArg
      (fun z ↦ DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map a) ≫ z) hl
    refine hl'.trans ?_
    simp only [← DerivedCategory.Q.map_comp_assoc]
    congr 1
  )

end AlgebraicGeometry.Etale

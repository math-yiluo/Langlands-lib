/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceComparison
public import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalDerivedExchangeLeray

/-! # Derived exchange on global sections before neighbourhood restriction

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-derived-exchange-global-sections).
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalDerivedExchangeGlobalSections.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The derived exchange computation on the global sections of the pulled-back
underived direct-image complex. No neighbourhood section restriction occurs.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and the
adjunction factorization in `Adjunction.derivedPlus_mateEquiv_app_fac`.
(blueprint: lem-weil-pbc-strict-local-derived-exchange-global-sections).

Proof: apply naturality of the exact strict-local sections/homology comparison
isomorphism to the derived mate. Expand smallModel_strictLocalBaseChangeTargetIso and
strictHenselizationLerayHomologyIso. The bounded-below exact homology comparison
is the unbounded comparison at the underlying object, so it cancels its inverse.
Apply degree-n homology to smallModel_strictLocalDerivedExchange_leray. Functoriality of
homology expands the derived-category composite into the displayed factors.
Expand termwiseSectionsToDerived and representativeSectionsComparison to identify
the right-hand side. No sections unit is inverted, so this holds in every degree
and for zero complexes without an acyclicity assumption on the pulled-back complex. -/
theorem smallModel_strictLocalDerivedExchange_globalSections {X S : Scheme.{v}} (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let U := upperStar AddCommGrpCat.{v + 1} (Scheme.strictHenselizationStructuralMap s)
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let C := (U.mapHomologicalComplex (.up ℤ)).obj L
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n
    let b := Functor.whiskerRight
        (baseChangeMap AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq) G ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    H.map (G.mapDerivedCategoryFactors.inv.app C ≫
      G.mapDerivedCategory.map (U.mapDerivedCategoryFactors.inv.app L ≫
        U.mapDerivedCategory.map (smallModel_sourceInjectiveDirectImageIso f K J q).inv)) ≫
      (G.mapDerivedCategoryHomologyFunctorIso n).inv.app
        (U.mapDerivedCategory.obj
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K).obj) ≫
      G.map ((DerivedCategory.Plus.homologyFunctor _ n).map
        ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
          (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
            (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
          (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
            (IsPullback.of_hasPullback f
              (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).app K)) ≫
      (smallModel_strictLocalBaseChangeTargetIso f s K n).hom =
    H.map (DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex b (.up ℤ)).app M)) ≫
      representativeSectionsComparison
        (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    dsimp only
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let m := (mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
        (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
      (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
        (IsPullback.of_hasPullback f
          (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom)).app K
    have hn := (G.mapDerivedCategoryHomologyFunctorIso n).inv.naturality
      (DerivedCategory.Plus.ι.map m)
    dsimp only [Functor.comp_map] at hn
    change _ ≫ _ ≫ G.map ((DerivedCategory.homologyFunctor _ n).map
      (DerivedCategory.Plus.ι.map m)) ≫ _ = _
    unfold smallModel_strictLocalBaseChangeTargetIso exactGlobalSectionsLerayHomologyIso
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    erw [← reassoc_of% hn]
    let T := (upperStar AddCommGrpCat.{v + 1}
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s))).mapDerivedCategoryPlus.obj K
    let V := (lowerStar AddCommGrpCat.{v + 1}
      (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).rightDerivedFunctorPlus.obj T
    have he : ((G.mapDerivedCategoryPlusHomologyFunctorIso n).app V).hom =
        (G.mapDerivedCategoryHomologyFunctorIso n).hom.app V.obj := by
      simp only [Functor.comp_obj, Iso.app_hom]
      change 𝟙 _ ≫ (G.mapDerivedCategoryHomologyFunctorIso n).hom.app V.obj ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map
          (𝟙 (G.mapDerivedCategory.obj V.obj)) = _
      rw [(DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map_id]
      rw [Category.id_comp]
      exact Category.comp_id _
    erw [he, Iso.inv_hom_id_app_assoc]
    simp only [representativeSectionsComparison, termwiseSectionsToDerived,
      cohomology, rightDerivedGlobalSections, Functor.comp_map,
      ← Functor.map_comp, Category.assoc]
    convert congrArg ((DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n).map)
      (smallModel_strictLocalDerivedExchange_leray f s K J q) using 1 <;>
      simp only [Functor.map_comp, Category.assoc, Iso.app_hom, Iso.symm_hom,
        DerivedCategory.Plus.homologyFunctor, Functor.comp_map, m, G,
        rightDerivedGlobalSections] <;> rfl
  )

end AlgebraicGeometry.Etale

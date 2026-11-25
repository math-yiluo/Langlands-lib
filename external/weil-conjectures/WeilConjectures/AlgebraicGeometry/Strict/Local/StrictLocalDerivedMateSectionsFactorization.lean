/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Strict.Henselization.StrictHenselizationSchemeSectionsExact
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalUnderivedSectionsMate
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalDerivedExchangeGlobalSections

/-! # The derived mate on the complex of neighbourhood sections

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalDerivedMateSectionsFactorization.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The derived mate on an injective representative is computed by the underived
exchange map followed by the derived-sections unit. This statement does not identify
that exchange map with restriction along any strict-local neighbourhood cone.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph, and the generic
factorization of derived adjunction mates on complexes.
(blueprint: lem-weil-pbc-strict-local-derived-mate-sections-factorization).

Proof: put M = ιJ, L = f_*M. Pass first to the homotopy category. Apply
Adjunction.derivedPlus_mateEquiv_app_fac to the two inverse/direct-image
adjunctions and squareUpperStarIso. The compatibility hypothesis on the square
follows by expanding pullbackSquareComparison and the localization factorization
of upperStarComp. The right-derived unit at M is invertible because M is a bounded
below complex of injectives. Its inverse is precisely the factor used in
smallModel_sourceInjectiveDirectImageIso. Move restriction of L across this identity by
naturality of the right-derived units. Apply global sections on the strict-local
base. Their exactness identifies homology of sections with sections of homology;
the derived Leray factorization converts the direct-image unit at p^*M into the
right-derived sections unit at p^*M. The remaining underived maps are restriction
on the base, baseChangeMap, and lowerStarCompGlobalSectionsIso, in that order:
this is smallModel_strictLocalUnderivedMateSections. Apply localization and degree-n homology,
using naturality of homologyFunctorFactors and the exact-sections homology
comparison. Transport by q using naturality. This yields the stated equality.
Only the direct-image unit at M is inverted; the sections unit at p^*M is retained.
Thus no acyclicity of p^*M is asserted or needed, and negative degrees and zero
complexes are included. -/
theorem smallModel_strictLocalComplexSectionRestriction_derivedMate {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    smallModel_strictLocalComplexSectionRestriction s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) L
      (smallModel_sourceInjectiveDirectImageIso f K J q) n i ≫
        ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.app K))) ≫
        (smallModel_strictLocalBaseChangeTargetIso f s K n).hom =
    (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map
      ((NatTrans.mapHomologicalComplex (smallModel_strictLocalUnderivedMateSections f s i)
        (.up ℤ)).app M) ≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    representativeSectionsComparison
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
  set_option backward.defeqAttrib.useBackward true in
  exact (by
    intro i
    have := strictHenselizationScheme_globalSections_preservesFiniteColimits s
    let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
    let L := ((lowerStar AddCommGrpCat.{v + 1} f).mapHomologicalComplex (.up ℤ)).obj M
    let G := Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
      AddCommGrpCat.{v + 1}
    let a := (NatTrans.mapHomologicalComplex (smallModel_strictLocalSectionRestrictionNat s i)
      (.up ℤ)).app L
    let b := Functor.whiskerRight
        (baseChangeMap AddCommGrpCat.{v + 1}
          (IsPullback.of_hasPullback f (Scheme.strictHenselizationStructuralMap s)).toCommSq) G ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft
        (upperStar AddCommGrpCat.{v + 1}
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)))
        (lowerStarCompGlobalSectionsIso AddCommGrpCat.{v + 1}
          (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).hom
    have hchain : (NatTrans.mapHomologicalComplex
        (smallModel_strictLocalUnderivedMateSections f s i)
        (.up ℤ)).app M = a ≫ (NatTrans.mapHomologicalComplex b (.up ℤ)).app M := by
      ext k
      simp [smallModel_strictLocalUnderivedMateSections, a, b, M, L, G]
    let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v + 1} n
    let A := ((sheafSections S.smallEtaleTopology AddCommGrpCat.{v + 1}).obj
      (op ((strictLocalNeighbourhoods s).obj i))).mapHomologicalComplex (.up ℤ)
    let c := representativeSectionsComparison
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n
    let e := (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app
      (A.obj L)
    have hcore := smallModel_strictLocalDerivedExchange_globalSections f s K n J q
    have hh := congrArg (fun z ↦ e ≫ H.map (DerivedCategory.Q.map a) ≫ z) hcore
    unfold smallModel_strictLocalComplexSectionRestriction
    dsimp only
    calc
      _ = e ≫ H.map (DerivedCategory.Q.map a) ≫
          H.map (DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex b (.up ℤ)).app M)) ≫ c := by
        convert hh using 1
        · simp only [Functor.map_comp, Category.assoc]
          rfl
      _ = _ := by
        rw [hchain]
        have hn :=
          (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.naturality
          (a ≫ (NatTrans.mapHomologicalComplex b (.up ℤ)).app M)
        dsimp only [Functor.comp_map] at hn
        convert congrArg (fun z ↦ z ≫ c) hn.symm using 1 <;>
          simp only [Functor.map_comp, Category.assoc] <;> rfl
  )

end AlgebraicGeometry.Etale

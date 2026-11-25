/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.MateProjectionData
public import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalLocalizedHomGerm
public import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalUnderivedSectionsMate
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalDerivedMateSectionsFactorization

/-! # The derived mate on the complex of neighbourhood sections

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
-/

/- This original-model counterpart follows the proved calculation in
WeilConjectures.AlgebraicGeometry.StrictLocalComplexSectionsMate.
The spectrum and structure morphism are those of the small coordinate-ring colimit. -/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

-- Comparing the composed section functors across localization requires extra defeq work.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The derived mate, on restricted sections of the direct-image representative,
is the canonical comparison of termwise restriction to fibre hypercohomology.
This statement starts with cohomology of the complex of sections on S: it contains
neither localized Hom classes nor their canonical germ map.

Source: Stacks Project, Tag 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-complex-sections-mate).

Proof: let M be the complex underlying J and L = f_*M. The invertible right-derived
unit on M gives smallModel_sourceInjectiveDirectImageIso. In the homotopy category expand the
mate into the adjunction unit along f, the pullback-square comparison, and the
counit along the base-changed f. The defining compatibility of the derived
adjunction with the underived adjunction identifies its value on M with the
underived mate followed by the right-derived direct-image unit on p^*M.
Naturality of the right-derived units moves the restriction of L's sections through
this composite. The strict-local exact-sections comparison and the derived Leray
factorization identify its result with the sections unit on p^*M. At the underived
level evaluate f_*M on the pointed neighbourhood, using smallModel_sourceStageSectionsIso.
The unit, square comparison, and counit send a section to its restriction on the
pullback. Q.smallModelFirst identifies the base component of this map with the specified
strict-henselization leg; Q.smallModelOver identifies the projection to X. These are the
components defining termwiseSectionsRestriction. Apply localization and H^n;
naturality of the homology and exact-sections comparisons gives the displayed
square. Finally transport by q. Only the right-derived unit on M is inverted;
no injectivity or acyclicity of p^*M is assumed. Zero complexes, negative degrees,
and nonetale cone legs use the same naturality and triangle identities. -/
theorem smallModel_strictLocalComplexSectionRestriction_mate {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
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
      ((NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i) (.up ℤ)).hom.app M) ≫
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.app _ ≫
    termwiseSectionsRestriction (Q.smallModelLegs.app i)
      ((strictLocalNeighbourhoodProjection f s).app i)
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm M n ≫
    representativeSectionsComparison
      (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n := by
  intro i
  dsimp only
  rw [smallModel_strictLocalComplexSectionRestriction_derivedMate f s K n J q i]
  let M := ((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj
  let a := (NatIso.mapHomologicalComplex (smallModel_sourceStageSectionsIso f s i)
    (.up ℤ)).hom.app M
  let b := (NatTrans.mapHomologicalComplex (sectionsPullbackNat (Q.smallModelLegs.app i))
      (.up ℤ)).app
      (((upperStar AddCommGrpCat.{v + 1}
        ((strictLocalNeighbourhoodProjection f s).app i)).mapHomologicalComplex
          (.up ℤ)).obj M) ≫
    ((Sheaf.Γ (pullback f (Scheme.strictHenselizationStructuralMap s)).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1} (Q.smallModelLegs.app i)
            ((strictLocalNeighbourhoodProjection f s).app i)
            (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) (Q.smallModelOver i).symm)
          (.up ℤ)).inv.app M)
  have hb : (NatTrans.mapHomologicalComplex (smallModel_strictLocalUnderivedMateSections f s i)
      (.up ℤ)).app M = a ≫ b := by
    rw [smallModel_strictLocalUnderivedMateSections_eq f s Q i]
    ext k
    simp [a, b]
  rw [hb, Functor.map_comp, Category.assoc]
  have hn :=
    (DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n).inv.naturality b
  change _ ≫ _ = _ ≫ _ at hn
  dsimp only [Functor.comp_map] at hn
  simpa only [a, b, M, termwiseSectionsRestriction, Category.assoc] using!
    congrArg (fun t ↦
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n).map a ≫
        t ≫ representativeSectionsComparison
          (pullback.fst f (Scheme.strictHenselizationStructuralMap s)) q n) hn

end AlgebraicGeometry.Etale

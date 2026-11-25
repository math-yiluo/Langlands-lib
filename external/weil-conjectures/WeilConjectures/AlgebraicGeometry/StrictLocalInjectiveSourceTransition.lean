/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.SourceDerivedSectionsNaturality
import WeilConjectures.AlgebraicGeometry.SourceStageSectionsNaturality
import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-transition).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The canonical cycle comparison commutes with neighbourhood restriction.
Source: Stacks Project, Tag 03Q8, computation of direct images by injective complexes;
Tag 03Q9, restrictions of the complex of sections.
(blueprint: lem-weil-pbc-strict-local-injective-source-transition).

Proof: write M for the complex underlying J and L for f_*M. The right-derived unit
on M is natural and invertible. Under its comparison with Rf_*K, precomposition by
the free sheaf of a neighbourhood map is precomposition in HomComplex(Z[V][0], L).
The localization bijection on Hom into the K-injective complex L commutes with
this precomposition: apply Qh to the corresponding chain maps and use functoriality.
Evaluation of the free generator commutes with the neighbourhood map by Yoneda
naturality. Hence the induced map on the complex of sections is L's restriction
map. Direct image evaluates this as restriction on the base-changed neighbourhood.
The localization-restriction comparison for each etale projection is the unique
comparison of two left adjoints to the same direct image; its unit compatibility
identifies this map with sectionsPullbackNat followed by upperStarComp.inv.
This is exactly the chain map defining termwiseSectionsRestriction. Naturality of
the Hom-complex homology isomorphism and of homologyFunctorFactors gives the stated
square. Transport by q is natural and therefore preserves it. No cone leg or mate
is involved. Identity transitions reduce to identity chain maps; zero complexes
and all integer degrees use the same computation. -/
theorem strictLocalInjectiveSourceIso_transition {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op ≫
          (strictLocalInjectiveSourceIso f s K n J q i).hom =
          (strictLocalInjectiveSourceIso f s K n J q j).hom ≫
            termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
              ((strictLocalNeighbourhoodProjection f s).app j)
              ((strictLocalNeighbourhoodProjection f s).app i)
              ((Category.comp_id _).symm.trans
                ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
              (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n := by
  intro i j a
  let M := (InjectiveObject.ι _).mapCochainComplexPlus.obj J
  let F := lowerStar AddCommGrpCat.{v + 1} f
  let L := F.mapCochainComplexPlus.obj M
  have : F.PreservesInjectiveObjects :=
    Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
      (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f)
  have (k : ℤ) : Injective (L.obj.X k) :=
    F.injective_obj ((InjectiveObject.ι _).obj (J.obj.X k))
  have : L.obj.IsKInjective := by
    obtain ⟨b, hb⟩ := L.property
    let : L.obj.IsStrictlyGE b := hb
    exact CochainComplex.isKInjective_of_injective L.obj b
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{v + 1} (.up ℤ) n
  let E := fun i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s) ↦
    sourcePlusHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj
      ((strictLocalNeighbourhoods s).obj i))
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) L.obj
      (sourceInjectiveDirectImageIso f K J q) n ≪≫
    (sourceClassDerivedHomIso ((strictLocalFreeSheaf S.smallEtaleTopology).obj
      ((strictLocalNeighbourhoods s).obj i)) L.obj n).symm ≪≫
    (CochainComplex.HomComplex.leftHomologyData
      ((CochainComplex.singleFunctor _ 0).obj ((strictLocalFreeSheaf S.smallEtaleTopology).obj
        ((strictLocalNeighbourhoods s).obj i))) L.obj n).homologyIso.symm ≪≫
    H.mapIso (sourceFreeSectionsComplexIso ((strictLocalNeighbourhoods s).obj i) L.obj)
  let P := fun i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s) ↦
    (NatIso.mapHomologicalComplex (sourceStageSectionsIso f s i) (.up ℤ)).hom.app M.obj
  let B := DerivedCategory.homologyFunctorFactors AddCommGrpCat.{v + 1} n
  have h₁ := sourceDerivedSections_naturality
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) L.obj
    (sourceInjectiveDirectImageIso f K J q) n ((strictLocalNeighbourhoods s).map a)
  have h₂ := sourceStageSectionsIso_naturality f s a M.obj
  change AddCommGrpCat.ofHom (Preadditive.leftComp
      (((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K)⟦n⟧)
      ((DerivedCategory.Plus.singleFunctor _ 0).map
        ((strictLocalFreeSheaf S.smallEtaleTopology).map
          ((strictLocalNeighbourhoods s).map a)))) ≫
      (E i).hom ≫ H.map (P i) ≫ B.inv.app _ =
    (E j).hom ≫ H.map (P j) ≫ B.inv.app _ ≫
      termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
        ((strictLocalNeighbourhoodProjection f s).app j)
        ((strictLocalNeighbourhoodProjection f s).app i)
        ((Category.comp_id _).symm.trans
          ((strictLocalNeighbourhoodProjection f s).naturality a).symm) M.obj n
  change _ ≫ (E i).hom = (E j).hom ≫ _ at h₁
  rw [reassoc_of% h₁]
  simp only [termwiseSectionsRestriction]
  have h₂' := congrArg (fun g ↦ H.map g) h₂
  simp only [Functor.map_comp] at h₂'
  change H.map _ ≫ H.map (P i) = H.map (P j) ≫ _ at h₂'
  erw [reassoc_of% h₂']
  let R := (NatTrans.mapHomologicalComplex
    (sectionsPullbackNat ((strictLocalNeighbourhoodDiagram f s).map a)) (.up ℤ)).app
      (((upperStar AddCommGrpCat.{v + 1}
        ((strictLocalNeighbourhoodProjection f s).app j)).mapHomologicalComplex
          (.up ℤ)).obj M.obj) ≫
    ((Sheaf.Γ ((strictLocalNeighbourhoodDiagram f s).obj i).smallEtaleTopology
      AddCommGrpCat.{v + 1}).mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex
          (upperStarComp AddCommGrpCat.{v + 1}
            ((strictLocalNeighbourhoodDiagram f s).map a)
            ((strictLocalNeighbourhoodProjection f s).app j)
            ((strictLocalNeighbourhoodProjection f s).app i)
            ((Category.comp_id _).symm.trans
              ((strictLocalNeighbourhoodProjection f s).naturality a).symm))
          (.up ℤ)).inv.app M.obj)
  have h₃ := B.inv.naturality R
  dsimp only [R, Functor.comp_map] at h₃
  simp only [Functor.map_comp, Category.assoc] at h₃
  erw [h₃]
  simp only [Functor.map_comp]
  rfl

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceTransition
import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceRestriction
import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologyGerms
import WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionData
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-sections).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Source derived Hom, neighbourhood restriction, and the sections map of the mate
computed on a specified bounded-below complex of injectives. The intermediate groups
are homology of actual termwise sections, not stage hypercohomology. At the limit
only the canonical map to derived sections is used; it need not be invertible.
Source: Stacks, Tags 03Q8 and 03Q9, final injective-complex paragraph
(blueprint: lem-weil-pbc-strict-local-injective-source-sections).

Proof: identify Rf_*K with f_*J using the right-derived unit on the injective
representative and the supplied q. Derived adjunction identifies a morphism from
Z[V][0] with a morphism from f^*Z[V][0] to J[n]. The free-sheaf sections adjunction
identifies the Hom complex with the complex of sections of J on V times_S X.
The restricted complex is injective, since its projection to X is etale. Thus
passing to homology gives the component isomorphisms e. Precomposition by an etale
neighbourhood map is restriction of those same sections, and composition of inverse
images gives the displayed transition. For a cone leg, evaluate the derived mate
on J using its construction by the two adjunction units and the pullback-square
comparison. It sends a section on V times_S X to its inverse image on the limit.
The canonical derived Hom-to-homology germ map takes that section to its homology
class; the first leg equation of Q identifies its geometric germ with this inverse
image. Exact inverse image commutes with homology, while exact strict-local
sections and Leray give strictLocalBaseChangeTargetIso. The comparison from the
complex of sections at the limit to its derived sections is precisely the
right-derived sections unit, even if the pulled-back J is not injective there.
This proves the restriction formula. Naturality with q identifies all maps with
those for K. Neither continuity nor invertibility of the mate is used. The
argument works in all integer degrees and for the zero complex. -/
theorem exists_strictLocalInjectiveSourceSections {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∃ e : ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
      (strictLocalCohomologyNeighbourhoodFunctor s
        ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).obj (op i) ≅
        termwiseSectionsCohomology ((strictLocalNeighbourhoodDiagram f s).obj i)
          (((upperStar AddCommGrpCat.{v + 1}
            ((strictLocalNeighbourhoodProjection f s).app i)).mapHomologicalComplex
              (.up ℤ)).obj
                (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) n,
      (∀ {i j : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)} (a : i ⟶ j),
        (strictLocalCohomologyNeighbourhoodFunctor s
          ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).map a.op =
          (e j).hom ≫
            termwiseSectionsRestriction ((strictLocalNeighbourhoodDiagram f s).map a)
              ((strictLocalNeighbourhoodProjection f s).app j)
              ((strictLocalNeighbourhoodProjection f s).app i)
              ((Category.comp_id _).symm.trans
                ((strictLocalNeighbourhoodProjection f s).naturality a).symm)
              (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
            (e i).inv) ∧
      (∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
        ((strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n).app (op i)) ≫
        ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K))) =
            (e i).hom ≫
              termwiseSectionsRestriction (Q.legs.app i)
                ((strictLocalNeighbourhoodProjection f s).app i)
                (pullback.fst f (Scheme.strictLocalizationToBase s))
                (Q.over i).symm
                (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
              representativeSectionsComparison
                (pullback.fst f (Scheme.strictLocalizationToBase s)) q n ≫
              (strictLocalBaseChangeTargetIso f s K n).inv)  := by
  let e := strictLocalInjectiveSourceIso f s K n J q
  refine ⟨e, ?_, ?_⟩
  · intro i j a
    apply (cancel_mono (e i).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    exact strictLocalInjectiveSourceIso_transition f s K n J q a
  · exact strictLocalInjectiveSourceIso_restriction f s K n Q J q

end AlgebraicGeometry.Etale

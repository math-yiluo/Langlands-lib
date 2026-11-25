/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceComparison
import WeilConjectures.AlgebraicGeometry.StrictLocalInjectiveSourceDerivedRestriction

/-! # Computing source derived sections on an injective representative

Source: Stacks Project, Tags 03Q8 and 03Q9, final injective-complex paragraph.
(blueprint: lem-weil-pbc-strict-local-injective-source-restriction).
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- The canonical cycle comparison identifies the strict-local derived mate with
restriction along the fixed geometric cone leg.
Source: Stacks Project, Tag 03Q9, final injective-complex paragraph; Tag 03Q8.
(blueprint: lem-weil-pbc-strict-local-injective-source-restriction).

Proof: compute the source direct image on the fixed bounded-below injective complex
J using the right-derived unit. Represent each source morphism by a Hom-complex
cocycle; localization into f_*J is bijective because f_*J is K-injective. The
canonical comparison evaluates that cocycle at the free generator. Applying the
degree-zero homology germ map before this evaluation gives its homology class,
with the shift isomorphism putting it in degree n. The defining germ-leg equation
for the unique strict-henselization stalk restriction takes this class to its
inverse-image restriction on the strict-local pullback. Q.first and Q.over fix
both projections of that restriction and identify it with Q.legs.app i.
On the injective representative, the derived adjunction unit and counit are the
classes of their termwise units and counits. Expand mateEquiv and the pullback
comparison. The adjunction triangle identities cancel the intermediate unit and
counit; its sections map is therefore sectionsPullbackNat along the cone leg,
followed by upperStarComp.inv. Taking homology gives termwiseSectionsRestriction.
At the limit the derived-sections unit is retained, rather than inverted, which
is exactly representativeSectionsComparison after transport by q. Exact inverse
image commutes with homology. Exact strict-local sections and the Leray comparison
identify the target by strictLocalBaseChangeTargetIso. These identifications give
the displayed equation after its inverse. Naturality transports every step from
J to K. This argument uses neither continuity nor injectivity of the limit
pullback of J; negative degrees and zero complexes are covered without alteration. -/
theorem strictLocalInjectiveSourceIso_restriction {X S : Scheme.{v}}
    (f : X ⟶ S)
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) (Q : StrictLocalNeighbourhoodGeometry f s)
    (J : CochainComplex.Plus (InjectiveObject
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1})))
    (q : K.obj ≅ DerivedCategory.Q.obj
      (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj)) :
    ∀ i : SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s),
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
            (strictLocalInjectiveSourceIso f s K n J q i).hom ≫
              termwiseSectionsRestriction (Q.legs.app i)
                ((strictLocalNeighbourhoodProjection f s).app i)
                (pullback.fst f (Scheme.strictLocalizationToBase s))
                (Q.over i).symm
                (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) n ≫
              representativeSectionsComparison
                (pullback.fst f (Scheme.strictLocalizationToBase s)) q n ≫
              (strictLocalBaseChangeTargetIso f s K n).inv := by
  intro i
  apply (cancel_mono (strictLocalBaseChangeTargetIso f s K n).hom).1
  rw [Category.assoc]
  rw [strictLocalInjectiveSourceIso_derivedRestriction f s K n Q J q i]
  have h := (injectiveSections_strictLocal_comparison f s K n Q J q).2.2 i
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    congrArg (fun a ↦ (strictLocalInjectiveSourceIso f s K n J q i).hom ≫ a) h

end AlgebraicGeometry.Etale

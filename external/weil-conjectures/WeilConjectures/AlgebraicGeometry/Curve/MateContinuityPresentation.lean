/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.MorphismDefs
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometry.NeighbourhoodGeometry
import WeilConjectures.AlgebraicGeometry.Curve.CohomologyGerms
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalCohomologySourceColimit
import WeilConjectures.AlgebraicGeometry.Strict.Local.StrictLocalInjectiveSourceSections
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives

/-! # Projection-restriction presentation on the small strict-local model

This theorem uses `strictHenselizationScheme` and `strictHenselizationStructuralMap`.
The adopted theorem with the unprefixed name uses `strictLocalization` instead.

Source: Stacks Project, Tag 03Q9, the neighbourhood-colimit construction and the
injective-complex restriction maps in its final proof paragraph.
-/

@[expose] public section

universe v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Present the source of the strict-local mate as neighbourhood hypercohomology,
and identify its germ components with projection pullbacks to the limit.
This supplies the input to derived continuity, without applying continuity and without
asserting that either the target cocone is a colimit or the mate is invertible.
Source: Stacks Project, Tag 03Q9, proof paragraphs 1 and 3; Tag 03Q8
(blueprint: lem-weil-pbc-strict-local-mate-continuity-presentation).

Proof: use the small representative category of affine pointed neighbourhoods of s.
It is cofiltered by strictHenselization_properties. Base change its diagram along f,
with limit the pullback of the strict henselization; the fibre-product limit theorem
and the characterisation of the structural map identify its cone legs. Its stages
are qcqs since the neighbourhoods are affine and f is qcqs; transitions are affine
since morphisms between affine schemes and their base changes are affine.
Take the diagram F of neighbourhood hypercohomology of the inverse images of K.
Choose a bounded-below injective representative J of K. Restriction along the etale
stage projections preserves injectives, so sections of J compute these groups, and
restriction of sections gives exactly the transition formula in the presentation.
By 03Q8 and invariance of geometric stalks under sheafification, the stalk of H^n Rf_*K
is the colimit of F. The canonical germ restriction is an isomorphism; exact inverse
image commutes with homology. Transport the stalk cocone through these two isomorphisms
to obtain sourceLegs and sourceIsColimit, with vertex the displayed source group.
Exact strict-local global sections and the Leray homology isomorphism identify the
displayed target with hypercohomology of the limit, giving limitIso. On J the
adjunction mate is restriction of sections along the pullback square. Thus each
source germ, followed by the mate and limitIso, is the projection pullback on
hypercohomology. This is precisely the restriction equation of the presentation.
This construction uses no continuity assertion and no isomorphism assertion for the mate.
It applies in negative degrees as well as positive degrees, and to the zero complex;
qcqs is used for the stages, not imposed on S or X separately. -/
theorem smallModel_nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictHenselizationScheme s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictHenselizationStructuralMap s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictHenselizationStructuralMap s)).toCommSq).hom))
                |>.app K)))) := by
  classical
  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
  obtain ⟨E⟩ : Nonempty (SmallModelStrictLocalMateProjectionData f s K n Q) := by
    obtain ⟨b, hb⟩ := K.property
    let : K.IsGE b := (K.isGE_ι_obj_iff b).1 hb
    obtain ⟨J, _, ⟨qJ⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K b
    let q : K.obj ≅ DerivedCategory.Q.obj
        (((InjectiveObject.ι _).mapHomologicalComplex (.up ℤ)).obj J.obj) :=
      DerivedCategory.Plus.ι.mapIso qJ.symm
    obtain ⟨e, ht, hr⟩ := smallModel_exists_strictLocalInjectiveSourceSections f s K n Q J q
    obtain ⟨he, htransition, hrestriction⟩ :=
      smallModel_injectiveSections_strictLocal_comparison f s K n Q J q
    let := he
    let E := fun i ↦ e i ≪≫ asIso (representativeSectionsComparison
      ((strictLocalNeighbourhoodProjection f s).app i) q n)
    refine ⟨{ e := E, transition := ?_, restriction := ?_ }⟩
    · intro i j a
      have h := htransition a
      refine (ht a).trans ?_
      dsimp only [E]
      simp only [Iso.trans_hom, Iso.trans_inv, asIso_hom, asIso_inv] at h ⊢
      simp only [Category.assoc] at h ⊢
      rw [reassoc_of% h]
      simp only [IsIso.hom_inv_id_assoc]
    · intro i
      have h := hrestriction i
      refine (hr i).trans ?_
      dsimp only [E]
      simp only [Iso.trans_hom, Iso.trans_inv, asIso_hom] at h ⊢
      simp only [Category.assoc] at h ⊢
      rw [reassoc_of% h]
  let := (Scheme.strictHenselization_properties s).2.1
  obtain ⟨hsource⟩ := smallModel_isColimit_strictLocalCohomologySourceLegs s
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
  let : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.compact
  let : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.quasiSeparated
  let : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a) := Q.affine
  refine ⟨{
    I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
    D := strictLocalNeighbourhoodDiagram f s
    c := Cone.mk _ Q.smallModelLegs
    isLimit := Q.smallModelIsLimit
    t := strictLocalNeighbourhoodProjection f s
    p := pullback.fst f (Scheme.strictHenselizationStructuralMap s)
    «over» := Q.smallModelOver
    F := strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    e := E.e
    transition := E.transition
    sourceLegs := smallModel_strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    sourceIsColimit := hsource
    limitIso := smallModel_strictLocalBaseChangeTargetIso f s K n
    restriction := fun i ↦ E.restriction i }⟩

end AlgebraicGeometry.Etale

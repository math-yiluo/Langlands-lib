/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.StrictHenselizationRestriction
public import WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
import WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import WeilConjectures.AlgebraicGeometry.StrictLocalCohomologySourceColimit
import WeilConjectures.AlgebraicGeometry.StrictLocalMateProjectionFormulas

/-! # Presenting the strict-local mate as projection restriction

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
It is cofiltered by strictHenselizationAffineProperties. Base change its diagram along f,
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
theorem nonempty_strictLocalBaseChange_continuityPresentation
    {X S : Scheme.{v}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {Ω : Type v} [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{v + 1}))
    (n : ℤ) :
    Nonempty (GlobalCohomologyContinuityPresentation X K n
      ((Sheaf.Γ (Scheme.strictLocalization s).smallEtaleTopology
        AddCommGrpCat.{v + 1}).map
        ((DerivedCategory.Plus.homologyFunctor _ n).map
          ((mateEquiv (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1} f).derivedPlus
            (upperStarLowerStarAdjunction AddCommGrpCat.{v + 1}
              (pullback.snd f (Scheme.strictLocalizationToBase s))).derivedPlus
            (TwoSquare.mk _ _ _ _ (pullbackSquareComparison AddCommGrpCat.{v + 1}
              (IsPullback.of_hasPullback f
                (Scheme.strictLocalizationToBase s)).toCommSq).hom))
                |>.app K)))) := by
  classical
  obtain ⟨Q⟩ := nonempty_strictLocalNeighbourhoodGeometry f s
  obtain ⟨E⟩ := nonempty_strictLocalMateProjectionData f s K n Q
  let := (Scheme.strictHenselizationAffineProperties s).2.1
  obtain ⟨hsource⟩ := isColimit_strictLocalCohomologySourceLegs s
    ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
  let : ∀ i, CompactSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.compact
  let : ∀ i, QuasiSeparatedSpace ((strictLocalNeighbourhoodDiagram f s).obj i) := Q.quasiSeparated
  let : ∀ {i j} (a : i ⟶ j), IsAffineHom ((strictLocalNeighbourhoodDiagram f s).map a) := Q.affine
  refine ⟨{
    I := SmallModel.{v} (Scheme.strictHenselizationNeighbourhoods s)
    D := strictLocalNeighbourhoodDiagram f s
    c := Cone.mk _ Q.legs
    isLimit := Q.isLimit
    t := strictLocalNeighbourhoodProjection f s
    p := pullback.fst f (Scheme.strictLocalizationToBase s)
    «over» := Q.over
    F := strictLocalCohomologyNeighbourhoodFunctor s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    e := E.e
    transition := E.transition
    sourceLegs := strictLocalCohomologySourceLegs s
      ((rightDerivedLowerStarPlus AddCommGrpCat.{v + 1} f).obj K) n
    sourceIsColimit := hsource
    limitIso := strictLocalBaseChangeTargetIso f s K n
    restriction := fun i ↦ E.restriction i }⟩

end AlgebraicGeometry.Etale

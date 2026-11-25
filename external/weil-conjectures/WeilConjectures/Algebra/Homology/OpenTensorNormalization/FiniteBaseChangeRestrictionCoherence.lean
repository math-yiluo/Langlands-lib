/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionLocalization
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.FiniteBaseChangeRestrictionRepresentative
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Finite base-change restriction coherence

(blueprint: lem-sf-finite-base-change-restriction-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- Restriction and pullback commute with the pinned finite realizations.
This is a comparison of pullback squares only; it does not involve an extension
by zero or an asserted base-change arrow.

Source: Stacks 03S6 and the sectionwise square in the proof of
lem-sf-finite-compatibility-transport.
Proof: the first-projection condition on the site square identifies its inverse
with the canonical pullback/map comparison, by the pullback universal property.
Apply the underlying-section comparisons to the ordinary right-adjoint square.
The two pull pins' right-section equations and the two open pins' section
equations identify both routes sectionwise. Faithfulness identifies these
ordinary transformations. Taking mates with the pinned pull adjunctions gives
the corresponding square of ordinary left pullbacks. On a resolving complex,
the pull model equations, the exact open model equations, and theta_model
identify the localized square with the displayed one. Left-derived uniqueness
and localization in the source identify the transformations on all objects.
(blueprint: lem-sf-finite-base-change-restriction-coherence) -/
theorem finite_base_change_restriction_coherence
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    ∀ M : FiniteD A X,
      e.pullU.hom.app ((finitePull A j).obj M) ≫
        o.gUPull.derived.map (r.hom.app M) ≫ o.theta.inv.app (e.realizeX.derived.obj M) =
      e.realizeU'.derived.map
          ((Functor.mapDerivedCategorySquareIso
            (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
        e.openPull'.hom.app ((finitePull A g).obj M) ≫
        o.opens.jStar'.map (e.pull.hom.app M) := by
  apply finite_base_change_restriction_of_representatives A gU j' j g sq o e
  intro P hP
  exact finite_base_change_restriction_representative A gU j' j g sq o e P hP

end SheafOfModules.OpenTensorNormalization

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.OpenTensorNormalization.FiniteBaseChangeRestrictionMateTransport
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.OpenTensorNormalization.FiniteBaseChangeRestrictionRightSquare

/-! The sectionwise ordinary mate identity for the finite restriction square.
(blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate)
-/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

/-- The ordinary restriction square commutes with all four finite comparison pins.

Source: the ordinary representative calculation in
`literature/blueprint/latest/blueprint/sec-six-functors/sk-thm-sf-compatibility/
fix-prop-coherence.proof.md`.
Proof: identify the inverse site-square map with the canonical pullback comparison
using its first projection and its structure map to X'. The two pull pins'
right-section equations and the two open pins' section equations then identify
both routes of the right-adjoint square on each section. Faithfulness of the
underlying sheaf functors gives equality of the square maps. Take mates under
the two finite pull adjunctions and the two ringed pull adjunctions, using
`FinitePullPin.mate` and `Operations.ordinaryTheta_mate`. The ordinary
fixed-scalar square has mate `upperStarCompIso`; this gives the displayed
identity between the four pinned left-adjoint comparisons.
(blueprint: lem-sf-finite-base-change-restriction-ordinary-pin-mate) -/
theorem finite_base_change_restriction_ordinary_pin_mate
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o) (N : FiniteModules A X) :
    e.pullU_pin.ordinary.hom.app
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) j).obj N) ≫
      o.gUPull.ordinary.map (e.open_pin.star.hom.app N) ≫
      o.ordinaryTheta.inv.app (e.realizeX.equivalence.functor.obj N) =
    e.realizeU'.equivalence.functor.map
        ((ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w).hom.app N) ≫
      e.open'_pin.star.hom.app ((ProEtale.upperStar (ModuleCat.{u + 1} A) g).obj N) ≫
      (restrict .ordinary j' (finiteInput A gU j' j g sq).S).map
        (e.pull_pin.ordinary.hom.app N) := by
  apply finite_base_change_restriction_mate_transport A gU j' j g sq o e N
  exact finite_base_change_restriction_right_square A gU j' j g sq o e

end SheafOfModules.OpenTensorNormalization

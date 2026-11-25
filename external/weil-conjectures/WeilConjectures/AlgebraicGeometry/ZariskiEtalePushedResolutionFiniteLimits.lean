/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleInclusionMorphismOfSites
@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open CategoryTheory.Functor.sheafPullbackConstruction
/-- Abelian pullback along an open-restriction lift preserves finite limits.

Source: Stacks Project, Sites, Tags 00X5 and 00X6; Etale Cohomology, Tag 09AX;
Modules on Sites, Tag 03DJ.
(blueprint: lem-weil-pbc-zariski-etale-pushed-resolution-finite-limits)

Proof: the usual inclusion j preserves finite limits. Both i and j become
X.restrictFunctor after applying Scheme.Etale.forget X, whose codomain is Over X,
not Scheme. This forgetful functor is fully faithful, so cancel it from the
natural isomorphism induced by the two equalities to obtain i ≅ j. Transfer
finite-limit preservation to i. Since the opens have finite limits, i is
representably flat. The universe-general left-Kan-extension theorem then gives
finite-limit preservation for i.op.lan with abelian coefficients: its pointwise
values are filtered colimits, which are exact in AddCommGrpCat. Finally the
constructed sheaf pullback is the composite of the sheaf inclusion, this Kan
extension, and sheafification, each preserving finite limits. No localized-site
factorization or extension by zero is required. -/
theorem zariski_etale_pushed_resolution_finite_limits
    {X : Scheme.{u + 1}}
    (i : X.Opens ⥤ X.Etale)
    (hi_inclusion : i ⋙ Scheme.Etale.forget X = X.restrictFunctor)
    (hi : i.IsContinuous (Opens.grothendieckTopology X.carrier)
      X.smallEtaleTopology)
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u + 1}]
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
    :
    PreservesFiniteLimits (sheafPullback i AddCommGrpCat.{u + 1}
      (Opens.grothendieckTopology X.carrier) X.smallEtaleTopology) := by
  let := hi
  obtain ⟨j, hj, _, hjlim, _, _⟩ := zariski_to_etale_is_morphism.{u + 1, 0} X
  let e : i ≅ j := Functor.fullyFaithfulCancelRight (Scheme.Etale.forget X)
    (eqToIso (hi_inclusion.trans hj.symm))
  have : PreservesFiniteLimits j := hjlim
  have : PreservesFiniteLimits i := preservesFiniteLimits_of_natIso e.symm
  have : RepresentablyFlat i := flat_of_preservesFiniteLimits i
  have : PreservesFiniteLimits (i.op.lan :
      (X.Opensᵒᵖ ⥤ AddCommGrpCat.{u + 1}) ⥤ X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :=
    preservesFiniteLimits_op_lan_of_flat i
  unfold sheafPullback
  exact comp_preservesFiniteLimits _ _

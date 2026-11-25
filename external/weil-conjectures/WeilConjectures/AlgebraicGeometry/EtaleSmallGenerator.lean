/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.Generator.Sheaf

/-!
# Concrete generator on the small etale site

Source: Stacks Project, Tags 01DO and 03EW; Mathlib free-Yoneda sheaves and
affine etale site comparison.
(blueprint: def-sc-etale-small-generator)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The coproduct of free abelian representable sheaves on a u-small affine etale model,
transported to the full etale site. It is a concrete construction, with no choice from
an unproved existence assertion.
Source: Stacks Project, Tags 01DO and 03EW; Mathlib's free-Yoneda construction and
comparison equivalences for dense subsites.
(blueprint: def-sc-etale-small-generator) -/
noncomputable def etaleSmallGenerator (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} := by
  let C := SmallModel.{u} X.AffineEtale
  let e := equivSmallModel.{u} X.AffineEtale
  let J := e.inverse.inducedTopology (AffineEtale.topology X)
  letI : HasSheafify J AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_of_essentiallySmall AddCommGrpCat.{u + 1} J
  letI : HasColimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  letI : HasColimitsOfSize.{u, u} (Sheaf J AddCommGrpCat.{u + 1}) :=
    Sheaf.instHasColimitsOfSize
  let Q : C × Unit → Sheaf J AddCommGrpCat.{u + 1} :=
    fun (⟨c, _⟩ : C × Unit) ↦ Sheaf.freeYoneda J c (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  letI : HasColimitsOfShape (Discrete (C × Unit)) (Sheaf J AddCommGrpCat.{u + 1}) :=
    HasColimitsOfSize.has_colimits_of_shape (C := Sheaf J AddCommGrpCat.{u + 1}) _
  letI : HasColimit (Discrete.functor Q) := HasColimitsOfShape.has_colimit _
  let G := ∐ Q
  let e₁ := e.inverse.sheafInducedTopologyEquivOfIsCoverDense
    (AffineEtale.topology X) AddCommGrpCat.{u + 1}
  let e₂ := (AffineEtale.Spec X).sheafInducedTopologyEquivOfIsCoverDense
    X.smallEtaleTopology AddCommGrpCat.{u + 1}
  exact e₂.functor.obj (e₁.functor.obj G)

end AlgebraicGeometry.Scheme

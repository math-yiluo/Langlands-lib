/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientProEtaleTorAmplitude
public import WeilConjectures.CategoryTheory.ConstantScalarRestrictionTensor

/-! # Fixed-scalar complexes on the coefficient-sized pro-etale site

Source: Stacks Tags 03CY and 09A5. Both changes of presentation are exact equivalences.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Read a fixed-scalar complex as a complex of modules over the constant ring on the
coefficient-sized site. First precompose with the site equivalence, then apply the
inverse of the specified constant-scalar restriction equivalence. No mathematical
object is selected from a mere existence statement.
Source: Stacks Tags 03CY and 09A5
(auxiliary; not a blueprint node). -/
@[irreducible] def fixedScalarComplexToModel (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) ℤ ⥤
      ConstantCompletion.Cx
        (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k) :=
  let F :=
    (AsSmall.down : coefficientProEtaleSiteModel.{u, u} X ⥤ X.ProEt).sheafPushforwardContinuous
      (ModuleCat.{u + 1} k)
      (coefficientProEtaleModelTopology.{u, u} X) (ProEt.topology X)
  letI : F.Additive := Functor.additive_of_preserves_binary_products F
  let G := (ConstantScalarRestriction.restriction
    (coefficientProEtaleModelTopology.{u, u} X) k).asEquivalence.inverse
  letI : G.Additive := Functor.additive_of_preserves_binary_products G
  (F ⋙ G).mapHomologicalComplex (.up ℤ)

/-- Localize the same fixed-scalar complex after the two exact changes of presentation.
Source: Stacks Tags 03CY, 09A5 and 05RU
(auxiliary; not a blueprint node). -/
@[irreducible] def fixedScalarDerivedModel (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (T : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k)) ℤ) :
    ConstantCompletion.D
      (ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, u} X) k) :=
  (ConstantCompletion.Q _).obj ((fixedScalarComplexToModel X k).obj T)

end AlgebraicGeometry.Scheme

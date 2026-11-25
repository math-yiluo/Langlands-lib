/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.EtaleExceptionalConstantTensor
public import WeilConjectures.AlgebraicGeometry.SystemProjection.EtaleSystemProjectionData
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjectionProperMate
import WeilConjectures.AlgebraicGeometry.Etale.Quotient.EtaleQuotientTensorProjectionOpenPasting

/-! # The restricted compact-support coefficient projection

Source: Zheng, Proposition 2.29(2), Construction 2.26, Lemma 5.22 and Proposition 5.24,
printed pp. 16, 36--37 (blueprint: lem-pur-etale-quotient-tensor-projection).

This identity compares the canonical coefficient map with the constant-tensor
projection. Its coefficient complex and scalar/tensor identifications are written
locally to keep the normalization module independent of this proof dependency.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SheafOfModules

namespace AlgebraicGeometry.Etale

/-- Restriction of the actual scalar projection is the constant-coefficient projection.
Source: Zheng, Proposition 2.29(2) and Construction 2.26; Stacks Tag 0GL6.
(blueprint: lem-pur-etale-quotient-tensor-projection).

Proof: expand the compact-support coefficient map as proper scalar mate followed by
open balancing. The restriction/proper-image comparison and scalar/tensor comparison
identify the first factor with the counit-defined proper projection. For the open
factor, restrict the two maps to the open and apply the invertible extension/restriction
unit. Both are the same balanced tensor map there; off the open both are zero.
Thus this factor is the inverse open projection followed by the coefficient pullback.
Naturality pastes these two squares. Exact descent of the constant-sheaf comparison
identifies the coefficient pullback with exceptionalConstantPullbackIso. Moving the
signed tensor symmetries through the projection gives coefficient-first order, which
is precisely exceptionalConstantProjectionMap. On K-flat representatives these are
the ordinary tensor comparisons, so no flatness of the ring map is required. -/
theorem etaleQuotientTensorProjection
    {C D : Type (u + 1)} [CommRing C] [CommRing D] (a : C →+* D)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (K : DerivedCategoryModule C X) :
  let V := (DerivedCategory.singleFunctor (ModuleCat.{u + 1} C) 0).obj
    ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))
  let e (W : Scheme.{u}) (L : DerivedCategoryModule C W) :=
    (scalarTensorIso a W).app L ≪≫
      ((derivedTensor (ModuleCat.{u + 1} C) W).obj L).mapIso
        ((DerivedCategory.singleFunctor _ 0).mapIso
          ((constantCommuteCompose W.smallEtaleTopology
            (ModuleCat.restrictScalars a)).app (ModuleCat.of D D)) ≪≫
          (Functor.mapDerivedCategorySingleFunctor
            (constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)) 0).symm.app
              ((ModuleCat.restrictScalars a).obj (ModuleCat.of D D))) ≪≫
      ((derivedTensorSymmetry (ModuleCat.{u + 1} C) W).app L).app
        ((constantSheaf W.smallEtaleTopology (ModuleCat.{u + 1} C)).mapDerivedCategory.obj V)
  (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a).map
      ((compactScalarMap a c).app K) ≫
    (SystemProjection.singleRestriction (CommRingCat.ofHom a) c).app
      ((scalarExtension a X).obj K) ≫
    (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).map
      (e X K).hom =
  (e Y ((rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} C) c).obj K)).hom ≫
    exceptionalConstantProjectionMap C c V K := by
  have hproper := scalarMate_restrict_eq_projection_unbounded a c.g
    ((openImmersionLowerShriek (ModuleCat.{u + 1} C) c.i).mapDerivedCategory.obj K)
  exact etaleQuotientTensorProjection_of_proper_mate a c K hproper

end AlgebraicGeometry.Etale

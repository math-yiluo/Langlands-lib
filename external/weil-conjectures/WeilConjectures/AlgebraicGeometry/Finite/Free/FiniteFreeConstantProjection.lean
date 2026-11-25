/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect

/-!
# Projection for bounded finite free constant complexes

Source: Stacks Project, Tag 0944, finite free case.
The library proves this case through dualizability of bounded finite free complexes.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Etale

attribute [local instance] Sheaf.monoidalCategory

/-- The projection map is invertible on a bounded finite free constant complex.
Source: Stacks Project, Tag 0944, finite free case
(blueprint: lem-sf-projection-bounded-finite-free-constant).

Proof: each term of the constant complex is dualizable, because it is isomorphic to
a finite power of the coefficient ring. A bounded complex of dualizable sheaves is
dualizable. Transport along the exact constant functor comparison identifies this
complex with the derived constant image of P. The projection formula at a dualizable
coefficient then gives the assertion. -/
theorem isIso_projectionMap_bounded_finiteFree_constant
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ)
    [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hP : ∀ i : ℤ, ∃ n : ℕ,
      Nonempty (P.X i ≅ ModuleCat.of A (Fin n → A))) :
    IsIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K).app
      ((constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)).mapDerivedCategory.obj
        (DerivedCategory.Q.obj P))) := by
  let C := constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A)
  let QP := (C.mapHomologicalComplex (.up ℤ)).obj P
  have hQP (i : ℤ) : IsDualizableSheaf (QP.X i) := by
    obtain ⟨n, ⟨e⟩⟩ := hP i
    exact IsDualizableSheaf.of_iso (C.mapIso e).symm
      (isDualizableSheaf_constantSheaf_pi n)
  have hD := DerivedCategory.isDualizableEtale_Q_obj QP a b hQP
  have hD' := hD.of_iso (C.mapDerivedCategoryFactors.app P).symm
  have result := isIso_rightDerivedLowerStarProjectionMap_app_app_of_isDualizable
    (L := C.mapDerivedCategory.obj (DerivedCategory.Q.obj P))
    (ModuleCat.{u + 1} A) f K hD'
  exact result

end AlgebraicGeometry.Etale

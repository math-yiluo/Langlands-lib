/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.RestrictionSquare.Terms

/-! # The mixed representative equation for finite coefficients -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization.RestrictionSquare

/-- `mixed_representation_normalized` for the finite coefficients `Mod_A`, with the signed
total complex written as `finiteTotal`.
(blueprint: lem-sf-mixed-representation-normalized) -/
theorem mixed_representation_finite
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (P Q : CochainComplex (FiniteModules A X) ℤ) :
    let F := ProEtale.upperStar (ModuleCat.{u + 1} A) j
    let a := F.mapDerivedCategoryFactors.hom
    let muX := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A X)) P Q
    let fc := F.mapHomologicalComplex (.up ℤ)
    let muU := Functor.LaxMonoidal.μ (DerivedCategory.Q (C := FiniteModules A U))
      (fc.obj P) (fc.obj Q)
    let c := ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q
    let delta := ((ProEtale.mapDerivedCategoryUpperStarDerivedTensorIso
      (ModuleCat.{u + 1} A) j).hom.app (DerivedCategory.Q.obj P)).app
        (DerivedCategory.Q.obj Q)
    let n := a.app P ⊗ₘ (F.leftDerivedFunctorIsoMapDerivedCategory.hom.app
      (DerivedCategory.Q.obj Q) ≫ a.app Q)
    delta ≫ F.mapDerivedCategory.map muX ≫ a.app (finiteTotal A X P Q) =
      n ≫ muU ≫ DerivedCategory.Q.map (inv c) :=
  mixed_representation_normalized (ModuleCat.{u + 1} A) j P Q

end SheafOfModules.OpenTensorNormalization.RestrictionSquare

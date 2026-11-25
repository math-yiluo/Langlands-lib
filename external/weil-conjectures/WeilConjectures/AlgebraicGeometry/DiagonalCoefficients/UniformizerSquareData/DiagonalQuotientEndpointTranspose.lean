/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalQuotientEndpointNormalization
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarEndpointsTranspose

/-! # The successive target endpoint under its actual adjunction

Source: diagonal tower coefficient changes (1), normalized scalar extension.
(blueprint: lem-diagonal-quotient-endpoint-transpose).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] spIntegralTwist geoCartierLine
attribute [local irreducible] derivedScalars quotientLine cyclicLine
  Functor.mapDerivedCategory Functor.mapDerivedCategorySingleFunctor
  DerivedCategory.singleFunctors HomotopyCategory.singleFunctors HasDerivedCategory.standard
  DerivedCategory HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctorIsoCompQ
  CondensedRing.lowerStar Profinite.continuousMapRingSheaf
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
  UniformizerSquareData.inverse_additive

private theorem insertion_comp
    {C D K : Type*} [Category C] [Category D] [Category K]
    (R : D ⥤ C) (S : K ⥤ D) {M : C} {N : D} {P Q : K}
    (v : M ⟶ R.obj N) (w : N ⟶ S.obj P) (z : P ⟶ Q) :
    (v ≫ R.map w) ≫ (S ⋙ R).map z = v ≫ R.map (w ≫ S.map z) := by
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc]

namespace UniformizerSquareData

attribute [local irreducible] Adjunction.homEquiv instCategoryDerivedCategory in
/-- The degree-zero endpoint transposes to its ordinary root insertion.
Source: diagonal tower coefficient changes (1)
(blueprint: lem-diagonal-quotient-endpoint-transpose).
Proof: Compose the scalar endpoint normalizations with the finite equivalence transpose. -/
theorem quotientEndpointZero_transpose
    {l : ℕ} [Fact l.Prime] {Y : Scheme.{u}}
    {E : PadicAlgCl.FiniteIntermediateField l} {π : PadicAlgCl.integers l E} {n : ℕ}
    {A : Type (u + 1)} [CommRing A] {hA : ((l ^ (n + 1) : ℕ) : A) = 0}
    (q : UniformizerSquareData l Y E π n A hA) :
    (quotientAdjunctionAux q).homEquiv _ _ (quotientEndpointZero q) =
      (DerivedCategory.singleFunctor _ 0).map q.quotientRootInsertion ≫
        (q.quotientRight.mapDerivedCategorySingleFunctor 0).inv.app _ := by
  let R₁ := Mod.comap (D := Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1})
    (coefficientMap (integralMap l E) (diagonalSurface Y))
  let R₂ := Mod.comap (D := Sheaf (Scheme.ProEt.topology (diagonalSurface Y)) Ab.{u + 1})
    (coefficientMap (quotientMap l E π n) (diagonalSurface Y))
  let z := q.eW.rootInsertion _ q.lineW.endpoint.iso
  have hv :
      (q.route.first.lineW.semilinear.hom ≫ R₁.map q.route.second.lineW.semilinear.hom) ≫
        (ScalarCompatibility.compositeRestriction q.route.first q.route.second).map z =
      q.quotientRootInsertion :=
    insertion_comp R₁ R₂ q.route.first.lineW.semilinear.hom
      q.route.second.lineW.semilinear.hom z
  have h := scalarRealizedEndpoints_transpose q.route.first q.route.second q.eW
    q.lineW.endpoint.iso q.quotientRootInsertion hv
  unfold quotientAdjunctionAux quotientEndpointZero quotientRight
  with_reducible assumption

end UniformizerSquareData
end AlgebraicGeometry.ProEtale.DiagonalCoefficients

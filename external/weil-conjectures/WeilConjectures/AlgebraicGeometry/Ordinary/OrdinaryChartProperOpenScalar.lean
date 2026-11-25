/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate
import all WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientMate

/-! # Unbounded scalar compatibility of proper/open exchange
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  upperStar lowerStar
/-- Unbounded scalar compatibility of proper/open exchange. -/
theorem ordinaryChartProperOpenScalar
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {U V W Z : Scheme.{u}}
    [IsNoetherian U] [IsNoetherian V] [IsNoetherian W] [IsNoetherian Z]
    {k : U ⟶ V} {r : U ⟶ W} {p : V ⟶ Z} {i : W ⟶ Z}
    [IsOpenImmersion k] [IsOpenImmersion i] [IsProper r] [IsProper p]
    (sq : IsPullback k r p i) (E : DerivedCategoryModule A U) :
    (scalarExtension φ Z).map ((properOpenCoefficientInterchange A sq).hom.app E) ≫
      finiteCoefficientDirectImageMap φ p
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) k).mapDerivedCategory.obj E) ≫
      (rightDerivedLowerStar (ModuleCat.{u + 1} B) p).map
        ((openScalarExtension φ k).hom.app E) =
      properOpenCoefficientComposite φ sq E := by
  let := (properOpenCoefficientInterchange_normalization B sq
    ((scalarExtension φ U).obj E)).2
  have h := coefficient_interchange_of_restriction
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) i)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) k)
    (derivedOpenImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} B) i)
    R((r)_*[ModuleCat.{u + 1} A]) R((p)_*[ModuleCat.{u + 1} A])
    R((r)_*[ModuleCat.{u + 1} B]) R((p)_*[ModuleCat.{u + 1} B])
    (scalarExtension φ U) (scalarExtension φ V) (scalarExtension φ W) (scalarExtension φ Z)
    (exactScalarReverse φ k) (exactScalarReverse φ i)
    (exactCoefficientMap φ r) (exactCoefficientMap φ p)
    (openScalarExtension φ k) (openScalarExtension φ i)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq)
    (exactDerivedBaseChangeMap (ModuleCat.{u + 1} B) sq.toCommSq)
    (exactCoefficient_exchange φ sq.toCommSq)
    (openScalarExtension_unit φ i) (openScalarExtension_unit φ k) E
    ((properOpenCoefficientInterchange A sq).hom.app E)
    ((properOpenCoefficientInterchange B sq).hom.app ((scalarExtension φ U).obj E))
    (properOpenCoefficientInterchange_normalization A sq E).1
    (properOpenCoefficientInterchange_normalization B sq ((scalarExtension φ U).obj E)).1
  simpa only [exactCoefficientMap_app, properOpenCoefficientComposite,
    rightDerivedLowerStar] using h

end AlgebraicGeometry.Etale

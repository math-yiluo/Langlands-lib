/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleTensorDefinitions
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarCoefficientSinglePullbackIso
import WeilConjectures.AlgebraicGeometry.Upper.UpperStarTensorCochainRepresentative
import WeilConjectures.AlgebraicGeometry.Upper.UpperStarSingleCoefficientRepresentative
import WeilConjectures.AlgebraicGeometry.Tensor.TensorSingleCounit
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData

/-!
# The tensor comparison with a coefficient sheaf in degree zero

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0FPH
(blueprint: lem-pur-upper-star-single-tensor-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v w v' w'
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar lowerStar

attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- Specializing the derived pullback tensor square to a sheaf in degree zero agrees
with the ordinary tensor square on every cochain complex.

Source: Stacks Project, sites-cohomology.tex, Tags 07A4 and 0FPH; step 2 of
lem-pur-scalar-tensor-pullback-normalization
(blueprint: lem-pur-upper-star-single-tensor-representative).

Proof: use the counit square defining leftDerivedUpperStarTensorComparison on P
and the complex concentrated in degree zero at M. The geometric counit on the
second complex equals exact inverse image on the single sheaf, by the defining
exact-derived comparison and the mapDerivedCategorySingleFunctor square. Compose
with the localization of the total-tensor/single-complex isomorphism. Its degree n
component is the degree n tensor comparison with M: only the summand (n,0) occurs,
so no permutation of degrees or sign occurs. Naturality with respect to k gives
the displayed square. No K-flat assumption is needed for this counit equation. -/
theorem upperStar_single_tensor_representative
    (A : Type (u + 1)) [CommRing A] {Z W : Scheme.{u}} (f : Z ⟶ W)
    {M : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)}
    {N : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (k : (upperStar (ModuleCat.{u + 1} A) f).obj M ≅ N)
    (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ) :
    ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (DerivedCategory.Q.obj P)).app ((DerivedCategory.singleFunctor _ 0).obj M) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj (DerivedCategory.Q.obj P))).map
          (upperStarSingleCoefficientIso A f k).hom ≫
        (scalarTensorModelFunctor N).map (scalarGeometricRepresentative A f P) ≫
        tensorSingleRepresentative N
          (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
      L(upperStar (ModuleCat.{u + 1} A) f).map (tensorSingleRepresentative M P) ≫
        scalarGeometricRepresentative A f
          (((tensorRight M).mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso (upperStarTensorSingleIso A f k) (.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl
              (upperStar (ModuleCat.{u + 1} A) f ⋙ tensorRight N)) (.up ℤ)).symm).hom.app P) := by
  change TensorSingleCounitSquare (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (scalarGeometricRepresentative A f) M N
    (upperStarSingleCoefficientIso A f k) (upperStarTensorSingleIso A f k) P
  exact tensor_single_cochain_counit (upperStar (ModuleCat.{u + 1} A) f)
    L(upperStar (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f)
    (scalarGeometricRepresentative A f) k
    (upperStarSingleCoefficientIso A f k) (upperStarTensorSingleIso A f k)
    (upperStar_single_coefficient_representative A f k)
    (by
      apply NatTrans.ext
      funext X
      rfl)
    (upperStar_tensor_cochain_representative A f)
    (by
      intro R S a
      exact scalarGeometricRepresentative_naturality A f a) P

end AlgebraicGeometry.Etale

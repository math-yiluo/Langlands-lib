/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.UniformizerSquareData.DiagonalCoefficientRouteComparison
import all WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalSourceAdjunctionTransport

/-! # Exact mate transport of ordinary source squares

Source: diagonal tower coefficient changes (1), exact scalar and finite-realization adjunctions.
(blueprint: lem-diagonal-source-mate-square).
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

-- Use the module-sheaf abelian structure of GeoCartierClass.
attribute [local instance 100000] sheafIsAbelian
attribute [local instance 200000] AlgebraicGeometry.ProEtale.diagonalAbSheafAbelian
attribute [local instance 300000] CommRing.toRing
attribute [local instance 400000] AlgebraicGeometry.ProEtale.diagonalModuleSheafAbelian

variable {C D K : Type*} [Category C] [Category D] [Category K]

/-- The transpose of the mate endpoint composite is the ordinary adjunction square.
Source: coefficient changes (1). (blueprint: lem-diagonal-source-mate-square).
Proof: naturality moves the endpoint map through the adjunction hom equivalence;
the formula for the mate followed by the quotient endpoint gives the result. -/
theorem mate_endpoint_transpose
    {L : C ⥤ D} {R : D ⥤ C} {L' : C ⥤ K} {R' : K ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (H : K ⥤ D) (s : R' ≅ H ⋙ R)
    {I : C} {P : K} (f : L'.obj I ⟶ P) (T : D) (c : H.obj P ⟶ T) :
    a.homEquiv _ _ ((UniformizerSquareData.restrictionMate a b H s).app I ≫
        H.map f ≫ c) =
      b.homEquiv _ _ f ≫ s.hom.app P ≫ R.map c := by
  rw [← Category.assoc, Adjunction.homEquiv_naturality_right, mate_postcompose]
  simp only [Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

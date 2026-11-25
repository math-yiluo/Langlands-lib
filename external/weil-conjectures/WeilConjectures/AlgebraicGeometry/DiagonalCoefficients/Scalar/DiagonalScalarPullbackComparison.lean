/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientPullbackEndpoints
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints

/-! # The scalar mate of restriction commuting with inverse image

Source: diagonal coefficient changes, paragraph (3), coefficient functors and pullback.
(blueprint: def-diagonal-scalar-pullback-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {R T : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj T] [IsCommMonObj T]
  (a : R ⟶ T) [IsMonHom a] {X S : Scheme.{u}} (f : X ⟶ S)

/-- Exact restriction commutes with derived inverse image, transported from the ordinary
restriction comparison by the canonical exact-functor identifications.
Source: coefficient functors and pullback, paragraph (3).
(blueprint: def-diagonal-scalar-pullback-comparison). -/
def scalarRestrictionPullbackIso :
    derivedUpper T f ⋙ (Mod.comap (coefficientMap a X)).mapDerivedCategory ≅
      (Mod.comap (coefficientMap a S)).mapDerivedCategory ⋙ derivedUpper R f :=
  Functor.isoWhiskerRight (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory T f)
      (Mod.comap (coefficientMap a X)).mapDerivedCategory ≪≫
    CondensedRing.derivedComapUpperStarIso a f ≪≫
    Functor.isoWhiskerLeft (Mod.comap (coefficientMap a S)).mapDerivedCategory
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R f).symm

/-- The scalar mate of the exact restriction/pullback comparison. Its construction uses
no flatness hypothesis on the coefficient change, and asserts no exchange invertibility.
Source: coefficient functors and pullback, paragraph (3).
(blueprint: def-diagonal-scalar-pullback-comparison). -/
def scalarPullbackComparison :
    derivedUpper R f ⋙ derivedScalars a X ⟶ derivedScalars a S ⋙ derivedUpper T f :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (scalarRestrictionPullbackIso a f)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

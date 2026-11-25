/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientCategory

/-! # Normalized diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-endpoints).

## Main definitions

- `derivedScalars`: the actual derived coefficient extension.
- `Endpoint`: the prescribed semilinear map and adjoint-normalized isomorphism.
- `Endpoint.shift`: its canonical shifted arrow.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

variable {Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ]
  {Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ'] [IsCommMonObj Λ'] (a : Λ ⟶ Λ') [IsMonHom a]

/-- The actual derived extension functor, named once to share its coefficient
and derived-category instances. Source: blueprint coefficient-change maps
(blueprint: def-sfb-diagonal-coefficient-endpoints). -/
def derivedScalars (X : Scheme.{u}) :
    DerivedCategory (Modules Λ X) ⥤ DerivedCategory (Modules Λ' X) :=
  (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor

/-- Derived extension carries the shift structure induced by its actual
adjunction to exact restriction, also for nonflat quotient maps.
Source: blueprint coefficient-change endpoint comparisons
(blueprint: def-sfb-diagonal-coefficient-endpoints). -/
instance (priority := 100) scalarCommShift (X : Scheme.{u}) :
    (derivedScalars a X).CommShift ℤ :=
  (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).leftAdjointCommShift ℤ

/-- A coefficient-semilinear map with its specified underlying sheaf map. Source:
blueprint coefficient-change maps, including quotient maps at every positive level
(blueprint: def-sfb-diagonal-coefficient-endpoints). -/
structure Semilinear {X : Scheme.{u}} (M : Modules Λ X) (N : Modules Λ' X)
    (m : M.X ⟶ N.X) where
  hom : M ⟶ (Mod.comap (coefficientMap a X)).obj N
  underlying : hom.hom = m

/-- An endpoint identification is fixed by its derived scalar/restriction adjoint.
Thus the displayed isomorphism cannot rescale a class or a trace. This definition
uses derived extension even for a nonflat quotient. Source: blueprint clauses 1--2
(blueprint: def-sfb-diagonal-coefficient-endpoints). -/
structure Endpoint {X : Scheme.{u}} (M : Modules Λ X) (N : Modules Λ' X)
    (m : M.X ⟶ N.X) where
  semilinear : Semilinear a M N m
  iso : (derivedScalars a X).obj
      ((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M) ≅
    (DerivedCategory.singleFunctor (Modules Λ' X) 0).obj N
  normalization :
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X)).homEquiv _ _ iso.hom =
      (DerivedCategory.singleFunctor (Modules Λ X) 0).map semilinear.hom ≫
      ((Mod.comap (coefficientMap a X)).mapDerivedCategorySingleFunctor 0).inv.app N

/-- The supported-source scalar map is the coefficient map pushed along the
closed diagonal and then the canonical ordinary restriction/direct-image comparison.
Source: blueprint clause 1 and proof step 3b
(blueprint: def-sfb-diagonal-coefficient-endpoints). -/
def supportMap (Y : Scheme.{u})
    (v : Mod.regular (condensedRingObj Λ (ProjectiveLine Y)) ⟶
      (Mod.comap (coefficientMap a (ProjectiveLine Y))).obj
        (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))) :
    source Λ Y ⟶ (Mod.comap (coefficientMap a (diagonalSurface Y))).obj (source Λ' Y) :=
  (CondensedRing.lowerStar Λ (diagonalImmersion Y)).map v ≫
    (CondensedRing.comapLowerStarIso a (diagonalImmersion Y)).inv.app
      (Mod.regular (condensedRingObj Λ' (ProjectiveLine Y)))

/-- Shift an endpoint comparison using the canonical shift of derived extension.
Source: blueprint coefficient changes (blueprint: def-sfb-diagonal-coefficient-endpoints). -/
def Endpoint.shift {X : Scheme.{u}} {M : Modules Λ X} {N : Modules Λ' X}
    {m : M.X ⟶ N.X} (e : Endpoint a M N m) :
    (derivedScalars a X).obj
        (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M)⟦(2 : ℤ)⟧) ⟶
      ((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj N)⟦(2 : ℤ)⟧ :=
  ((derivedScalars a X).commShiftIso
    (2 : ℤ)).hom.app _ ≫ e.iso.hom⟦(2 : ℤ)⟧'

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

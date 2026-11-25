/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientDiagrams

/-! # Generic data for comparing two coefficient routes

These structures group already supplied diagrams and maps; they contain no
existence assertion or new class equation.
Source: diagonal tower coefficient changes (1), derived scalar transitivity.
(blueprint: def-diagonal-coefficient-arrow-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Two successive specified coefficient extensions of an arbitrary diagonal
arrow. The two ScalarCompatibility structures retain their original full
normalizations; this record only shares their types.
Source: coefficient changes (1) (blueprint: def-diagonal-coefficient-arrow-transport). -/
structure CoefficientArrowRoute (l : ℕ) [Fact l.Prime] (Y : Scheme.{u})
    {I Q : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj I] [IsCommMonObj I] [MonObj Q] [IsCommMonObj Q]
    (a : Profinite.continuousMapRingObj.{u} ℤ_[l] ⟶ I) [IsMonHom a]
    (b : I ⟶ Q) [IsMonHom b]
    (L : ∀ X : Scheme.{u}, Modules I X) (M : ∀ X : Scheme.{u}, Modules Q X)
    (m : ∀ X : Scheme.{u}, (zlLine l X).X ⟶ (L X).X)
    (v : ∀ X : Scheme.{u}, (L X).X ⟶ (M X).X) where
  initial : Diagram (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y (zlLine l)
  middle : Diagram I Y L
  final : Diagram Q Y M
  first : ScalarCompatibility a Y (zlLine l) L m initial middle
  second : ScalarCompatibility b Y L M v middle final

/-- The normalized constant and root maps occurring in finite Cartier scalar
compatibility, without a class equation or a derived-unit assertion.
Source: Cartier coefficient naturality (4), and coefficient changes (1)
(blueprint: def-diagonal-coefficient-arrow-transport). -/
structure CartierScalarMaps
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) (N : ℕ) (hR : (N : R) = 0) (hA : (N : A) = 0)
    (Y : Scheme.{u}) where
  source : geoCartierConstant R (ProjectiveLine Y) ⟶
    (Sheaf.restrictScalars (Scheme.ProEt.topology (ProjectiveLine Y)) φ).obj
      (geoCartierConstant A (ProjectiveLine Y))
  line : geoCartierLine R N hR (diagonalSurface Y) ⟶
    (Sheaf.restrictScalars (Scheme.ProEt.topology (diagonalSurface Y)) φ).obj
      (geoCartierLine A N hA (diagonalSurface Y))
  source_normalization : ∀ (V : (ProjectiveLine Y).ProEtᵒᵖ) (a : R),
    source.hom.app V ((toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
      ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj (ModuleCat.of R R))).app V a) =
      (toSheafify (Scheme.ProEt.topology (ProjectiveLine Y))
        ((Functor.const (ProjectiveLine Y).ProEtᵒᵖ).obj (ModuleCat.of A A))).app V (φ a)
  line_normalization : ∀ (V : (diagonalSurface Y).Etaleᵒᵖ) (a : R)
    (z : ((diagonalSurface Y).rootsOfUnitySheaf N).obj.obj V),
    line.hom.app ((Scheme.toProEt (diagonalSurface Y)).op.obj V)
      (((comparisonAdjunction (ModuleCat.{u + 1} R) (diagonalSurface Y)).unit.app
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) N R hR)).hom.app V
          (Scheme.finiteEtaleTateOneGenerator R N (diagonalSurface Y) hR V a z)) =
      ((comparisonAdjunction (ModuleCat.{u + 1} A) (diagonalSurface Y)).unit.app
        (Scheme.finiteEtaleTateLine (diagonalSurface Y) N A hA)).hom.app V
          (Scheme.finiteEtaleTateOneGenerator A N (diagonalSurface Y) hA V (φ a) z)

/-- The Yoneda square for the supplied coefficient maps, without asserting it.
Source: coefficient changes (1) (blueprint: def-diagonal-coefficient-arrow-transport). -/
@[irreducible]
def CartierScalarMaps.Equation
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    {φ : R →+* A} {N : ℕ} {hR : (N : R) = 0} {hA : (N : A) = 0}
    {Y : Scheme.{u}} (maps : CartierScalarMaps φ N hR hA Y)
    (cR : GeoCartierClass R N hR (diagonalImmersion Y))
    (cA : GeoCartierClass A N hA (diagonalImmersion Y)) : Prop :=
  (Ext.mk₀ ((lowerStar (ModuleCat.{u + 1} R) (diagonalImmersion Y)).map
    maps.source)).comp
      (cA.mapExactFunctor (Sheaf.restrictScalars
        (Scheme.ProEt.topology (diagonalSurface Y)) φ)) (zero_add 2) =
    cR.comp (Ext.mk₀ maps.line) (add_zero 2)

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

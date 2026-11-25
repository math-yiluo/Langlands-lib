/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientEndpoints

/-! # Normalized diagonal coefficient diagrams

Source: blueprint main-20261015, sk-prop-diagonal-tower-coefficients.
(blueprint: def-sfb-diagonal-coefficient-scalars).

## Main definitions

- `RestrictionSquare.mate`: the canonical scalar/direct-image comparison.
- `TraceCompatibility`, `ScalarCompatibility`: the trace and diagonal squares.
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

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

/-- Restriction/direct-image comparison with its universal-unit normalization.
Its scalar mate is therefore the canonical scalar/direct-image map. Source:
blueprint coefficient changes, proof steps 1--2
(blueprint: def-sfb-diagonal-coefficient-scalars). -/
abbrev RestrictionSquare {X S : Scheme.{u}} (f : X ⟶ S)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f)) :=
  DiagonalTrace.ExactSquareOfUniverses
    (CondensedRing.lowerStar Λ' f) (CondensedRing.lowerStar Λ f)
    (Mod.comap (coefficientMap a X)) (Mod.comap (coefficientMap a S))
    R' R (CondensedRing.comapLowerStarIso a f)

/-- The scalar/direct-image comparison is the adjunction mate of the normalized
restriction comparison, for arbitrary coefficients including nonflat quotients.
Source: blueprint coefficient changes (blueprint: def-sfb-diagonal-coefficient-scalars). -/
def RestrictionSquare.mate {X S : Scheme.{u}} {f : X ⟶ S}
    {R : DiagonalRightDerived (CondensedRing.lowerStar Λ f)}
    {R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f)}
    (s : RestrictionSquare a f R R') :
    R.R ⋙ (derivedScalars a S) ⟶
      (derivedScalars a X) ⋙ R'.R :=
  Adjunction.pushHomOfComapIso
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a X))
    (Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a S)) s.iso

/-- One canonical scalar/trace square. The specified scalar/direct-image mate
must be invertible on the shifted positive line. Factoring this uniform
construction shares the derived-category witnesses for all three projections.
Source: blueprint clauses 1--2
(blueprint: def-sfb-diagonal-coefficient-scalars). -/
structure TraceCompatibility {X S : Scheme.{u}} (f : X ⟶ S)
    {M : Modules Λ X} {M' : Modules Λ' X} {m : M.X ⟶ M'.X}
    (c : Endpoint a (Mod.regular (condensedRingObj Λ S))
      (Mod.regular (condensedRingObj Λ' S)) (coefficientMap a S))
    (line : Endpoint a M M' m)
    (R : DiagonalRightDerived (CondensedRing.lowerStar Λ f))
    (R' : DiagonalRightDerived (CondensedRing.lowerStar Λ' f))
    (t : R.R.obj (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M)⟦(2 : ℤ)⟧) ⟶
      unit Λ S)
    (t' : R'.R.obj (((DerivedCategory.singleFunctor (Modules Λ' X) 0).obj M')⟦(2 : ℤ)⟧) ⟶
      unit Λ' S) where
  square : RestrictionSquare a f R R'
  comparison_iso : IsIso ((square.mate a).app
    (((DerivedCategory.singleFunctor (Modules Λ X) 0).obj M)⟦(2 : ℤ)⟧))
  trace : (derivedScalars a S).map t ≫ c.iso.hom =
    (square.mate a).app _ ≫ R'.R.map (line.shift a) ≫ t'

/-- All scalar-extension squares for a diagonal class and its three traces.
The endpoint maps are normalized adjoints of the actual unit and root maps, and
all direct-image maps are their specified adjunction mates. Source: blueprint
clauses 1--2 (blueprint: def-sfb-diagonal-coefficient-scalars). -/
structure ScalarCompatibility (Y : Scheme.{u})
    (L : ∀ X : Scheme.{u}, Modules Λ X) (L' : ∀ X : Scheme.{u}, Modules Λ' X)
    (m : ∀ X : Scheme.{u}, (L X).X ⟶ (L' X).X)
    (d : Diagram Λ Y L) (d' : Diagram Λ' Y L') where
  units : ∀ X : Scheme.{u}, Endpoint a
    (Mod.regular (condensedRingObj Λ X)) (Mod.regular (condensedRingObj Λ' X))
    (coefficientMap a X)
  lineP : Endpoint a (L (ProjectiveLine Y)) (L' (ProjectiveLine Y)) (m (ProjectiveLine Y))
  lineW : Endpoint a (L (diagonalSurface Y)) (L' (diagonalSurface Y)) (m (diagonalSurface Y))
  supported : Endpoint a (source Λ Y) (source Λ' Y)
    (supportMap a Y (units (ProjectiveLine Y)).semilinear.hom).hom
  q : TraceCompatibility a (ProjectiveLine Y ↘ Y)
    (units Y) lineP d.Rq d'.Rq d.traceq d'.traceq
  p₁ : TraceCompatibility a
    (pullback.fst (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (units (ProjectiveLine Y)) lineW d.R₁ d'.R₁ d.trace₁ d'.trace₁
  p₂ : TraceCompatibility a
    (pullback.snd (ProjectiveLine Y ↘ Y) (ProjectiveLine Y ↘ Y))
    (units (ProjectiveLine Y)) lineW d.R₂ d'.R₂ d.trace₂ d'.trace₂
  delta : (derivedScalars a (diagonalSurface Y)).map
      d.delta ≫ lineW.shift a = supported.iso.hom ≫ d'.delta

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

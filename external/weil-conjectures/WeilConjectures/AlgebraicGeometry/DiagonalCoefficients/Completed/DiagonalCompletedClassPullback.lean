/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientSourcePullback

/-! # Completed diagonal class under geometric inverse image

Source: the latest blueprint, diagonal coefficient changes, proof paragraph (3).
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

/-- Geometric inverse image of the completed positive diagonal class, before any
trace or extension of coefficients is considered. The supported source comparison
and the positive-line endpoint are normalized on ordinary sheaves.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-diagonal-tower/sk-prop-diagonal-tower-coefficients.proof.md, paragraph (3),
Cartier extension, whole Kummer system, and its completed class.
(blueprint: lem-diagonal-completed-class-pullback).

Proof: pull the positive Cartier extension along the diagonal square. On the
standard charts the equation a-b remains a non-zero-divisor over every base, and
the inverse equation still maps to +1. The units map and this generator define a
map of the two-term roofs. Exact inverse image and the canonical tensor comparison
therefore give a square of entire Kummer systems, with ell in degree -1 and the
identity in degree zero in the quotient resolutions. Use closed base change for
the supported constant source. Its explicit limit and the Cartesian root-line
limit make the inverse-image/derived-limit comparison invertible on both endpoints.
Apply naturality of that comparison to the single system morphism. The defining
whole-system equations in hdelta and hdelta' identify the completed arrows, without
inferring equality of derived morphisms from their finite evaluations. Finally
transport through eW and eW'. The source normalizations hs and hs' identify the
supported mate; the unit and root normalizations of the realizations identify the
coefficient and line endpoints. Thus the square is the one displayed below.
Neither traces nor the other coefficient stages are used. -/
theorem diagonalCompletedClass_pullback (l : ℕ) [Fact l.Prime]
    (Y Y' : Scheme.{u})
    [DiagonalTraceLocalizations l (diagonalSurface Y)]
    [DiagonalTraceLocalizations l (diagonalSurface Y')]
    (g : Y' ⟶ Y) (geometry : BaseSquares g)
    (hY : IsUnit (l : Γ(Y, ⊤))) (hY' : IsUnit (l : Γ(Y', ⊤)))
    (D : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y)))
    (D' : DiagonalDerivedReduction l (diagonalScalarExtension l (diagonalSurface Y')))
    (δ : diagonalCompletedDomain l Y ⟶ diagonalCompletedCodomain l Y)
    (δ' : diagonalCompletedDomain l Y' ⟶ diagonalCompletedCodomain l Y')
    (hdelta : DiagonalTrace.IsDiagonalLimit l Y hY D δ)
    (hdelta' : DiagonalTrace.IsDiagonalLimit l Y' hY' D' δ')
    (eP : CompletedRealization l (ProjectiveLine Y))
    (eW : CompletedRealization l (diagonalSurface Y))
    (eP' : CompletedRealization l (ProjectiveLine Y'))
    (eW' : CompletedRealization l (diagonalSurface Y'))
    (s : eW.F.obj (diagonalCompletedSource l Y) ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y)
    (s' : eW'.F.obj (diagonalCompletedSource l Y') ≅
      source (Profinite.continuousMapRingObj.{u} ℤ_[l]) Y')
    (hs : HEq (eW.underlying.inv.app (diagonalCompletedSource l Y) ≫ s.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y)).map
        (eP.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y)
            (Scheme.purTwistZlCompletion (ProjectiveLine Y) l))) ≫ eP.unitIso.hom.hom)))
    (hs' : HEq (eW'.underlying.inv.app (diagonalCompletedSource l Y') ≫ s'.hom.hom)
      ((lowerStar Ab.{u + 1} (diagonalImmersion Y')).map
        (eP'.underlying.inv.app (SheafOfModules.unit
          (Scheme.purTwistRing (ProjectiveLine Y')
            (Scheme.purTwistZlCompletion (ProjectiveLine Y') l))) ≫ eP'.unitIso.hom.hom))) :
    let R := Profinite.continuousMapRingObj.{u} ℤ_[l]
    let δz := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map s.inv ≫
      SpTowerClasses.mapSingleArrow eW.F (2 : ℤ) δ ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y)) 0).map
          eW.lineIso.hom)⟦(2 : ℤ)⟧'
    let δz' := (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map s'.inv ≫
      SpTowerClasses.mapSingleArrow eW'.F (2 : ℤ) δ' ≫
        ((DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
          eW'.lineIso.hom)⟦(2 : ℤ)⟧'
    ∃ data : SourcePullback R g (zlLine l)
        (spIntegralComparison (baseP g) l (bottomField l))
        (spIntegralComparison (baseW g) l (bottomField l)),
      (derivedUpper R (baseW g)).map δz ≫ data.endpoints.lineW.shift =
        (singlePullback R (baseW g) (source R Y)).hom ≫
          (DerivedCategory.singleFunctor (Modules R (diagonalSurface Y')) 0).map
            data.supported.hom ≫ δz' := by sorry

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

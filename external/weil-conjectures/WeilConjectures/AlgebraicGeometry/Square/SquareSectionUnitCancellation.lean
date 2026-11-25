/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageSectionUnit
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedSquareUnitMap
public import WeilConjectures.AlgebraicGeometry.Square.SquareResolutionRoofModels
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.AlgebraicGeometry.Square.SquareSectionUnitForward

/-! # Cancelling the normalized square on a cochain section unit

Source: Stacks Project, Cohomology, Tags 0D5T and 0D5X.
(blueprint: lem-weil-pbc-square-section-unit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
open Scheme.Modules
variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- A square transports the canonical section unit to the identity on the upstairs
section complex. This concerns only the target injective representative: it has no
source coefficient, coefficient morphism, numerator, denominator or replacement complex.
Source: Stacks Project, Tags 0D5T and 0D5X
(blueprint: lem-weil-pbc-square-section-unit-cancellation).

Proof: Identify the right-adjoint mate of the square with the normalized direct-image
composition square by derivedDirectImage_square_mate. Apply
normalizedDirectImageSquare_unit on J extended by zero. It identifies the two pasted
units with the ordinary pushforward square. Apply local derived sections. The universal
factorization equation for localLerayComparison carries each pasted unit to the
inverse-open section unit. Its change from sectionDerivedDirectImage to the standard
derived direct image preserves the unit, since both comparisons are inverse units
on the same K-injective representative. The definition of squareInverseOpenComparison
then cancels the two comparisons with the fixed K-injective representative. The
remaining ordinary pushforward square acts as the canonical equality transport of
sections on v inverse(f inverse V) and k inverse(g inverse V). The target raw comparison
uses precisely this equality of opens. Its inverse cancels the target section unit,
and naturality transports back along J.ι'. The resulting map is the identity.
No preservation of injectives by a pushforward is asserted; local Leray uses the
already established direct-image acyclicity. Empty opens and identity squares obey
the same unit equations. -/
theorem squareSectionUnit_cancellation {X S Z T : Scheme.{u}}
    (f : X ⟶ S) (k : Z ⟶ T) (g : T ⟶ S) (v : Z ⟶ X) (h : v ≫ f = k ≫ g)
    (G : Z.Modules) (J : InjectiveResolution G) (q : ℕ) (V : S.Opens) :
    let U := f ⁻¹ᵁ V
    let t := (RingedSpace.moduleDirectImage v.toLRSHom.toShHom).rightDerivedFunctorUnitQ
       J.cochainComplex ≫
        (schemeDerivedDirectImage v).map (inv (DerivedCategory.Q.map J.ι'))
    directImageSectionUnitAt f (q : ℤ) V
        (((pushforward v).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex) ≫
      ((RingedSpace.localHypercohomologyPresheaf S.toRingedSpace (q : ℤ)).map
        ((schemeDerivedDirectImage f).map t ≫
          (derivedSquareRightComparison f k g v h).hom.app
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).app (op V) ≫
      (RingedSpace.topEdgeLocalLeray g.toLRSHom.toShHom (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInverseOpenComparison g (q : ℤ)
        ((schemeDerivedDirectImage k).obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) 0).obj G))).hom.app (op V) ≫
      (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J (v ⁻¹ᵁ U) (by
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).inv = 𝟙 _ := by
  dsimp only
  apply (cancel_mono (squareInjectiveLocalComparison k G q (g ⁻¹ᵁ V) J
    (v ⁻¹ᵁ (f ⁻¹ᵁ V)) (by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, h])).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact squareSectionUnit_forward f k g v h G J q V

end AlgebraicGeometry

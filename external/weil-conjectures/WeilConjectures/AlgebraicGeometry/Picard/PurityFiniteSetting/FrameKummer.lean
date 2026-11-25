/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Picard.PurityFiniteSetting.FrameCoefficients
public import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup

/-! # Kummer classes and boundaries of an étale frame

The coordinate map of a unit, its Kummer class and the induced support boundary.
Part of the construction in
`WeilConjectures.AlgebraicGeometry.Picard.PurityFiniteSetting.FrameClass`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Functor
namespace WeilConjectures.PurityFiniteSetting

/-- The map defined by a unit to the punctured affine line over the coefficient base.
Its factorization through the coordinate basic open is the explicit frame map used
for the Kummer pullback. -/
noncomputable def frameCoordinateMap (P : PurityFiniteSetting.{u}) {X : Scheme.{u}}
    (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    X ⟶ Punctured (Spec (.of P.field.k)) := by
  let S := Spec (CommRingCat.of P.field.k)
  let q : X ⟶ AffineSpace (ULift.{u} (Fin 1)) S :=
    AffineSpace.homOfVector a (fun _ ↦ (t : Γ(X, ⊤)))
  let j := openImmersion S
  letI : IsOpenImmersion j := by
    dsimp [j, openImmersion]
    infer_instance
  have hpre : q ⁻¹ᵁ ((AffineSpace (ULift.{u} (Fin 1)) S).basicOpen
      (AffineSpace.coord S (ULift.up 0))) = ⊤ := by
    dsimp [q]
    rw [Scheme.preimage_basicOpen_top,
      AffineSpace.homOfVector_appTop_coord, X.basicOpen_of_isUnit t.isUnit]
  have hrange : Set.range q.base ⊆ Set.range j.base := by
    change Set.range q.base ⊆ Set.range
      (((AffineSpace (ULift.{u} (Fin 1)) S).basicOpen
        (AffineSpace.coord S (ULift.up 0))).ι.base)
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    exact hpre.ge trivial
  exact IsOpenImmersion.lift j q hrange

/-- Pull back the recorded affine-line datum's coordinate Kummer class along the unit's
map to G_m over Spec k. The cartesian twist comparison identifies its target with A(1).
The inherited divisibility hypothesis is the one required by `coordinateKummer`. -/
def frameCoordinateKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constant X) (P.frameCoefficientTwist h X 1) 1 := by
  let S := Spec (CommRingCat.of P.field.k)
  let g := P.frameCoordinateMap a t
  let κg := (P.coordinateKummer h S (𝟙 S)).mapExactFunctor
    (upperStar (ModuleCat.{u + 1} P.Coefficient) g)
  exact (Abelian.Ext.mk₀ (P.frameConstantPullback g).inv).comp κg (zero_add 1) |>.comp
    (Abelian.Ext.mk₀ (P.frameCoefficientPullback h g (puncturedProjection S)).hom) (add_zero 1)

/-- The frame unit's Kummer class, namely g^* kappa(t) from the affine-line datum. -/
def finiteFrameKummer (P : PurityFiniteSetting.{u}) (h : P.ramificationIndex ∣ P.level)
    (X : Scheme.{u}) (a : X ⟶ Spec (.of P.field.k)) (t : Γ(X, ⊤)ˣ) :
    Abelian.Ext (P.constant X) (P.frameCoefficientTwist h X 1) 1 :=
  P.frameCoordinateKummer h X a t

/-- The normalized twist counit for the individual complementary basic open. -/
def finiteFrameTwistCounit (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
      (P.frameCoefficientTwist h (X.basicOpen f).toScheme 1) ⟶ P.frameCoefficientTwist h X 1 :=
  (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).map
      (P.frameCoefficientPullback h (X.basicOpen f).ι a).inv ≫
    (openImmersionLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} P.Coefficient)
      (X.basicOpen f).ι).counit.app (P.frameCoefficientTwist h X 1)

/-- Extend the Kummer class by zero and apply the normalized twist counit.
The source is the first object of the canonical coefficient localization sequence. -/
def finiteFrameOpenKummer (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    Abelian.Ext
      ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
        ((upperStar (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).obj
          (P.constant X))) (P.frameCoefficientTwist h X 1) 1 :=
  (Abelian.Ext.mk₀
    ((openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι).map
      (P.frameConstantPullback (X.basicOpen f).ι).hom)).comp
    (((P.finiteFrameKummer h (X.basicOpen f).toScheme ((X.basicOpen f).ι ≫ a)
      (X.basicOpenUnit f)).mapExactFunctor
        (openImmersionLowerShriek (ModuleCat.{u + 1} P.Coefficient) (X.basicOpen f).ι)).comp
          (Abelian.Ext.mk₀ (P.finiteFrameTwistCounit h X a f)) (add_zero 1)) (zero_add 1)

/-- The boundary for (X,V(f)), formed before intersecting any supports. Its Yoneda
splice with the canonical short exact localization sequence is the right-derived
support connecting map, with the usual positive boundary convention. A principal
basic-open immersion is affine, hence quasi-compact; no quasi-compactness assumption
on X is imposed. Constant pullback identifies the closed source with i_* A_D. -/
def finiteFrameBoundary (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (X : Scheme.{u})
    (a : X ⟶ Spec (.of P.field.k)) (f : Γ(X, ⊤)) :
    cupSupportedHom P (X.zeroLocusSubschemeι {f})
      ((cupSingle P X).obj (P.frameCoefficientTwist h X 1)) 2 := by
  exact (P.frameSupportBoundary X f (P.frameCoefficientTwist h X 1)
    (P.finiteFrameOpenKummer h X a f)).hom

end WeilConjectures.PurityFiniteSetting

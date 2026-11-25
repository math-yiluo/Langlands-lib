/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.EtaleCoordinateTraceContractions
public import WeilConjectures.EtaleCohomology.Purity.Smooth.TraceDiagonal

/-! # Canonical maps for compact-support diagonal integration

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
thm-amb-p1-adjunction.proof.md, the exchange and projection computations in both triangles.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.SfDiagonalKernel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- The first-coordinate proper exchange, with exactly the flipped Cartesian square.
Source: thm-amb-p1-adjunction.proof.md, first triangle. -/
def exchangeFirst :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙ CoordinateTrace.pull A f ≅
      CoordinateTrace.pull A (pullback.snd f f) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f) :=
  have := isIso_rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f).flip
  asIso (rightDerivedLowerShriekBaseChangeMap A (IsPullback.of_hasPullback f f).flip)

/-- The canonical identification of the two pullbacks of a coefficient from the base.
Source: thm-amb-p1-adjunction.proof.md, common coefficient in the second triangle. -/
def coordinate {B : DerivedCategoryModule A X} (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (CoordinateTrace.pull A (pullback.fst f f)).obj B ≅
      (CoordinateTrace.pull A (pullback.snd f f)).obj B :=
  (CoordinateTrace.pull A (pullback.fst f f)).mapIso e ≪≫
    CoordinateTrace.coordinate A f L ≪≫
      (CoordinateTrace.pull A (pullback.snd f f)).mapIso e.symm

/-- The source identification for integration along the first projection.
Source: thm-amb-p1-adjunction.proof.md, alpha_1 for p_1 Delta = id. -/
def diagonalFirst :
    𝟭 (DerivedCategoryModule A X) ≅
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) (TraceDiagonalDatum.diagonal f) ⋙
        rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f) :=
  let h := TraceDiagonalDatum.diagonal_fst f
  have : HasCompactification (TraceDiagonalDatum.diagonal f ≫ pullback.fst f f) := by
    rw [h]
    infer_instance
  have : QuasiCompact (TraceDiagonalDatum.diagonal f ≫ pullback.fst f f) := by
    rw [h]
    infer_instance
  (rightDerivedLowerShriekIdIsoOfLowerStar (ModuleCat.{u + 1} A) X).symm ≪≫
    rightDerivedLowerShriekCongrIso A h.symm ≪≫
      rightDerivedLowerShriekCompIso A (TraceDiagonalDatum.diagonal f) (pullback.fst f f)

variable {f} {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

/-- The first trace is obtained from the original trace by inverse proper exchange.
Source: thm-amb-p1-adjunction.proof.md, trace base change in the first coordinate. -/
def traceFirst :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj B) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  (exchangeFirst A f).inv.app B ≫
    (CoordinateTrace.pull A f).map d.trace ≫
      (leftDerivedUpperStarDerivedTensorUnitIso f).hom

/-- The second trace uses the same original trace and the other proper exchange.
Source: thm-amb-p1-adjunction.proof.md, trace base change in the second coordinate. -/
def traceSecond (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).obj
      ((CoordinateTrace.pull A (pullback.snd f f)).obj B) ⟶
        derivedTensorUnit (ModuleCat.{u + 1} A) X :=
  (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
      (coordinate A f L e).inv ≫
    (TraceDiagonalDatum.baseChangeIso (Λ := A) f).inv.app B ≫
      (CoordinateTrace.pull A f).map d.trace ≫
        (leftDerivedUpperStarDerivedTensorUnitIso f).hom

/-- Both coordinate integrals of the same diagonal class are one. No adjunction or
triangle identity is included in this property.
Source: thm-amb-p1-adjunction.proof.md, the two diagonal integrals. -/
def Integrals (L : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) : Prop :=
  ((diagonalFirst A f).hom.app (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.fst f f)).map
        d.diagonalClass ≫ traceFirst A d =
      𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X)) ∧
    ((TraceDiagonalDatum.idIsoDiagonalSnd (Λ := A) f).hom.app
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ≫
      (rightDerivedLowerShriek (ModuleCat.{u + 1} A) (pullback.snd f f)).map
        d.diagonalClass ≫ traceSecond A d L e =
      𝟙 (derivedTensorUnit (ModuleCat.{u + 1} A) X))

/-- The inverse canonical projection followed by trace tensor identity and left unitor.
Source: thm-amb-p1-adjunction.proof.md, G7. -/
def counit :
    (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B) ⋙
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⟶
        𝟭 (DerivedCategoryModule A Y) :=
  (projectionIso A f B).inv ≫
    (derivedTensor (ModuleCat.{u + 1} A) Y).map d.trace ≫
      (derivedTensorUnitLeftUnitor (ModuleCat.{u + 1} A) Y).hom

end AlgebraicGeometry.Etale.SfDiagonalKernel

namespace AlgebraicGeometry.Etale.SupportedTrace

variable (A : Type (u + 1)) [CommRing A] [Finite A]

/-- The existing compactly supported direct image, with its coefficient category explicit.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
abbrev push {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] :=
  rightDerivedLowerShriek (ModuleCat.{u + 1} A) f

/-- The kernel object before integration along the second coordinate.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
abbrev kernel {X Y : Scheme.{u}} (f : X ⟶ Y)
    (B M : DerivedCategoryModule A X) :=
  CoordinateTrace.tensor A (pullback f f)
    ((CoordinateTrace.pull A (pullback.fst f f)).obj M)
    ((CoordinateTrace.pull A (pullback.snd f f)).obj B)

/-- The canonical compact-support projection formula in outside-coefficient-first order.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def orderedProjection {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f]
    (M : DerivedCategoryModule A Y) (E : DerivedCategoryModule A X) :
    CoordinateTrace.tensor A Y M ((push A f).obj E) ≅
      (push A f).obj
        (CoordinateTrace.tensor A X ((CoordinateTrace.pull A f).obj M) E) :=
  CoordinateTrace.swap A Y M ((push A f).obj E) ≪≫
    (projectionIso A f E).app M ≪≫
      (push A f).mapIso (CoordinateTrace.swap A X E ((CoordinateTrace.pull A f).obj M))

/-- Inverse projection and exchange, with the final symmetry putting the coefficient first.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def comparisonIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (B : DerivedCategoryModule A X) :
    (CoordinateTrace.pull A (pullback.fst f f) ⋙
      derivedTensorRight (ModuleCat.{u + 1} A) (pullback f f)
        ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ⋙
        push A (pullback.snd f f) ≅ push A f ⋙ (CoordinateTrace.pull A f ⋙ (derivedTensor
          (ModuleCat.{u + 1} A) X).obj B) :=
  TraceDiagonalDatum.sndProjectionIso f B ≪≫
    Functor.isoWhiskerLeft (push A f)
      (Functor.isoWhiskerLeft (CoordinateTrace.pull A f)
        ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).app B).symm)

/-- The component of the canonical kernel comparison.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def comparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (B M : DerivedCategoryModule A X) :
    (push A (pullback.snd f f)).obj (kernel A f B M) ≅
      (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj ((push A
        f).obj M) :=
  (comparisonIso A f B).app M

/-- Interchange the coordinates under direct image, using the canonical compositors.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def directComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    push A (pullback.snd f f) ⋙ push A f ≅
      push A (pullback.fst f f) ⋙ push A f :=
  (rightDerivedLowerShriekCompIso A (pullback.snd f f) f).symm ≪≫
    rightDerivedLowerShriekCongrIso A (pullback.condition (f := f) (g := f)).symm ≪≫
      rightDerivedLowerShriekCompIso A (pullback.fst f f) f

/-- Express the coefficient-first twisted pullback as the pullback of a tensor on the base.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def coefficientPull {X Y : Scheme.{u}} (f : X ⟶ Y)
    {B : DerivedCategoryModule A X} (L K : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B).obj K ≅
      (CoordinateTrace.pull A f).obj (CoordinateTrace.tensor A Y L K) :=
  ((derivedTensor (ModuleCat.{u + 1} A) X).mapIso e).app
      ((CoordinateTrace.pull A f).obj K) ≪≫
    (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} A) f L K).symm

/-- The common-base comparison for the whole twisted pullback object.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def coordinateTwisted {X Y : Scheme.{u}} (f : X ⟶ Y)
    {B : DerivedCategoryModule A X} (L K : DerivedCategoryModule A Y)
    (e : B ≅ (CoordinateTrace.pull A f).obj L) :
    (CoordinateTrace.pull A (pullback.fst f f)).obj ((CoordinateTrace.pull A f ⋙ (derivedTensor
      (ModuleCat.{u + 1} A) X).obj B).obj K) ≅
      (CoordinateTrace.pull A (pullback.snd f f)).obj ((CoordinateTrace.pull A f ⋙ (derivedTensor
        (ModuleCat.{u + 1} A) X).obj B).obj K) :=
  SfDiagonalKernel.coordinate A f (CoordinateTrace.tensor A Y L K)
    (coefficientPull A f L K e)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]

/-- Insert the diagonal class and integrate along the second projection, before exchange.
Source: thm-amb-p1-adjunction.proof.md (auxiliary; not a blueprint node). -/
def insertion {B : DerivedCategoryModule A X}
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B) :
    𝟭 (DerivedCategoryModule A X) ⟶
      (CoordinateTrace.pull A (pullback.fst f f) ⋙
        derivedTensorRight (ModuleCat.{u + 1} A) (pullback f f)
          ((CoordinateTrace.pull A (pullback.snd f f)).obj B)) ⋙
        push A (pullback.snd f f) :=
  (TraceDiagonalDatum.idIsoDiagonalSnd f).hom ≫
    Functor.whiskerRight (TraceDiagonalDatum.diagonalIso f).hom
      (push A (pullback.snd f f)) ≫
    Functor.whiskerRight
      (Functor.whiskerLeft (CoordinateTrace.pull A (pullback.fst f f))
        ((derivedTensor (ModuleCat.{u + 1} A) (pullback f f)).map δ ≫
          ((derivedTensorSymmetry (ModuleCat.{u + 1} A) (pullback f f)).app _).hom))
      (push A (pullback.snd f f))

/-- The insertion component with its target written as the pushed-forward kernel.
Source: thm-amb-p1-adjunction.proof.md, insertion of the diagonal class
(auxiliary; not a blueprint node). -/
def insertionApp {B : DerivedCategoryModule A X}
    (δ : (push A (TraceDiagonalDatum.diagonal f)).obj
        (derivedTensorUnit (ModuleCat.{u + 1} A) X) ⟶
      (CoordinateTrace.pull A (pullback.snd f f)).obj B)
    (M : DerivedCategoryModule A X) :
    (𝟭 (DerivedCategoryModule A X)).obj M ⟶
      (push A (pullback.snd f f)).obj (kernel A f B M) :=
  (insertion A f δ).app M

section TensorUnit

variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]

/-- The canonical right unitor with its unit object explicitly named.
Source: the right-unitor cancellation in thm-amb-p1-adjunction.proof.md
(auxiliary; not a blueprint node).
This is defined for general coefficients before specializing to modules. -/
def unitRightUnitor (Z : Scheme.{u})
    (M : _root_.DerivedCategory (Sheaf Z.smallEtaleTopology C)) :
    ((derivedTensor C Z).obj M).obj (derivedTensorUnit C Z) ≅ M :=
  derivedTensorRightUnitor C Z M

end TensorUnit

end AlgebraicGeometry.Etale.SupportedTrace

namespace AlgebraicGeometry.Etale.SfDiagonalKernel

variable (A : Type (u + 1)) [CommRing A] [Finite A]
variable {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
variable {B : DerivedCategoryModule A X} (d : TraceDiagonalDatum A f B)

/-- The canonical diagonal unit in the factor order B tensor f* K.
Source: thm-amb-p1-adjunction.proof.md, diagonal-kernel construction of eta.
The two factors are the original insertion and projection/exchange composites. -/
def unit :
    𝟭 (DerivedCategoryModule A X) ⟶
      rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⋙
        (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B) :=
  SupportedTrace.insertion A f d.diagonalClass ≫
    (SupportedTrace.comparisonIso A f B).hom

section Components

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  HasDerivedCategory.ofIsGrothendieckAbelian
  HasDerivedCategory.ofHasKInjectiveResolutions
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  derivedTensor derivedTensorSymmetry

attribute [local implicit_reducible] rightDerivedLowerShriek derivedTensorRight

/-- The component of the canonical unit is insertion followed by comparison.
Source: thm-amb-p1-adjunction.proof.md, definition of the diagonal unit
(auxiliary; not a blueprint node). -/
theorem unit_app_eq (M : DerivedCategoryModule A X) :
    (unit A d).app M =
      SupportedTrace.insertionApp A f d.diagonalClass M ≫
        (SupportedTrace.comparison A f B M).hom := by
  rfl

end Components

end AlgebraicGeometry.Etale.SfDiagonalKernel

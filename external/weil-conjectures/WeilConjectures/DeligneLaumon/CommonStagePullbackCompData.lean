/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom

/-! # Common-stage pullback composition data

(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u v
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures
variable (l : ℕ) [Fact l.Prime]
  (Ω : Type v) [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The prescribed pullback object on an arbitrary literal common-stage pair.
Source: blueprint common-stage pullback convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
theorem commonStagePullbackIntegralObject {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    (commonStageDerivedPullback l Ω f).obj P =
      (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
        ((sfRationalConstructibleLocalization l _ X).obj
          ((constructibleIntegralPullback l _ f).obj P.obj.obj)) := by
  refine ((commonStageDerivedPullback_existsUnique l Ω f).exists.choose_spec.1 P).trans ?_
  change (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
    ((rationalDerivedPullback l _ f).obj P.obj) = _
  exact congrArg (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
    ((rationalDerivedPullback_existsUnique l _ f).exists.choose_spec.2.1 P.obj)

/-- The component obtained from the specified integral compositor and object equalities.
Source: Stacks 099N(5), blueprint common-stage composition convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
def commonStagePullbackCompComponent {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (commonStageDerivedPullback l Ω (f ≫ g)).obj P ≅
      (commonStageDerivedPullback l Ω f).obj ((commonStageDerivedPullback l Ω g).obj P) :=
  eqToIso (commonStagePullbackIntegralObject l Ω (f ≫ g) P) ≪≫
    (GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).mapIso
      ((sfRationalConstructibleLocalization l _ X).mapIso
        (((integralPullbackComposition l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).choose f g).app
            P.obj.obj)) ≪≫
    (eqToIso ((congrArg (commonStageDerivedPullback l Ω f).obj
      (commonStagePullbackIntegralObject l Ω g P)).trans
        (commonStagePullbackIntegralObject l Ω f
          ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
            ((sfRationalConstructibleLocalization l _ Y).obj
              ((constructibleIntegralPullback l _ g).obj P.obj.obj)))))).symm

section
attribute [local irreducible] ScalarLocalization.category

/-- Object representation for the selected common-stage pullback functor.
Source: the defining universal property of common-stage pullback.
Proof: the object clause of `commonStageDerivedPullback_existsUnique`.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
theorem commonStageDerivedPullback_object_representation
    {V W : Scheme.{u}} (k : V ⟶ W)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    (commonStageDerivedPullback l Ω k).obj M = commonStagePullbackObject l Ω k M :=
  (commonStageDerivedPullback_existsUnique l Ω k).exists.choose_spec.1 M

/-- Map representation for a common-stage pullback on one stage representative.
Source: the defining universal property of common-stage pullback.
Proof: the representative clause of `commonStageDerivedPullback_existsUnique`.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
theorem commonStageDerivedPullback_map_representation
    {V W : Scheme.{u}} (k : V ⟶ W)
    [∀ v : V, Invertible (l : V.residueField v)]
    [∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (hM : M.stage ≤ L) (hN : N.stage ≤ L)
    (s : M.toStage hM ⟶ N.toStage hN) :
    HEq ((commonStageDerivedPullback l Ω k).map
      (GeneralAlgebraicallyClosedCoefficients.ofHom M N L hM hN s))
      (GeneralAlgebraicallyClosedCoefficients.ofHom
        (commonStagePullbackObject l Ω k M) (commonStagePullbackObject l Ω k N)
        L hM hN
        ((commonStagePullbackComparison l Ω k M L hM).hom ≫
          (rationalDerivedPullback l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) k).map s ≫
          (commonStagePullbackComparison l Ω k N L hN).inv)) :=
  (commonStageDerivedPullback_existsUnique l Ω k).exists.choose_spec.2 M N L hM hN s

end

attribute [local irreducible] commonStagePullbackCompComponent
  commonStageDerivedPullback constructibleIntegralPullback

/-- The component arrow is exactly the localized integral compositor up to object equality.
Source: blueprint normalized composition convention
(blueprint: lem-zl-common-stage-pullback-comp-naturality). -/
theorem commonStagePullbackCompComponent_heq {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq (commonStagePullbackCompComponent l Ω f g P).hom
      ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).map
        ((sfRationalConstructibleLocalization l _ X).map
          (((integralPullbackComposition l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage)).choose f g).hom.app
              P.obj.obj))) := by
  unfold commonStagePullbackCompComponent
  apply (conj_eqToHom_iff_heq _ _ (commonStagePullbackIntegralObject l Ω (f ≫ g) P)
    ((congrArg (commonStageDerivedPullback l Ω f).obj
      (commonStagePullbackIntegralObject l Ω g P)).trans
        (commonStagePullbackIntegralObject l Ω f
          ((GeneralAlgebraicallyClosedCoefficients.inclusion P.stage).obj
            ((sfRationalConstructibleLocalization l _ Y).obj
              ((constructibleIntegralPullback l _ g).obj P.obj.obj)))))).1
  simp only [Iso.trans_hom, eqToIso.hom]
  rfl

/-- The rational pullback compositor at a fixed coefficient stage, obtained by
transporting the selected integral compositor through the canonical pullback objects.
Source: Stacks 099N(5), finite-stage representative convention.
(blueprint: lem-zl-common-stage-pullback-comp-naturality-representative). -/
def commonStagePullbackRationalComposition
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Z)
    (hM : M.stage ≤ L) :
    (rationalDerivedPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).obj
        (M.toStage hM) ≅
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj
        ((rationalDerivedPullback l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
            (M.toStage hM)) :=
  eqToIso ((rationalDerivedPullback_existsUnique l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) (f ≫ g)).exists.choose_spec.2.1
        (M.toStage hM)) ≪≫
    (sfRationalConstructibleLocalization l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) X).mapIso
      (((integralPullbackComposition l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)).choose f g).app
          (M.toStage hM).obj) ≪≫
    (eqToIso ((congrArg
      (rationalDerivedPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).obj
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).exists.choose_spec.2.1
          (M.toStage hM))).trans
      ((rationalDerivedPullback_existsUnique l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) f).exists.choose_spec.2.1
          ((sfRationalConstructibleLocalization l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) Y).obj
              ((constructibleIntegralPullback l
                (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) g).obj
                (M.toStage hM).obj))))).symm

end WeilConjectures

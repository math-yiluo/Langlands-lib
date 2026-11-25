/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Functor
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarExtension
public import WeilConjectures.CategoryTheory.StageSystem.PbcQbarCategory

/-! # Interfaces for scalar-compatible proper-base-change operations

These are the operation interfaces used by proper-base-change descent.

## Implementation details

Keeping these definitions separate lets the finite-stage inputs of descent avoid importing it.
On the normalized PBC stage systems, the unit equation of a `CoherentExactMorphism` follows from
associator coherence at repeated stages.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v u' v'
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.StageSystem
/-- A family of exact finite-stage functors `Φ_E` with scalar-extension comparisons `β_{F/E}`
satisfying associator coherence, which are additive, compatible with shifts and preserve
distinguished triangles at every stage. -/
structure CoherentExactMorphism {I : Type w} [Preorder I]
    {C : I → Type u} [∀ i, Category.{v} (C i)]
    {D : I → Type u'} [∀ i, Category.{v'} (D i)]
    (S : StageSystem C) (S' : StageSystem D)
    [∀ i, Preadditive (C i)] [∀ i, Preadditive (D i)]
    [∀ i, HasZeroObject (C i)] [∀ i, HasZeroObject (D i)]
    [∀ i, HasShift (C i) ℤ] [∀ i, HasShift (D i) ℤ]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, ∀ n : ℤ, (shiftFunctor (D i) n).Additive]
    [∀ i, Pretriangulated (C i)] [∀ i, Pretriangulated (D i)]
    [∀ (i j : I) (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ (i j : I) (h : i ≤ j), (S'.T h).CommShift ℤ] where
  base : StageSystem.Morphism S S'
  additive : ∀ i, (base.Φ i).Additive
  [commShift : ∀ i, (base.Φ i).CommShift ℤ]
  betaCommShift : ∀ {i j : I} (h : i ≤ j),
    NatTrans.CommShift (base.β h).hom ℤ
  triangulated : ∀ i, (base.Φ i).IsTriangulated

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Ω : Type w)
  [Field Ω] [Algebra ℚ_[l] Ω] [IsAlgClosure ℚ_[l] Ω]

/-- The rational finite-stage direct image is the restriction of the actual ringed
pro-etale derived direct image followed by the recorded raw scalar localization. -/
def pbcDescentDirectImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω X E ⥤ pbcStageCategory l Ω Y E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (h E) (pbcStageUniformizer.{u} l Ω E)

/-- The rational finite-stage pullback is the restriction of the actual completed
ringed pro-etale pullback followed by the recorded raw scalar localization. -/
def pbcDescentPullback {X Y : Scheme.{u}} (g : X ⟶ Y)
    (h : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageCategory l Ω Y E ⥤ pbcStageCategory l Ω X E :=
  pbcConditionalRational (pbcStageDatum.{u} l Ω E)
    (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (h E)
    (pbcStageUniformizer.{u} l Ω E)

variable (X Y X' Y' : Scheme.{u})
  [IsNoetherian X]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [IsNoetherian Y]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]
  [IsNoetherian X']
  [dX' : Fact (∃ n : ℕ, topologicalKrullDim X' ≤ (n : WithBot ℕ∞))]
  [iX' : Fact (∀ t : X', IsUnit (l : X'.presheaf.stalk t))]
  [IsNoetherian Y']
  [dY' : Fact (∃ n : ℕ, topologicalKrullDim Y' ≤ (n : WithBot ℕ∞))]
  [iY' : Fact (∀ t : Y', IsUnit (l : Y'.presheaf.stalk t))]

section CanonicalBeta
variable {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
  [dX : Fact (∃ n : ℕ, topologicalKrullDim X ≤ (n : WithBot ℕ∞))]
  [iX : Fact (∀ t : X, IsUnit (l : X.presheaf.stalk t))]
  [dY : Fact (∃ n : ℕ, topologicalKrullDim Y ≤ (n : WithBot ℕ∞))]
  [iY : Fact (∀ t : Y, IsUnit (l : Y.presheaf.stalk t))]

/-- Direct-image β is the localized canonical scalar mate, conjugated by the
integral/scalar comparisons, including equal coefficient stages. The right-hand
side is the unique comparison characterized by the localized ambient mate in
`pbcScalarDirectImage_rational`, at the canonical small coefficient fields.
The endpoint equalities are already concluded separately for every stage;
quantification over their proofs does not impose an additional assumption. -/
def PbcDirectImageBetaSpec (f : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω X E),
      PbcIsBoundedConstructibleComplete Y (pbcStageDatum.{u} l Ω E)
        ((pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Rf : StageSystem.Morphism (pbcScalarSystem l Ω X dX.out iX.out)
      (pbcScalarSystem l Ω Y dY.out iY.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Rf.Φ E = pbcDescentDirectImage l Ω f pres E)
    (eF : Rf.Φ F = pbcDescentDirectImage l Ω f pres F)
    (K : pbcIntegralStage l Ω X E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Rf.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualDerivedPush f (pbcStageDatum.{u} l Ω E)) (pres E)).obj K) ≫
        β.hom.app (ScalarLocalization.mk K) ≫
        (pbcDescentDirectImage l Ω f pres F).map
          ((pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app K))
      (((pbcScalarDirectImage_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) f
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))

/-- Pullback β inverse is the localized canonical completed scalar comparison,
conjugated by the integral/scalar comparisons, including equal stages. The
right-hand side is the unique comparison characterized by the localized
completed tensor comparison in `pbcScalarCompletedPull_rational`, at the small
coefficient fields. Its orientation is opposite to `Morphism.β`. Endpoint
identifications are concluded separately, so this predicate fixes every β. -/
def PbcPullbackBetaSpec (g : X ⟶ Y)
    (pres : ∀ (E : Padic.FiniteCoefficientFields l Ω) (K : pbcIntegralStage l Ω Y E),
      PbcIsBoundedConstructibleComplete X (pbcStageDatum.{u} l Ω E)
        ((pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)).obj K.obj))
    (Lg : StageSystem.Morphism (pbcScalarSystem l Ω Y dY.out iY.out)
      (pbcScalarSystem l Ω X dX.out iX.out)) : Prop := by
  exact ∀ {E F : Padic.FiniteCoefficientFields l Ω} (hEF : E ≤ F)
    (eE : Lg.Φ E = pbcDescentPullback l Ω g pres E)
    (eF : Lg.Φ F = pbcDescentPullback l Ω g pres F)
    (K : pbcIntegralStage l Ω Y E),
    let β := Functor.isoWhiskerRight (eqToIso eE).symm _ ≪≫ Lg.β hEF ≪≫
      Functor.isoWhiskerLeft _ (eqToIso eF)
    HEq
      ((pbcDescentPullback l Ω g pres F).map
          ((pbcScalarIntegralComparison l Ω Y dY.out iY.out hEF).inv.app K) ≫
        β.inv.app (ScalarLocalization.mk K) ≫
        (pbcScalarIntegralComparison l Ω X dX.out iX.out hEF).hom.app
          ((pbcConditionalIntegral (pbcStageDatum.{u} l Ω E)
            (pbcActualCompletedPull g (pbcStageDatum.{u} l Ω E)) (pres E)).obj K))
      (((pbcScalarCompletedPull_rational l (pbcFiniteField.{u} l Ω E)
        (pbcFiniteField.{u} l Ω F) (pbcFiniteFieldInclusion l Ω hEF) g
        dX.out dY.out iX.out iY.out (pres E) (pres F)).exists.choose).hom.app
          (ScalarLocalization.mk K))
end CanonicalBeta

end AlgebraicGeometry.Scheme

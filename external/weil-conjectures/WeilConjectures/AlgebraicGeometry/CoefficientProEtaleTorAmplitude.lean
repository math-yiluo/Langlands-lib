/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleSmallModelComparison
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData

/-! # Tor amplitude with independent coefficient size

Source: Stacks Project, Tag 08FZ (auxiliary; not a blueprint node).
The original predicate is retained. The additional interface uses the same standard
localization on the coefficient-sized site and the existing total tensor on K-flat models.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- Cohomology at the standard derived localization. Source: Stacks Tag 05RU
(auxiliary; not a blueprint node). -/
abbrev coefficientModelCohomology {C : Type w} [SmallCategory C]
    {T : GrothendieckTopology C} (R : Sheaf T CommRingCat.{w}) (q : ℤ) :
    ConstantCompletion.D R ⥤ ConstantCompletion.Mod R :=
  @DerivedCategory.homologyFunctor _ _ _ (HasDerivedCategory.standard _) q

/-- The Tor test on every K-flat representative, tensoring with every degree-zero module.
K-flat resolutions exist, so quantification over representatives is independent of choices.
Source: Stacks Tags 08FZ and 06YS (auxiliary; not a blueprint node). -/
def HasCoefficientModelTorAmplitude {C : Type w} [SmallCategory C]
    {T : GrothendieckTopology C} (R : Sheaf T CommRingCat.{w})
    (K : ConstantCompletion.D R) (a b : ℤ) : Prop :=
  a ≤ b ∧ ∀ P : ConstantCompletion.Cx R,
    CochainComplex.IsKFlatIndependentCoefficients (J := T) (R := R) P →
    Nonempty ((ConstantCompletion.Q R).obj P ≅ K) →
    ∀ (M : ConstantCompletion.Mod R) (q : ℤ), q < a ∨ b < q →
      IsZero ((((ringedKoszulTensor R).obj P).obj
        ((HomologicalComplex.single (ConstantCompletion.Mod R)
          (ComplexShape.up ℤ) 0).obj M)).homology q)

end CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Sheafification on the existing coefficient-sized small site, with its exact size.
This uses the general small-site theorem, avoiding the older successor-universe instance.
Source: Stacks Tags 00W1 and 08FZ (auxiliary; not a blueprint node). -/
instance coefficientModelAdditiveSheafify (X : Scheme.{u}) :
    HasSheafify (coefficientProEtaleModelTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The same size-correct sheafification on the etale model.
Source: Stacks Tags 00W1 and 08FZ (auxiliary; not a blueprint node). -/
instance coefficientEtaleModelAdditiveSheafify (X : Scheme.{u}) :
    HasSheafify (smallModelComparisonEtaleTopology.{u, v} X)
      AddCommGrpCat.{max v (u + 1)} :=
  GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _

/-- The recorded pro-etale Tor predicate on the equivalent coefficient-sized model.
No equality between the scheme and coefficient universes is required.
Source: Stacks Tags 08FZ and 09A5 (auxiliary; not a blueprint node). -/
abbrev HasCoefficientProEtaleTorAmplitude (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (K : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A))
    (a b : ℤ) : Prop :=
  HasCoefficientModelTorAmplitude _ K a b

/-- Finite Tor amplitude is one common ordered interval for all module-sheaf tests.
Source: Stacks Tag 08FZ (auxiliary; not a blueprint node). -/
abbrev HasFiniteCoefficientProEtaleTorAmplitude (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (K : CategoryTheory.ConstantCompletion.D
      (CategoryTheory.ConstantCompletion.constant (coefficientProEtaleModelTopology.{u, v} X) A)) :
    Prop :=
  ∃ a b : ℤ, HasCoefficientProEtaleTorAmplitude X A K a b

end AlgebraicGeometry.Scheme

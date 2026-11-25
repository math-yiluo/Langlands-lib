/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
public import WeilConjectures.SmoothPurity.Sf.SfConstructibleHeart
public import WeilConjectures.SmoothPurity.Finite.FiniteCoefficientPoint
public import WeilConjectures.DeligneLaumon.ConstructibleTruncations
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SmoothPurity.Sf.SfIntegralStandardTruncations

/-! # Standard cohomology of the specified point realization

Source: Bhatt--Scholze, Propositions 6.8.11(3), 6.8.14 and Section 4.1;
the exact-sections, localization and coherence argument of the DAG
(blueprint: lem-a1-point-realization-standard-cohomology).

The ordinary target is viewed through its full embedding in D(E), and the
common-stage target through its fully faithful realization in D(Ω). Thus its
cohomological classes are the usual classes, without choosing a new target category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe w u uC vC uB vB uA vA uD vD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Triangulated AlgebraicGeometry
namespace WeilConjectures

/-- The canonical truncation comparisons together with exactness and t-exactness.
The equations fix both comparisons by the truncation counit and unit.
Source: the DAG proof, Steps 2--4, using BBD 1.3.3
(blueprint: lem-a1-point-realization-standard-cohomology). -/
structure PointRealizationComparison
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    (t : TStructure C) (s : TStructure B) (F : C ⥤ B) where
  commShift : F.CommShift ℤ
  exact : (fun [_c : F.CommShift ℤ] ↦ F.IsTriangulated) (_c := commShift)
  tExact : F.IsTExact t s
  upper : ∀ j : ℤ, t.truncLE j ⋙ F ≅ F ⋙ s.truncLE j
  lower : ∀ j : ℤ, t.truncGE j ⋙ F ≅ F ⋙ s.truncGE j
  upper_counit : ∀ (j : ℤ) (K : C),
    (upper j).hom.app K ≫ (s.truncLEι j).app (F.obj K) =
      F.map ((t.truncLEι j).app K)
  lower_unit : ∀ (j : ℤ) (K : C),
    F.map ((t.truncGEπ j).app K) ≫ (lower j).hom.app K =
      (s.truncGEπ j).app (F.obj K)

/-- Compose the counit- and unit-characterized comparisons, then commute the shift.
This is the truncation-induced δ, rather than an arbitrary cohomology isomorphism.
Source: DAG proof, Step 4 (blueprint: lem-a1-point-realization-standard-cohomology). -/
def PointRealizationComparison.delta
    {C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    {B : Type uB} [Category.{vB} B] [Preadditive B] [HasZeroObject B] [HasShift B ℤ]
    [∀ n : ℤ, (shiftFunctor B n).Additive] [Pretriangulated B]
    {t : TStructure C} {s : TStructure B} {F : C ⥤ B}
    (P : PointRealizationComparison t s F) (j : ℤ) :
    constructibleTruncationCohomology t j ⋙ F ≅
      F ⋙ constructibleTruncationCohomology s j :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (P.commShift.commShiftIso j) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ (P.lower j) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (P.upper j) _ ≪≫ Functor.associator _ _ _) _ ≪≫
    Functor.associator _ _ _

variable (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]

section StageNormalization

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] pointStageFibre pointStageFibreScalarIso
  pointRationalFibre pointRationalFibreScalarIso DerivedCategory.pointFdQbarStageComp

end StageNormalization

end WeilConjectures

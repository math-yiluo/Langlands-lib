/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatWeaklyEtale
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
public import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
import WeilConjectures.CategoryTheory.Exact.ExactDerivedHomComparisonShift
import WeilConjectures.CategoryTheory.SixFunctors.ContravariantIsoLocus
import all WeilConjectures.CategoryTheory.Exact.ExactClosedDerivedHom
import all WeilConjectures.CategoryTheory.Exact.ExactDerivedTensorSquare
import WeilConjectures.SixFunctors.ProEtale.Comparison.Monoidal
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtaleDerived
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.InternalHom
import WeilConjectures.SixFunctors.Etale.LowerShriek.EtaleMapProjection

/-! # Exactness and thick locus of the specified site Hom comparison

The map is the recorded evaluation transpose. The shift structures below are normalized
by the adjunction mate of total-tensor shifts and the signed opposite-category convention.
## Main declarations

* `siteHomComparison_exact_thick`: exactness, signed naturality and thick closure.
* `siteHomComparison_restriction`: the canonical equation on every etale slice.
* The other declarations construct their canonical functors, shifts and maps.

Restrictions are exact inverse image along an etale object, canonically identified with
slice restriction. Every comparison is constructed from the existing adjunctions.

## References

* Stacks Project, Tags 08J9, 08JB and 08JC
* Stacks 07A4
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 2048
universe u v d e d₁ e₁
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Functor.mapDerivedCategory

/-- Derive the ordinary tensor comparison and transport it to the exact termwise
functor. This packages the existing construction without selecting new tensor data. -/
@[irreducible] def siteHomExactDerivedMonoidal
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] :
    F.mapDerivedCategory.Monoidal :=
  Functor.exactClosedDerivedMonoidal F

/-- The complete exactness and thick-locus assertion for a specified closed-category
comparison. This is a transparent proposition, not an extra hypothesis or chosen map.
It uses the canonical signed source shifts on both rows. -/
@[irreducible] def siteHomExactThickAssertion
    {C : Type d} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [MonoidalClosed C] [(curriedTensor C).CommShift₂Int]
    {D : Type e} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [MonoidalCategory D] [MonoidalClosed D] [(curriedTensor D).CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ]
    (b : ∀ K M : C, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (M : C) : Prop :=
  let B := MonoidalClosed.internalHom.flip.obj M ⋙ F
  let E := F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M)
  let P : ObjectProperty C := fun K ↦ IsIso (b K M)
  ∃ (sB : B.CommShift ℤ) (sE : E.CommShift ℤ) (β : B ⟶ E),
    (∀ K : C, β.app (op K) = b K M) ∧
    (fun [_sB : B.CommShift ℤ] [_sE : E.CommShift ℤ] ↦
      B.IsTriangulated ∧ E.IsTriangulated ∧ NatTrans.CommShift β ℤ ∧
      (∀ (K : C) (n : ℤ), (B.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          (F.map ((siteHomOppositeSourceShift K n).hom.app M) ≫
            (F.commShiftIso n).hom.app ((ihom K).obj M))) ∧
      (∀ (K : C) (n : ℤ), (E.commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          ((MonoidalClosed.internalHom.map ((F.commShiftIso (-n)).inv.app K).op).app
              (F.obj M) ≫
            (siteHomOppositeSourceShift (F.obj K) n).hom.app (F.obj M))) ∧
      (∀ T : Triangle C, T ∈ distTriang C →
        ∃ φ : B.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)) ⟶
          E.mapTriangle.obj ((triangleOpEquivalence C).functor.obj (op T)),
          φ.hom₁ = β.app (op T.obj₃) ∧ φ.hom₂ = β.app (op T.obj₂) ∧
            φ.hom₃ = β.app (op T.obj₁))) (_sB := sB) (_sE := sE) ∧
    P.IsTriangulated ∧ P.IsStableUnderRetracts

private theorem exactThickAssertion_of_signed
    {C : Type d} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [MonoidalCategory C] [MonoidalClosed C] [(curriedTensor C).CommShift₂Int]
    {D : Type e} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    [MonoidalCategory D] [MonoidalClosed D] [(curriedTensor D).CommShift₂Int]
    (F : C ⥤ D) [F.CommShift ℤ] [F.IsTriangulated] [F.Additive]
    (M : C)
    [sH : (MonoidalClosed.internalHom.flip.obj M).CommShift ℤ]
    [sJ : (MonoidalClosed.internalHom.flip.obj (F.obj M)).CommShift ℤ]
    [(MonoidalClosed.internalHom.flip.obj M).IsTriangulated]
    [(MonoidalClosed.internalHom.flip.obj (F.obj M)).IsTriangulated]
    (hsH : ∀ K n,
      ((MonoidalClosed.internalHom.flip.obj M).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow • (siteHomOppositeSourceShift K n).hom.app M)
    (hsJ : ∀ K n,
      ((MonoidalClosed.internalHom.flip.obj (F.obj M)).commShiftIso n).hom.app (op K) =
        (n * (n + 1) / 2).negOnePow •
          (siteHomOppositeSourceShift K n).hom.app (F.obj M))
    (b : ∀ K M : C, F.obj ((ihom K).obj M) ⟶ (ihom (F.obj K)).obj (F.obj M))
    (β : MonoidalClosed.internalHom.flip.obj M ⋙ F ⟶
      F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M))
    [NatTrans.CommShift β ℤ] (hβ : ∀ K, β.app (op K) = b K M) :
    siteHomExactThickAssertion F b M := by
  let B := MonoidalClosed.internalHom.flip.obj M ⋙ F
  let E := F.op ⋙ MonoidalClosed.internalHom.flip.obj (F.obj M)
  unfold siteHomExactThickAssertion
  dsimp only
  refine ⟨inferInstanceAs (B.CommShift ℤ), inferInstanceAs (E.CommShift ℤ), β, ?_, ?_, ?_⟩
  · intro K
    exact hβ K
  · refine ⟨inferInstanceAs B.IsTriangulated, inferInstanceAs E.IsTriangulated,
      inferInstanceAs (NatTrans.CommShift β ℤ), ?_, ?_, ?_⟩
    · intro K n
      change (B.commShiftIso n).hom.app (op K) = _
      rw [Functor.commShiftIso_comp_hom_app, hsH]
      simp only [Functor.map_units_smul, Linear.units_smul_comp]
      rfl
    · intro K n
      change (E.commShiftIso n).hom.app (op K) = _
      rw [Functor.commShiftIso_comp_hom_app]
      have hFop : (F.op.commShiftIso n).hom.app (op K) =
          ((F.commShiftIso (-n)).inv.app K).op := by
        rw [Functor.op_commShiftIso_hom_app F (op K) n (-n) (add_neg_cancel n)]
        change (F.map (𝟙 _)).op ≫ _ ≫ 𝟙 _ = _
        rw [F.map_id, op_id, Category.id_comp, Category.comp_id]
      rw [hFop]
      rw [hsJ]
      simp only [Linear.comp_units_smul]
      rfl
    · intro T _
      exact ⟨(NatTrans.mapTriangle β).app
        ((triangleOpEquivalence _).functor.obj (op T)), rfl, rfl, rfl⟩
  · simpa only [hβ] using contravariantComparison_isoLocus β

private theorem exactThickAssertion_of_exactFunctor
    {C : Type d} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type e} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal] (M : DerivedCategory C)
    (b : ∀ K M : DerivedCategory C,
      F.mapDerivedCategory.obj ((ihom K).obj M) ⟶
        (ihom (F.mapDerivedCategory.obj K)).obj (F.mapDerivedCategory.obj M))
    (hb : letI := Functor.exactClosedDerivedMonoidal F
      ∀ K N, b K N = Functor.closedComparison F.mapDerivedCategory K N) :
    siteHomExactThickAssertion F.mapDerivedCategory b M := by
  let G := F.mapDerivedCategory
  let H := MonoidalClosed.internalHom.flip.obj M
  let J := MonoidalClosed.internalHom.flip.obj (G.obj M)
  letI := Functor.exactClosedDerivedMonoidal F
  let β : H ⋙ G ⟶ G.op ⋙ J :=
    { app := fun K ↦ Functor.closedComparison G K.unop M
      naturality := fun K L f ↦ by
        unfold Functor.closedComparison
        exact Functor.LaxMonoidal.map_pre_app_comp_ihomComparison_app G f.unop M }
  obtain ⟨sH, hH, hsH⟩ := nativeDerivedHom_signed_exact M
  obtain ⟨sJ, hJ, hsJ⟩ := nativeDerivedHom_signed_exact (G.obj M)
  letI := sH
  letI := sJ
  haveI : H.IsTriangulated := hH
  haveI : J.IsTriangulated := hJ
  haveI : NatTrans.CommShift β ℤ :=
    Functor.exactDerivedHomComparison_shift F M sH sJ hsH hsJ β (fun _ ↦ rfl)
  exact exactThickAssertion_of_signed G M hsH hsJ b β (fun K ↦ (hb K M).symm)

/-- Specialize the transparent assertion to the actual site evaluation comparison.
Abstracting the coefficient category keeps the canonical structures compact in kernel
checking. -/
@[irreducible] def siteHomSiteExactThick
    (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
    [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
    [Abelian.HasFunctorialFlatResolution B]
    (X : Scheme.{u}) [(comparisonUpperStar B X).PreservesFlat]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology B)) : Prop :=
  siteHomExactThickAssertion (comparisonUpperStar B X).mapDerivedCategory
    (siteComparisonEvaluationHom B X) M

section RestrictionSquare
variable (B : Type (u + 2)) [Category.{u + 1} B] [Abelian B]
  [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B]
  [MonoidalPreadditive B] [SymmetricCategory B] [MonoidalClosed B]
  [Abelian.HasFunctorialFlatResolution B]

private theorem comparisonDerivedMonoidal_eq (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat] :
    letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
    siteComparisonDerivedMonoidal B X =
      siteHomExactDerivedMonoidal (comparisonUpperStar B X) := by
  letI : (comparisonUpperStar B X).Monoidal := siteComparisonMonoidal B X
  unfold siteHomExactDerivedMonoidal
  exact Functor.exactDerivedMonoidal_eq_of_delta (comparisonUpperStar B X)
    (siteComparisonDerivedMonoidal B X) (siteComparisonDerivedMonoidal_δ B X)
private theorem siteComparisonEvaluationHom_eq_closedComparison (X : Scheme.{u})
    [(comparisonUpperStar B X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology B)) :
    letI : (comparisonUpperStar B X).mapDerivedCategory.Monoidal :=
      siteComparisonDerivedMonoidal B X
    siteComparisonEvaluationHom B X K M =
      Functor.closedComparison (comparisonUpperStar B X).mapDerivedCategory K M := by
  unfold siteComparisonEvaluationHom Functor.closedComparison
  rfl

end RestrictionSquare

private theorem siteHomExactThick_generic (V : Type (u + 2)) [Category.{u + 1} V] [Abelian V]
    [IsGrothendieckAbelian.{u + 1} V] [MonoidalCategory V]
    [MonoidalPreadditive V] [SymmetricCategory V] [MonoidalClosed V]
    [Abelian.HasFunctorialFlatResolution V] (X : Scheme.{u})
    [(comparisonUpperStar V X).PreservesFlat]
    (M : DerivedCategory (Sheaf X.smallEtaleTopology V)) :
    siteHomSiteExactThick V X M := by
  unfold siteHomSiteExactThick
  letI := siteComparisonMonoidal V X
  apply exactThickAssertion_of_exactFunctor
    (C := Sheaf X.smallEtaleTopology V)
    (D := Sheaf (Scheme.ProEt.topology X) V)
    (comparisonUpperStar V X) M (siteComparisonEvaluationHom V X)
  intro K N
  rw [siteComparisonEvaluationHom_eq_closedComparison]
  have he := comparisonDerivedMonoidal_eq V X
  unfold siteHomExactDerivedMonoidal at he
  exact congrArg (fun m ↦ @Functor.closedComparison _ _ _ _ _ _ _ _
    (comparisonUpperStar V X).mapDerivedCategory m.toLaxMonoidal K N) he

variable (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})

/-- The first contravariant functor F RHom(-,M), using the recorded Hom and pullback. -/
abbrev siteHomComparisonSource (M : Etale.DerivedCategoryModule A X) :=
  (Etale.derivedHom (ModuleCat.{u + 1} A) X).flip.obj M ⋙
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory

/-- The isomorphism locus of the specified evaluation transpose, not of chosen isomorphisms. -/
def siteHomComparisonLocus (M : Etale.DerivedCategoryModule A X) :
    ObjectProperty (Etale.DerivedCategoryModule A X) :=
  fun K ↦ IsIso (siteComparisonEvaluationHom (ModuleCat.{u + 1} A) X K M)

/-- Exactness, signed shift compatibility, the full reversed triangle morphism and thick
closure for the specified evaluation comparison, for each arbitrary fixed target M. -/
theorem siteHomComparison_exact_thick (M : Etale.DerivedCategoryModule A X) :
    siteHomSiteExactThick (ModuleCat.{u + 1} A) X M := by
  exact siteHomExactThick_generic (ModuleCat.{u + 1} A) X M

end AlgebraicGeometry.ProEtale

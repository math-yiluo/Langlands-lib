/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal

/-! # The evaluation-defined site comparison

The tensor comparison below uses only the comparison-site adjunction, avoiding
unrelated scheme-pullback coherence modules.

## References

* Stacks Tags 03EL, 08J7
* Stacks Tags 03EO, 03EL
-/

@[expose] public section
set_option autoImplicit false
universe u u₁ u₂
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
namespace AlgebraicGeometry.ProEtale

/-- The canonical strong monoidal structure of comparison inverse image. -/
@[irreducible]
noncomputable def siteComparisonMonoidal
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    (comparisonUpperStar A X).Monoidal := by
  let : (comparisonLowerStar A X).LaxMonoidal := by
    unfold comparisonLowerStar
    infer_instance
  let : (comparisonUpperStar A X).OplaxMonoidal :=
    (comparisonAdjunction A X).leftAdjointOplaxMonoidal
  let (V : X.ProEtᵒᵖ) : IsFiltered (CostructuredArrow X.toProEt.op V) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ (unop V))
  let (F G : Sheaf X.smallEtaleTopology A) :
      IsIso (Functor.OplaxMonoidal.δ (comparisonUpperStar A X) F G) := by
    unfold comparisonUpperStar
    infer_instance
  let : IsIso (Functor.OplaxMonoidal.η (comparisonUpperStar A X)) := by
    unfold comparisonUpperStar
    infer_instance
  exact .ofOplaxMonoidal _

private theorem derived_monoidal_exists
    {C : Type u₁} [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Abelian.HasFunctorialFlatResolution C]
    {D : Type u₂} [Category.{u + 1} D] [Abelian D]
    [IsGrothendieckAbelian.{u + 1} D] [MonoidalCategory D]
    [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Abelian.HasFunctorialFlatResolution D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.PreservesFlat] [F.IsLeftAdjoint] [F.Monoidal]
    (e : F.leftDerivedFunctor ≅ F.mapDerivedCategory) :
    ∃ m : F.mapDerivedCategory.Monoidal,
      let := m
      ∀ K M, Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
        e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
          (e.hom.app K ⊗ₘ e.hom.app M) := by
  let : F.leftDerivedFunctor.Monoidal := F.residueDerivedMonoidal
  refine ⟨Functor.Monoidal.transport e, ?_⟩
  dsimp only
  intro K M
  rw [Functor.Monoidal.transport_δ
    (C := DerivedCategory C) (D := DerivedCategory D) e K M]
  rfl

/-- The canonical derived tensor comparison admits a strong monoidal structure.
Its tensor components are prescribed, so the structure determines the comparison maps
used below. -/
theorem siteComparisonDerivedMonoidal_exists
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    let := siteComparisonMonoidal A X
    let F := comparisonUpperStar A X
    let e := F.leftDerivedFunctorIsoMapDerivedCategory
    ∃ m : F.mapDerivedCategory.Monoidal,
      let := m
      ∀ K M, Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
        e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
          (e.hom.app K ⊗ₘ e.hom.app M) := by
  let : (comparisonUpperStar A X).Monoidal := siteComparisonMonoidal A X
  exact derived_monoidal_exists
    (C := Sheaf X.smallEtaleTopology A)
    (D := Sheaf (Scheme.ProEt.topology X) A)
    (comparisonUpperStar A X)
    (comparisonUpperStar A X).leftDerivedFunctorIsoMapDerivedCategory

/-- Strong monoidal structure with the prescribed canonical derived tensor components.
Only those components and their inverses occur in the comparison maps. The preceding
proved theorem specifies them before the structure is selected. -/
@[irreducible]
noncomputable def siteComparisonDerivedMonoidal
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat] :
    (comparisonUpperStar A X).mapDerivedCategory.Monoidal :=
  (siteComparisonDerivedMonoidal_exists A X).choose

set_option backward.isDefEq.respectTransparency true in
/-- The chosen structure has exactly the canonical transported tensor components. -/
theorem siteComparisonDerivedMonoidal_δ
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    let := siteComparisonMonoidal A X
    let F := comparisonUpperStar A X
    let e := F.leftDerivedFunctorIsoMapDerivedCategory
    let := siteComparisonDerivedMonoidal A X
    Functor.OplaxMonoidal.δ F.mapDerivedCategory K M =
      e.inv.app (K ⊗ M) ≫ (F.leftDerivedTensorComparison.app K).app M ≫
        (e.hom.app K ⊗ₘ e.hom.app M) := by
  dsimp only
  unfold siteComparisonDerivedMonoidal
  exact (siteComparisonDerivedMonoidal_exists A X).choose_spec K M

/-- The canonical derived tensor comparison of the comparison inverse image.
It is obtained by deriving the oplax structure conjugate to restriction of sheaves;
representable flatness makes that structure strong monoidal. -/
@[irreducible]
noncomputable def siteComparisonTensorIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (Etale.derivedTensor A X).obj K ⋙ (comparisonUpperStar A X).mapDerivedCategory ≅
      (comparisonUpperStar A X).mapDerivedCategory ⋙
        (derivedTensor A X).obj ((comparisonUpperStar A X).mapDerivedCategory.obj K) := by
  let F := comparisonUpperStar A X
  let : F.mapDerivedCategory.Monoidal := siteComparisonDerivedMonoidal A X
  exact NatIso.ofComponents
    (fun M ↦ (Functor.Monoidal.μIso F.mapDerivedCategory K M).symm)
    (fun f ↦ (Functor.OplaxMonoidal.δ_natural_right F.mapDerivedCategory K f).symm)

/-- The specified comparison is the transpose of pullback of evaluation, using the
canonical tensor comparison. It is defined on all ambient complexes; invertibility
requires hypotheses and is a separate assertion. -/
@[irreducible]
noncomputable def siteComparisonEvaluationHom
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [Abelian.HasFunctorialFlatResolution A]
    (X : Scheme.{u}) [(comparisonUpperStar A X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology A)) :
    (comparisonUpperStar A X).mapDerivedCategory.obj
        (((Etale.derivedHom A X).obj (op K)).obj M) ⟶
      ((derivedHom A X).obj
        (op ((comparisonUpperStar A X).mapDerivedCategory.obj K))).obj
          ((comparisonUpperStar A X).mapDerivedCategory.obj M) :=
  let F := (comparisonUpperStar A X).mapDerivedCategory
  let : F.Monoidal := siteComparisonDerivedMonoidal A X
  (Functor.LaxMonoidal.ihomComparison F K).app M

end AlgebraicGeometry.ProEtale

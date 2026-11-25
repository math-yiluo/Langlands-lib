/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.InternalScalarPullbackNormalizationData
import WeilConjectures.CategoryTheory.DerivedCategory.CochainHomotopyComparison

/-! # Existence of normalized section scalar comparisons

The universal scalar counit is transported from cochains to homotopy complexes
and compared with the fixed internal scalar functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] SheafOfModules.ScalarDerivedPair.extension_additive
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
open CategoryTheory.InternalAbelianSheafModule
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj TensorProduct ChangeOfRings
namespace AlgebraicGeometry.ProEtale.QuotientChange
variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ' T)]

private theorem complex_comparison_eq
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive] (H : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ H ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (P : CochainComplex A ℤ) :
    H.map ((DerivedCategory.quotientCompQhIso A).inv.app P) ≫
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((E.mapHomotopyCategoryFactors (.up ℤ)).hom.app P) ≫
        (DerivedCategory.quotientCompQhIso B).hom.app
          ((E.mapHomologicalComplex (.up ℤ)).obj P) =
      ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  change H.map (𝟙 _) ≫ ε.app _ ≫ DerivedCategory.Qh.map (𝟙 _) ≫ 𝟙 _ = _
  erw [H.map_id, DerivedCategory.Qh.map_id]
  erw [Category.id_comp, Category.comp_id, Category.comp_id]
  rfl

private theorem complex_leftDerived_unique
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (E : A ⥤ B) [E.Additive]
    (H K : DerivedCategory A ⥤ DerivedCategory B)
    (ε : DerivedCategory.Qh ⋙ H ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (δ : DerivedCategory.Qh ⋙ K ⟶ E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso A (.up ℤ))]
    [K.IsLeftDerivedFunctor δ (HomotopyCategory.quasiIso A (.up ℤ))]
    (P : CochainComplex A ℤ) :
    (Functor.leftDerivedUnique K H ε δ
        (HomotopyCategory.quasiIso A (.up ℤ))).hom.app (DerivedCategory.Q.obj P) ≫
      δ.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) =
        ε.app ((HomotopyCategory.quotient A (.up ℤ)).obj P) := by
  have h := Functor.leftDerivedNatTrans_app H K ε δ
    (HomotopyCategory.quasiIso A (.up ℤ)) (𝟙 _)
    ((HomotopyCategory.quotient A (.up ℤ)).obj P)
  simp only [NatTrans.id_app, Category.comp_id] at h
  exact h

private theorem compute_eq_scalarCounit (a : Λ ⟶ Λ') [IsMonHom a] (T : Scheme.{u})
    (P : CochainComplex (Modules Λ T) ℤ) :
    compute a T P = (scalarCounit a T).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P) :=
  complex_comparison_eq (extension a T) (D a T) (scalarCounit a T) P

/-- The section scalar comparison and its normalized counit equations exist.
(1);
Stacks Tags 03EK, 06YY, 07A6 (auxiliary; not a blueprint node).
Proof: use the normalized internal section scalar adjunction, transport its left-derived
counit through the homotopy quotient, and identify its component with `compute`.
The extension comparison is normalized on balanced local generators and the K-flat
representative equation is the defining universal-counit square. -/
theorem internal_section_scalar_normalization_exists (a : Λ ⟶ Λ') [IsMonHom a]
    (T : Scheme.{u}) :
    ∃ s : SectionScalarComparison a T, SectionScalarNormalized a T s := by
  obtain ⟨pair, restriction, hr, ordinary, ho, _, LF, εc, hLF, _, _, _, _, _,
    derived, hd, _⟩ :=
    internal_section_scalar_adjunction (Scheme.ProEt.topology T) (coefficientMap a T)
  obtain ⟨εh, hLFh, hεh⟩ :=
    exists_homotopy_leftDerived_comparison (extension a T) LF εc hLF
  have := hLFh
  have hD : (D a T).IsLeftDerivedFunctor (scalarCounit a T)
      (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)) := by
    unfold scalarCounit D
    change (extension a T).leftDerivedFunctor.IsLeftDerivedFunctor
      (extension a T).leftDerivedFunctorCounit
      (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ))
    infer_instance
  let e : D a T ≅ LF := Functor.leftDerivedNatIso (D a T) LF
    (scalarCounit a T) εh (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ)) (Iso.refl _)
  let s : SectionScalarComparison a T :=
    { pair := pair
      restriction := restriction
      ordinary := ordinary
      derived := Functor.isoWhiskerRight e
        (ModuleRingedComparison.derivedEquivalence Λ' T).functor ≪≫ derived }
  refine ⟨s, hr, ho, ?_⟩
  intro P hP hflat
  have he : e.hom.app (DerivedCategory.Q.obj P) ≫ εc.app P = compute a T P := by
    have hε := hεh P
    change εh.app _ = LF.map (𝟙 _) ≫ εc.app P ≫ 𝟙 _ at hε
    erw [LF.map_id, Category.id_comp, Category.comp_id] at hε
    rw [← hε, compute_eq_scalarCounit]
    unfold e
    change (Functor.leftDerivedUnique LF (D a T) (scalarCounit a T) εh
      (HomotopyCategory.quasiIso (Modules Λ T) (.up ℤ))).hom.app
        (DerivedCategory.Q.obj P) ≫ εh.app _ = _
    exact complex_leftDerived_unique (extension a T) (D a T) LF (scalarCounit a T) εh P
  dsimp only [s]
  rw [← he, Functor.map_comp, Category.assoc]
  erw [hd P hP hflat]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.QuotientChange

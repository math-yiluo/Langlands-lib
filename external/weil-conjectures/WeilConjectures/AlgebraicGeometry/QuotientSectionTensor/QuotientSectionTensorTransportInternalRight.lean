/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTransportInternalData
public import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTotalSquare
import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorTotalLocalizationPath

/-! # Ordinary-side scalar tensor evaluation

## References

* Stacks Project, Tag 03EL, extension of scalars and pure sections
* Tags 06YY and 07A4, signed total constituents
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency.types false
set_option cleanup.letToHave false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient
open ModuleRingedComparison

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ' T)]

attribute [local irreducible] ModuleRingedComparison.tensor tensorComparison qTensor
  totalComparison totalScalar QuotientChange.compute Mod.extendScalars
  CondensedRing.internalScalarMonoidal Mod.monoidalCategoryStruct
  Localization.Monoidal.tensorBifunctor
  HomologicalComplex₂.total Mod.inducingFunctorData
  InternalAbelianSheafModule.sectionModuleEquivalence SheafOfModules.monoidalCategory

private theorem paste_input_path {C : Type*} [Category C]
    {A B D E F G H : C} {a : A ⟶ B} {b : B ⟶ D} {c : D ⟶ E}
    {d : E ⟶ F} {e : F ⟶ G} {f : G ⟶ H} {r : A ⟶ H}
    (h : a ≫ b ≫ c ≫ d ≫ e ≫ f = r) :
    (a ≫ b ≫ c) ≫ d ≫ e ≫ f = r := by
  simpa only [Category.assoc] using h

private theorem internal_right_total_tensor_map
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    [∀ X : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules Λ X)]
    (Z : Scheme.{u}) {P P' Q Q' : CochainComplex (ModuleRingedComparison.modules Λ Z) ℤ}
    (f : P ⟶ P') (g : Q ⟶ Q') :
    (ModuleRingedComparison.totalTensor Λ Z).map (Prod.mkHom f g) = f ⊗ₘ g := by
  change (f ▷ _) ≫ (_ ◁ g) = f ⊗ₘ g
  exact (MonoidalCategory.tensorHom_def f g).symm

-- Retain large derived tensor terms while identifying the localized path wrappers.
/-- Evaluate the ordinary scalar-total side on all internal complexes. -/
theorem section_tensor_transport_internal_right (T : Scheme.{u})
    (c : ScalarSectionData a T) (hc : ScalarSectionNormalized a T c)
    [PreservesColimitsOfSize.{0, 0} c.model.E]
    (e : (Functor.postcompose₂.obj c.model.E).obj (curriedTensor (modules Λ T)) ⟶
        (((Functor.whiskeringLeft₂ _).obj c.model.E).obj c.model.E).obj
          (curriedTensor (modules Λ' T)))
    (he : ∀ (M N : modules Λ T) (W : T.ProEtᵒᵖ) (m : M.val.obj W)
      (n : N.val.obj W) (s : (ring Λ' T).obj.obj W),
      (((e.app M).app N).val.app W)
          (sectionScalarElement a T c (M ⊗ N) W
            (sectionPureTensor Λ T M N W m n) s) =
        sectionPureTensor Λ' T (c.model.E.obj M) (c.model.E.obj N) W
          (sectionScalarElement a T c M W m 1)
          (sectionScalarElement a T c N W n s)) :
    ∀ P Q : CochainComplex (Modules Λ T) ℤ,
      let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
      let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
      scalarTensorSectionInput a T c P Q ≫
        c.model.T.map ((qTensor Λ T).app (EP, EQ)) ≫
          c.model.ε.app ((totalTensor Λ T).obj (EP, EQ)) ≫
          DerivedCategory.Q.map
            (HomologicalComplex.mapBifunctorComparison e (.up ℤ) EP EQ) =
        scalarTensorSectionPath a T c P Q := by
  intro P Q
  let EP := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj P
  let EQ := ((equivalence Λ T).functor.mapHomologicalComplex (.up ℤ)).obj Q
  let g := HomologicalComplex.mapBifunctorComparison e (.up ℤ) EP EQ
  have hg : ∀ (i j k : ℤ) (h : i + j = k),
      c.model.E.map (HomologicalComplex.ιTensorObj EP EQ i j k h) ≫ g.f k =
        (e.app ((equivalence Λ T).functor.obj (P.X i))).app
            ((equivalence Λ T).functor.obj (Q.X j)) ≫
          HomologicalComplex.ιTensorObj
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj EP)
            ((c.model.E.mapHomologicalComplex (.up ℤ)).obj EQ) i j k h := by
    intro i j k h
    exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      e (.up ℤ) EP EQ i j k h
  have hord := section_tensor_total_scalar_square a T c hc e he P Q g hg
  have hpath := section_tensor_total_localization_path a T c hc P Q g hord
  dsimp only at hpath
  dsimp only [scalarTensorSectionInput]
  apply paste_input_path
  refine hpath.trans ?_
  dsimp only [scalarTensorSectionPath, localizedTotalComparison,
    sectionLocalizationComparison, Functor.mapHomologicalComplexCompIso,
    Iso.trans_hom, Iso.symm_hom, NatIso.mapHomologicalComplex,
    Iso.refl_hom, Iso.refl_inv, NatTrans.comp_app]
  simp only [sectionTotalComparison_eq, Functor.map_comp, Category.assoc,
    NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.comp_id,
    internal_right_total_tensor_map]
  rfl

end AlgebraicGeometry.ProEtale.QuotientSectionTensor

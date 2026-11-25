/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ComapUpperStarIsoMate
public import WeilConjectures.AlgebraicGeometry.IntegralReductionTensor
public import WeilConjectures.AlgebraicGeometry.IntegralResiduePullFlatModelMateNormalized
public import WeilConjectures.AlgebraicGeometry.IntegralResiduePullOrdinaryUnit
public import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import WeilConjectures.CategoryTheory.DerivedCategory.KFlatAcyclic

/-! # The canonical restricted residue tensor presentation

Source: Bhatt--Scholze, Lemma 6.5.9(3), and derived scalar extension.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]
  [MonoidalCategory C] [MonoidalClosed C] [MonoidalPreadditive C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]

instance genericTensorLeft_preservesKFlatQuasiIso (B : C) :
    (tensorLeft B).PreservesKFlatQuasiIso := by
  refine Functor.PreservesKFlatQuasiIso.mk' _ ?_
  intro K hK hKa
  exact (CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa B).of_iso
    ((NatIso.mapHomologicalComplex (BraidedCategory.tensorLeftIsoTensorRight B) _).app K).symm

@[irreducible] noncomputable def homotopyTensorSingleIso (B : C) :
    tensorLeft ((HomotopyCategory.quotient C (.up ℤ)).obj
      ((HomologicalComplex.single C (.up ℤ) 0).obj B)) ≅
        (tensorLeft B).mapHomotopyCategory (.up ℤ) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj B
  let e : tensorLeft P ≅ (tensorLeft B).mapHomologicalComplex (.up ℤ) :=
    CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B
  let pre : q ⋙ tensorLeft (q.obj P) ≅
      q ⋙ (tensorLeft B).mapHomotopyCategory (.up ℤ) :=
    (Functor.Monoidal.commTensorLeft q P).symm ≪≫
      Functor.isoWhiskerRight e q ≪≫ (tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)
  exact (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ _).obj q)).preimageIso pre

/-- The canonical comparison from a degree-zero derived object to its homotopy
representative. This is the standard single/quotient comparison, kept as one map.
Source: the single-object and quotient localization comparisons.
(auxiliary; not a blueprint node) -/
@[irreducible] noncomputable def homotopySingleComparisonIso (B : C) :
    (DerivedCategory.singleFunctor C 0).obj B ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj B)) :=
  (DerivedCategory.singleFunctorIsoCompQ C 0).app B ≪≫
    (DerivedCategory.quotientCompQhIso C).symm.app _

@[irreducible] noncomputable def derivedTensorSingleIso (B : C) :
    (tensorLeft B).leftDerivedFunctor ≅
      tensorLeft ((DerivedCategory.singleFunctor C 0).obj B) := by
  let P := (HomotopyCategory.quotient C (.up ℤ)).obj
    ((HomologicalComplex.single C (.up ℤ) 0).obj B)
  let eB : (DerivedCategory.singleFunctor C 0).obj B ≅ DerivedCategory.Qh.obj P :=
    homotopySingleComparisonIso B
  exact Functor.leftDerivedNatIso (tensorLeft B).leftDerivedFunctor
      (tensorLeft (DerivedCategory.Qh.obj P)) (tensorLeft B).leftDerivedFunctorCounit
      (DerivedCategory.tensorLeftQhObjCounit P) (HomotopyCategory.quasiIso C (.up ℤ))
      (Functor.isoWhiskerRight (homotopyTensorSingleIso B).symm DerivedCategory.Qh) ≪≫
    (curriedTensor (DerivedCategory C)).mapIso eB.symm

/-- The fixed braiding used by the derived tensor comparisons.
Its data are the existing derived monoidal braiding; the name lets the
presentation and model use exactly the same instance.
Source: the canonical braided structure on the derived tensor product.
(auxiliary; not a blueprint node) -/
@[instance_reducible] noncomputable def derivedTensorPresentationBraiding :
    BraidedCategory (DerivedCategory C) :=
  DerivedMonoidal.braidedCategory' (DerivedCategory.Qh (C := C))
    (HomotopyCategory.quasiIso C (.up ℤ))

@[irreducible] noncomputable def derivedTensorPresentationIso (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))] :
    H ≅ tensorRight ((DerivedCategory.singleFunctor C 0).obj B) := by
  let : BraidedCategory (DerivedCategory C) := derivedTensorPresentationBraiding
  exact Functor.leftDerivedUnique (tensorLeft B).leftDerivedFunctor H ε
      (tensorLeft B).leftDerivedFunctorCounit (HomotopyCategory.quasiIso C (.up ℤ)) ≪≫
    derivedTensorSingleIso B ≪≫ BraidedCategory.tensorLeftIsoTensorRight _

noncomputable section NormalizationAPI

attribute [local instance] derivedTensorPresentationBraiding

/-- The tensor presentation is normalized by its balanced tensor counit.

Cancel the braiding and the two standard single comparisons. The defining
left-derived natural-transformation equation then gives the stated counit.

Source: Bhatt--Scholze, Remark 6.8.15; canonical derived tensor comparison.
(auxiliary; not a blueprint node) -/
theorem derivedTensorPresentationIso_fac (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : HomotopyCategory C (.up ℤ)) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Qh.obj P) ≫
      (β_ ((DerivedCategory.singleFunctor C 0).obj B) (DerivedCategory.Qh.obj P)).inv ≫
      (homotopySingleComparisonIso B).hom ▷ DerivedCategory.Qh.obj P ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj B)) P =
      ε.app P ≫ DerivedCategory.Qh.map ((homotopyTensorSingleIso B).inv.app P) := by
  simp only [derivedTensorPresentationIso, derivedTensorSingleIso, Iso.trans_hom,
    NatTrans.comp_app, BraidedCategory.tensorLeftIsoTensorRight,
    Category.assoc, Iso.hom_inv_id_assoc]
  simp only [Functor.mapIso_hom, Iso.symm_hom,
    curriedTensor_map_app]
  rw [← comp_whiskerRight_assoc, Iso.inv_hom_id, id_whiskerRight, Category.id_comp]
  change _ ≫ _ ≫ (DerivedCategory.tensorLeftQhObjCounit
    ((HomotopyCategory.quotient C (.up ℤ)).obj
        ((HomologicalComplex.single C (.up ℤ) 0).obj B))).app P = _
  simp only [Functor.leftDerivedNatIso_hom, Functor.leftDerivedNatTrans_app,
    Functor.leftDerivedUnique, Functor.leftDerivedNatTrans_app_assoc,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp]

end NormalizationAPI

end CategoryTheory

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C]
  [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
  [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
  (φ : R ⟶ S) [IsMonHom φ]

/-- Restricted derived scalar extension is right tensor with the degree-zero
restricted regular module, using the canonical balanced tensor counit. -/
@[irreducible] noncomputable def residueDerivedTensorIso :
    (extendScalars φ).leftDerivedFunctor ⋙ (comap φ).mapDerivedCategory ≅
      MonoidalCategory.tensorRight ((DerivedCategory.singleFunctor (Mod C R) 0).obj
        ((comap φ).obj (regular S))) := by
  letI := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor φ
  exact CategoryTheory.derivedTensorPresentationIso _ _ (Mod.tensorPresentationDerivedCounit φ)

end CategoryTheory.Mod

attribute [local instance] _root_.instEssentiallySmallProfinite_weilConjectures

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] sheafBraidedCategory

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type) [NormedField E] [NormedAlgebra ℚ_[ℓ] E]

end AlgebraicGeometry.ProEtale.CondensedRing

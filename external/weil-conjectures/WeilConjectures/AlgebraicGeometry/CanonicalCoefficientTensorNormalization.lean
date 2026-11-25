/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.IntegralResidueTensorPullPresentation
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientPullbackData
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor

/-! # Computation normalization of the canonical coefficient tensor presentation

Source: Stacks 06YY and 0G7E; the scalar comparison in the rational proper
base-change proof, paragraph (1)
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] AlgebraicGeometry.ProEtale.upperStarFromPoint
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.mapDerivedCategory

universe v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory

section CochainNormalization
variable {C : Type u} [Category.{v} C] [Abelian C]
  [IsGrothendieckAbelian.{v} C] [MonoidalCategory C] [MonoidalClosed C]
  [MonoidalPreadditive C] [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] derivedTensorPresentationBraiding

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem single_inv_quotient (B : C) (K : CochainComplex C ℤ) :
    (homotopyTensorSingleIso B).inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
    ((tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)).inv.app K ≫
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B).inv.app K) ≫
      Functor.LaxMonoidal.μ (HomotopyCategory.quotient C (.up ℤ))
        ((HomologicalComplex.single C (.up ℤ) 0).obj B) K := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let P := (HomologicalComplex.single C (.up ℤ) 0).obj B
  let e : tensorLeft P ≅ (tensorLeft B).mapHomologicalComplex (.up ℤ) :=
    CochainComplex.map₂HomologicalComplexObjSingleIso (curriedTensor C) B
  let pre := (Functor.Monoidal.commTensorLeft q P).symm ≪≫
    Functor.isoWhiskerRight e q ≪≫ (tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)
  have h : Functor.whiskerLeft q (homotopyTensorSingleIso B).inv = pre.inv := by
    unfold homotopyTensorSingleIso
    exact (Functor.FullyFaithful.ofFullyFaithful
      ((Functor.whiskeringLeft _ _ _).obj q)).map_preimage _
  have ha := NatTrans.congr_app h K
  simpa only [pre, e, q, P, Functor.whiskerLeft_app, Iso.trans_inv, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
    Functor.Monoidal.commTensorLeft_hom_app, Category.assoc] using ha

omit [Abelian.HasFunctorialFlatResolution C] in
private theorem tensor_single_braiding (B : C) (P : CochainComplex C ℤ) :
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C) B P).inv ≫
      (β_ ((CochainComplex.singleFunctor C 0).obj B) P).hom ≫
      (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P).hom =
      (NatTrans.mapHomologicalComplex
        (BraidedCategory.tensorLeftIsoTensorRight B).hom (.up ℤ)).app P := by
  change (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C) B P).inv ≫
    (CochainComplex.Monoidal.braiding _ P).hom ≫ _ = _
  simp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_hom, Iso.symm_hom,
    CochainComplex.Monoidal.braiding,
    Category.assoc, Iso.hom_inv_id_assoc]
  ext n : 1
  simp only [HomologicalComplex.comp_f,
    CochainComplex.mapBifunctorSingle₁Iso_inv_f, NatTrans.mapHomologicalComplex_app_f,
    Category.assoc]
  erw [HomologicalComplex₂.ιTotal_map_assoc]
  change (HomologicalComplex.singleObjXSelf (.up ℤ) 0 B).inv ▷ P.X n ≫
    (β_ _ (P.X n)).hom ≫
      HomologicalComplex.ιMapBifunctor _ P (curriedTensor C).flip (.up ℤ) 0 n n _ ≫
        (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C).flip B P).hom.f n =
    (β_ B (P.X n)).hom
  rw [BraidedCategory.braiding_naturality_left_assoc]
  have hi := HomologicalComplex.congr_hom
    (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C).flip B P).inv_hom_id n
  simp only [HomologicalComplex.comp_f, CochainComplex.mapBifunctorSingle₁Iso_inv_f,
    HomologicalComplex.id_f, Category.assoc] at hi
  exact (congrArg (fun k ↦ (β_ B (P.X n)).hom ≫ k) hi).trans (Category.comp_id _)

private theorem presentation_cochain_fac (B : C)
    (H : DerivedCategory C ⥤ DerivedCategory C)
    (ε : DerivedCategory.Qh ⋙ H ⟶
      (tensorLeft B).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    [H.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ))]
    (P : CochainComplex C ℤ) :
    (derivedTensorPresentationIso B H ε).hom.app (DerivedCategory.Q.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P ((CochainComplex.singleFunctor C 0).obj B) ≫
      DerivedCategory.Q.map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P).hom =
      ε.app ((HomotopyCategory.quotient C (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map
          (((tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)).inv.app P) ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex
            (BraidedCategory.tensorLeftIsoTensorRight B).hom (.up ℤ)).app P) := by
  let q := HomotopyCategory.quotient C (.up ℤ)
  let PB := (CochainComplex.singleFunctor C 0).obj B
  have h := derivedTensorPresentationIso_fac B H ε (q.obj P)
  have he : (homotopySingleComparisonIso B).hom = 𝟙 _ := by
    unfold homotopySingleComparisonIso
    change (𝟙 _) ≫ (𝟙 _) = 𝟙 _
    exact Category.id_comp _
  rw [he, id_whiskerRight, Category.id_comp] at h
  have h' := congrArg (fun z ↦ z ≫ DerivedCategory.Qh.map (β_ (q.obj PB) (q.obj P)).hom ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P).hom) h
  simp only [Category.assoc] at h'
  have hb : (β_ (DerivedCategory.Qh.obj (q.obj PB))
      (DerivedCategory.Qh.obj (q.obj P))).hom ≫
      Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj P) (q.obj PB) =
      Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj PB) (q.obj P) ≫
        DerivedCategory.Qh.map (β_ (q.obj PB) (q.obj P)).hom :=
    DerivedMonoidal.braiding_hom_μ DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) (q.obj PB) (q.obj P)
  erw [← reassoc_of% hb] at h'
  erw [Iso.inv_hom_id_assoc] at h'
  erw [single_inv_quotient] at h'
  have hfac : ((tensorLeft B).mapHomotopyCategoryFactors (.up ℤ)).inv.app P = 𝟙 _ := rfl
  have hμ : Functor.LaxMonoidal.μ q PB P = 𝟙 _ := rfl
  simp only [hfac, Category.id_comp, Functor.map_comp, Category.assoc] at h'
  erw [hμ, DerivedCategory.Qh.map_id, Category.id_comp] at h'
  have hμQ : Functor.LaxMonoidal.μ DerivedCategory.Q P PB =
      Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj P) (q.obj PB) := by
    change (𝟙 (DerivedCategory.Q.obj P) ⊗ₘ 𝟙 (DerivedCategory.Q.obj PB)) ≫
      (Functor.LaxMonoidal.μ DerivedCategory.Qh (q.obj P) (q.obj PB) ≫
        (DerivedCategory.Qh (C := C)).map (𝟙 (q.obj (P ⊗ PB)))) ≫ 𝟙 _ = _
    simp only [id_tensorHom_id, Category.comp_id, Category.id_comp]
    erw [DerivedCategory.Qh.map_id, Category.comp_id]
  rw [hμQ, hfac, DerivedCategory.Qh.map_id]
  erw [Category.id_comp]
  change _ = ε.app (q.obj P) ≫ DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      (BraidedCategory.tensorLeftIsoTensorRight B).hom (.up ℤ)).app P)
  change _ = ε.app (q.obj P) ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₁Iso (curriedTensor C) B P).inv ≫
    DerivedCategory.Q.map (β_ PB P).hom ≫
    DerivedCategory.Q.map (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor C) B P).hom at h'
  simp only [← Functor.map_comp] at h'
  dsimp only [PB] at h'
  erw [tensor_single_braiding] at h'
  exact h'

end CochainNormalization

private theorem tensorPresentation_app
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {R S : A} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ]
    (P : HomotopyCategory (Mod A R) (.up ℤ)) :
    (Mod.tensorPresentationDerivedCounit φ).app P =
      (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctorCounit.app P) ≫
      (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
        (((Mod.extendScalars φ).mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((Mod.tensorPresentationHomotopyIso φ).hom.app P) := by
  dsimp only [Mod.tensorPresentationDerivedCounit, Mod.extendComapCounit,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app]
  simp only [DerivedCategory.Qh.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp, Category.id_comp, Category.id_comp]

private theorem exactFactorsh_app
    {A E : Type*} [Category* A] [Category* E] [Abelian A] [Abelian E]
    [HasDerivedCategory A] [HasDerivedCategory E]
    (F : A ⥤ E) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex A ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 _) ≫ F.mapDerivedCategoryFactors.hom.app P ≫
    𝟙 _ ≫ DerivedCategory.Qh.map (𝟙 _) = _
  erw [F.mapDerivedCategory.map_id (DerivedCategory.Q.obj P),
    DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ _).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P))]
  simp only [Category.id_comp]
  exact Category.comp_id _

private theorem residue_cochain_fac
    {A : Type u} [Category.{v} A] [Abelian A] [MonoidalCategory A]
    [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
    [IsGrothendieckAbelian.{v} A] [Abelian.HasFunctorialFlatResolution A]
    {R S : A} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] (P : CochainComplex (Mod A R) ℤ) :
    (Mod.residueDerivedTensorIso φ).hom.app (DerivedCategory.Q.obj P) ≫
      Functor.LaxMonoidal.μ DerivedCategory.Q P
        ((CochainComplex.singleFunctor (Mod A R) 0).obj
          ((Mod.comap φ).obj (Mod.regular S))) ≫
      DerivedCategory.Q.map
        (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor (Mod A R))
          ((Mod.comap φ).obj (Mod.regular S)) P).hom =
    (Mod.comap φ).mapDerivedCategory.map
        ((Mod.extendScalars φ).leftDerivedFunctorCounit.app
          ((HomotopyCategory.quotient _ _).obj P)) ≫
      (Mod.comap φ).mapDerivedCategoryFactors.hom.app
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso
          (Mod.extendComapTensorIso φ ≪≫
            BraidedCategory.tensorLeftIsoTensorRight ((Mod.comap φ).obj (Mod.regular S)))
          (.up ℤ)).hom.app P) := by
  let := Mod.tensorPresentationDerivedCounit_isLeftDerivedFunctor φ
  unfold Mod.residueDerivedTensorIso
  rw [presentation_cochain_fac, tensorPresentation_app]
  simp only [Category.assoc]
  change (Mod.comap φ).mapDerivedCategory.map _ ≫
    (Mod.comap φ).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj
        (((Mod.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj P)) ≫ _ = _
  rw [exactFactorsh_app]
  have hfac : ((tensorLeft ((Mod.comap φ).obj (Mod.regular S))).mapHomotopyCategoryFactors
      (.up ℤ)).inv.app P = 𝟙 _ := rfl
  rw [hfac, DerivedCategory.Qh.map_id]
  erw [Category.id_comp]
  simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.trans_hom, NatTrans.mapHomologicalComplex_comp, NatTrans.comp_app]
  rw [DerivedCategory.Q.map_comp]
  rfl

end CategoryTheory

namespace AlgebraicGeometry.ProEtale.QuotientChange

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]

private theorem compute_eq_counit (T : Scheme.{u}) (P : CochainComplex (Modules R T) ℤ) :
    compute a T P = (scalarCounit a T).app
      ((HomotopyCategory.quotient _ _).obj P) := by
  unfold compute
  have hq : (DerivedCategory.quotientCompQhIso (Modules R T)).inv.app P = 𝟙 _ := rfl
  have hq' : (DerivedCategory.quotientCompQhIso (Modules S T)).hom.app
      (((extension a T).mapHomologicalComplex (.up ℤ)).obj P) = 𝟙 _ := rfl
  have hf : (((extension a T).mapHomotopyCategoryFactors (.up ℤ)).hom.app P) = 𝟙 _ := rfl
  rw [hq, hq', hf]
  unfold D
  erw [(extension a T).leftDerivedFunctor.map_id (DerivedCategory.Q.obj P),
    DerivedCategory.Qh.map_id ((HomotopyCategory.quotient _ _).obj
      (((extension a T).mapHomologicalComplex (.up ℤ)).obj P))]
  simp only [Category.id_comp]
  erw [Category.comp_id, Category.comp_id]

private theorem pull_unit_eq (A : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Functor.Monoidal.εIso (CondensedRing.upperStar A f)).inv =
      (by
        letI := CondensedRing.residueOrdinaryUpperStarMonoidal A f
        exact (Functor.Monoidal.εIso (CondensedRing.upperStar A f)).inv) := by
  change (Mod.extendScalars (condensedPullbackHom A f)).map (𝟙 _) ≫ _ = _
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

private theorem regularPullback₀_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    RestrictedCoefficientMate.regularPullback₀ a f =
      CondensedRing.residueOrdinaryRestrictedRegularPullIso R S a f := by
  apply Iso.ext
  unfold RestrictedCoefficientMate.regularPullback₀
    CondensedRing.residueOrdinaryRestrictedRegularPullIso
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom]
  rw [pull_unit_eq S f]

/-- The canonical balanced tensor presentation, including its fixed symmetry.
Source: Stacks 06YY, 0G7E
(auxiliary; not a blueprint node). -/
def canonicalCoefficientTensorNormalization (T : Scheme.{u}) : TensorNormalization a T := by
  letI : SymmetricCategory (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
    { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} T
      symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
        (sheafSymmetricCategory T) M N }
  refine
    { ordinary := Mod.extendComapTensorIso (coefficientMap a T) ≪≫
        BraidedCategory.tensorLeftIsoTensorRight (B₀ a T)
      ordinary_hom := ?_
      derived := ?_ }
  · intro M
    rfl
  · unfold D
    exact Mod.residueDerivedTensorIso (coefficientMap a T)

/-- The canonical balanced tensor comparison satisfies the universal computation
normalization, and the two exact single-object pullback constructions agree.

Source: Stacks 06YY and 0G7E; the canonical scalar tensor and inverse-image
comparisons in rational proper base change, paragraph (1)
(auxiliary; not a blueprint node).

Proof. Apply derivedTensorPresentationIso_fac to the quotient of a complex P.
Naturality of the braiding moves the coefficient single-object comparison across
Qh's tensor comparison. Compatibility of Qh with the braiding changes the
coefficient-first expression into the coefficient-last expression. The ordinary
single-tensor comparisons identify the remaining composite with termwise tensor
on P. Expanding the balanced counit gives compute followed by exact restriction
and the ordinary balanced map, which is precisely TensorNormalized. No flatness
of P or of the coefficient is used. For the second assertion, expand the exact
single/left-derived comparison through the exact mapDerivedCategory comparison.
For the ordinary unit comparison, precompose with the balanced scalar-extension
coprojection. The standard composite monoidal structure and the transported
residue monoidal structure both give multiplication by the pulled scalar: their
unit maps send a local scalar s to 1 tensor s, and their inverses multiply.
The coprojection is epi,
so these unit maps agree. The ordinary restriction/pullback maps are already the
same specified comapUpperStarIso. Both derived constructions therefore consist
of the same localization factor, single factor and ordinary restricted unit map.
Functoriality of Q combines the last two factors. -/
theorem canonicalCoefficientTensorNormalization_normalized :
    (∀ T : Scheme.{u},
      TensorNormalized a T (canonicalCoefficientTensorNormalization a T)) ∧
    (∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      RestrictedCoefficientMate.regularPullback a f =
      (by
        unfold L CondensedRing.moduleObjectDerivedPullback
        let e := CondensedRing.residueRestrictedRegularPullIso R S a f
        unfold CondensedRing.residueExchangeUpperStar at e
        run_tac Lean.Elab.Tactic.withMainContext do
          let e ← Lean.Meta.getLocalDeclFromUserName `e
          (← Lean.Elab.Tactic.getMainGoal).assign e.toExpr
          Lean.Elab.Tactic.replaceMainGoal [])) := by
  constructor
  · intro T P
    let : SymmetricCategory (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) :=
      { toBraidedCategory := sheafBraidedCategory Ab.{u + 1} T
        symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
          (sheafSymmetricCategory T) M N }
    have h := residue_cochain_fac (coefficientMap a T) P
    unfold canonicalCoefficientTensorNormalization
    dsimp only [id]
    unfold D singleTensor
    erw [h]
    rw [compute_eq_counit]
    rfl
  · intro X Y f
    unfold L CondensedRing.moduleObjectDerivedPullback
    unfold RestrictedCoefficientMate.regularPullback
    rw [CondensedRing.residueRestrictedRegularPullIso_def]
    dsimp only [id]
    apply Iso.ext (C := DerivedCategory (Modules R X))
    simp only [Iso.trans_hom, Iso.app_hom,
      Functor.singleFunctorCompLeftDerivedFunctorIso, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rw [CategoryTheory.Functor.mapDerivedCategorySingleFunctor_hom_app_eq]
    rw [regularPullback₀_eq a f]
    simp only [Category.assoc]
    rfl

end AlgebraicGeometry.ProEtale.QuotientChange

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.Finite.RingedFiniteFreeHomBaseChangeData
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.CategoryTheory.RingedKFlatModel.RingedKFlatNativeModelIdentification
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Homology.HomComplex
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.RingTheory.Flat.CategoryTheory
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all WeilConjectures.Algebra.Homology.InternalHom
import all WeilConjectures.Algebra.Homology.HomComplexComponents
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import all WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import all WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionConstraintCoherence
import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.CategoryTheory.Monoidal.Subcategory
/-! # Strong monoidality of derived scalar extension.

Source: Stacks Project, Tags 06YS, 07A4 and Categories 04VK.
(blueprint: lem-fix-ringed-scalar-tensor-monoidal). -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.MonoidalCategory WeilConjectures
attribute [local instance 2000] SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive

namespace CategoryTheory.ScalarMonoidalProof
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
  (R : Sheaf J CommRingCat.{r})
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
variable {R} {S : Sheaf J CommRingCat.{r}} (φ : R ⟶ S)
open CochainPullback
private theorem scalarGradedTensor (A : Sheaf J CommRingCat.{r})
    (X Y : GradedObject ℤ (Modules A)) : X.HasTensor Y := by
  have (I : Type r) : HasColimitsOfShape (Discrete I) (PresheafOfModules.{r}
      ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj A).obj) :=
    PresheafOfModules.hasColimitsOfShape _ _
  infer_instance
omit [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarGradedFour (A : Sheaf J CommRingCat.{r})
    (W X Y Z : GradedObject ℤ (Modules A)) :
    GradedObject.HasTensor₄ObjExt W X Y Z := inferInstance
omit [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarGradedLeft (A : Sheaf J CommRingCat.{r})
    (X Y Z : GradedObject ℤ (Modules A)) :
    GradedObject.HasGoodTensor₁₂Tensor X Y Z := inferInstance
omit [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem scalarGradedRight (A : Sheaf J CommRingCat.{r})
    (X Y Z : GradedObject ℤ (Modules A)) :
    GradedObject.HasGoodTensorTensor₂₃ X Y Z := inferInstance
attribute [local instance] scalarGradedTensor scalarGradedFour scalarGradedLeft scalarGradedRight

private def scalarModuleCore
    (d : SheafOfModules.ScalarExtensionConstraintData R S φ) :
    (extensionFunctor φ).CoreMonoidal := by
  refine
    { εIso := d.unitIso.symm
      μIso M N := (d.tensorIso M N).symm
      μIso_hom_natural_left := ?_
      μIso_hom_natural_right := ?_
      associativity := ?_
      left_unitality := ?_
      right_unitality := ?_ }
  · intro M M' f N
    change SheafOfModules.changeOfRingsHom φ M f ▷ SheafOfModules.changeOfRings φ N ≫
        (d.tensorIso M' N).inv = (d.tensorIso M N).inv ≫
          SheafOfModules.changeOfRingsHom φ (M ⊗ N) (f ▷ N)
    have hn := d.natural M N M' N f (𝟙 N)
    rw [(extensionFunctor_laws φ).1 N] at hn
    simp only [tensorHom_id] at hn
    apply (cancel_mono (d.tensorIso M' N).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  · intro N N' M f
    change SheafOfModules.changeOfRings φ M ◁ SheafOfModules.changeOfRingsHom φ N f ≫
        (d.tensorIso M N').inv = (d.tensorIso M N).inv ≫
          SheafOfModules.changeOfRingsHom φ (M ⊗ N) (M ◁ f)
    have hn := d.natural M N M N' (𝟙 M) f
    rw [(extensionFunctor_laws φ).1 M] at hn
    simp only [id_tensorHom] at hn
    apply (cancel_mono (d.tensorIso M N').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  · exact d.lax_associativity
  · exact fun X ↦ (d.lax_left_unit X).symm
  · exact fun X ↦ (d.lax_right_unit X).symm

omit [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}] in
private theorem extensionUnit (M : Modules R) (U : Cᵒᵖ) (x : M.val.obj U) :
    ((extensionAdjunction φ).unit.app M).val.app U x = extensionTmul φ M U 1 x :=
  (Classical.choose_spec (extensionAdjunction_existsUnique φ)).1 M U x

private theorem extendedTotal_ext (P Q : CochainPullback.Complex R) (N : Modules S) (n : ℤ)
    (f g : (extensionFunctor φ).obj ((P ⊗ Q).X n) ⟶ N)
    (h : ∀ p q (hpq : p + q = n) (U : Cᵒᵖ)
      (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
      f.val.app U (extensionTmul φ _ U 1
        ((CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq).val.app U
          (SheafOfModules.scalarExtensionConstraintPureTensor R _ _ U x y))) =
      g.val.app U (extensionTmul φ _ U 1
        ((CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq).val.app U
          (SheafOfModules.scalarExtensionConstraintPureTensor R _ _ U x y)))) : f = g := by
  apply ((extensionAdjunction φ).homEquiv _ _).injective
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  apply SheafOfModules.tensor_ext R _ _ _ _ _
  intro U x y
  simp only [Adjunction.homEquiv_unit]
  change f.val.app U (((extensionAdjunction φ).unit.app _).val.app U _) =
    g.val.app U (((extensionAdjunction φ).unit.app _).val.app U _)
  simp only [extensionUnit J φ]
  exact h p q hpq U x y

private theorem complexScalar_generators
    (d : SheafOfModules.ScalarExtensionConstraintData R S φ)
    (P Q : CochainPullback.Complex R) (p q n : ℤ) (hpq : p + q = n) (U : Cᵒᵖ)
    (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U) :
    letI := (scalarModuleCore.{c, v, r} J φ d).toMonoidal
    letI := (extensionAdjunction φ).isLeftAdjoint
    (((extensionFunctor φ).mapCochainComplexμIso P Q).inv.f n).val.app U
      (extensionTmul φ _ U 1
        ((CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq).val.app U
        (SheafOfModules.scalarExtensionConstraintPureTensor R _ _ U x y))) =
    (CochainComplex.ιMapBifunctor ((extend φ).obj P) ((extend φ).obj Q)
        (curriedTensor (Modules S)) p q n hpq).val.app U
      (SheafOfModules.scalarExtensionConstraintPureTensor S _ _ U
        (extensionTmul φ _ U 1 x) (extensionTmul φ _ U 1 y)) := by
  let := (scalarModuleCore.{c, v, r} J φ d).toMonoidal
  let := (extensionAdjunction φ).isLeftAdjoint
  let L := extensionFunctor φ
  let ι := CochainComplex.ιMapBifunctor P Q (curriedTensor (Modules R)) p q n hpq
  let ι' := CochainComplex.ιMapBifunctor ((extend φ).obj P) ((extend φ).obj Q)
        (curriedTensor (Modules S)) p q n hpq
  have hi : L.map ι ≫ ((L.mapCochainComplexμIso P Q).inv.f n) =
      (d.tensorIso (P.X p) (Q.X q)).hom ≫ ι' := by
    have hh := HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
      (Functor.OplaxMonoidal.δNatTrans L) (.up ℤ) P Q p q n hpq
    exact hh
  have hn := congrArg (fun f ↦ f.val.app U
    (SheafOfModules.scalarExtensionConstraintPureTensor R _ _ U x y))
    ((extensionAdjunction φ).unit.naturality ι)
  change ((extensionAdjunction φ).unit.app _).val.app U (ι.val.app U _) =
    (L.map ι).val.app U (((extensionAdjunction φ).unit.app _).val.app U _) at hn
  simp only [extensionUnit J φ] at hn
  erw [hn]
  have hh := congrArg (fun f ↦ f.val.app U
    (extensionTmul φ _ U 1 (SheafOfModules.scalarExtensionConstraintPureTensor R _ _ U x y))) hi
  exact hh.trans (congrArg (ι'.val.app U) (d.insertion _ _ U x y))

end CategoryTheory.ScalarMonoidalProof

namespace CategoryTheory.ScalarMonoidalProof
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

@[reducible] private def complexMonoidal (A : Sheaf J CommRingCat.{max c v r}) :
    MonoidalCategory (CochainComplex (RingedTensorModules.{c, v, r} J A) ℤ) := by
  letI := RingedDerivedNative.gradedTensor.{c, v, r} J A
  letI := RingedDerivedNative.gradedTensorFour.{c, v, r} J A
  letI := RingedDerivedNative.gradedTensorLeft.{c, v, r} J A
  letI := RingedDerivedNative.gradedTensorRight.{c, v, r} J A
  infer_instance

private theorem scalarCoreExists
    (E : RingedTensorModules.{c, v, r} J R ⥤ RingedTensorModules.{c, v, r} J S)
    [E.Additive]
    (hobj : ∀ M, E.obj M = SheafOfModules.changeOfRings φ M)
    (hmap : ∀ {M N} (f : M ⟶ N), E.map f = eqToHom (hobj M) ≫
      SheafOfModules.changeOfRingsHom φ M f ≫ eqToHom (hobj N).symm)
    (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
    (hκ : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E hobj
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E hobj (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ E hobj (Q.X q) U 1 y))
    : letI := complexMonoidal.{c, v, r} J R
      letI := complexMonoidal.{c, v, r} J S
      ∃ m : (E.mapHomologicalComplex (.up ℤ)).CoreMonoidal,
        ∀ P Q, (m.μIso P Q).inv = κ.hom.app (P, Q) := by
  classical
  have he : E = CochainPullback.extensionFunctor φ :=
    Functor.ext hobj (fun _ _ f ↦ hmap f)
  subst E
  let := complexMonoidal.{c, v, r} J R
  let := complexMonoidal.{c, v, r} J S
  obtain ⟨d⟩ := SheafOfModules.scalarExtension_constraint_coherence R S φ
  let := (scalarModuleCore J φ d).toMonoidal
  let := (CochainPullback.extensionAdjunction φ).isLeftAdjoint
  let F := (CochainPullback.extensionFunctor φ).mapHomologicalComplex (.up ℤ)
  let m := Functor.CoreMonoidal.ofOplaxMonoidal F
  refine ⟨m, ?_⟩
  intro P Q
  change ((CochainPullback.extensionFunctor φ).mapCochainComplexμIso P Q).inv = _
  apply HomologicalComplex.hom_ext
  intro n
  apply extendedTotal_ext J φ P Q _ n
  intro p q hpq U x y
  subst n
  have hc := complexScalar_generators J φ d P Q p q (p + q) rfl U x y
  have hh := hκ P Q p q U x y
  with_unfolding_all exact hc.trans hh.symm
end CategoryTheory.ScalarMonoidalProof

namespace CategoryTheory.ScalarMonoidalProof
variable {C : Type c} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  (R : Sheaf J CommRingCat.{max c v r})
@[reducible] private def complexStruct :
    MonoidalCategoryStruct (CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :=
  (complexMonoidal.{c, v, r} J R).toMonoidalCategoryStruct

private theorem complex_whiskerRight {P P' :
    CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ}
    (f : P ⟶ P') (Q : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ) :
    letI := complexStruct.{c, v, r} J R
    f ▷ Q = HomologicalComplex.mapBifunctorMap f (𝟙 Q)
      (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) := by
  rfl
private theorem complex_whiskerLeft (P :
    CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
    {Q Q' : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ} (f : Q ⟶ Q') :
    letI := complexStruct.{c, v, r} J R
    P ◁ f = HomologicalComplex.mapBifunctorMap (𝟙 P) f
      (curriedTensor (RingedTensorModules.{c, v, r} J R)) (.up ℤ) := by
  rfl

private theorem unitKFlat :
    letI := complexMonoidal.{c, v, r} J R
    CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r}
      (J := J) (R := R) (ringedTensorUnitComplex.{c, v, r} J R) := by
  let := complexMonoidal.{c, v, r} J R
  intro F hF i
  change (F ⊗ (𝟙_ (CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ))).ExactAt i
  exact (exactAt_iff_of_quasiIsoAt (ρ_ F).hom i).2 (hF i)
private theorem kFlatMonoidal :
    let := complexMonoidal.{c, v, r} J R
    ObjectProperty.IsMonoidal
      (CochainComplex.IsKFlatIndependentCoefficients.{c, v, max c v r} (J := J) (R := R)) := by
  let := complexMonoidal.{c, v, r} J R
  exact {
  prop_unit := unitKFlat.{c, v, r} J R
  prop_tensor P Q hP hQ := coefficientTotalTensor_isKFlat.{r, c, v} J R P Q hP hQ }
variable [HasDerivedCategory.{w} (RingedTensorModules.{c, v, r} J R)]
  (A : CoefficientClosedStructure (derivedInternalHomOfUniverses.{c, v, r, w} J R))
  (M : CoefficientTensorModels.{r, c, v, w} J R A)
  (β : @SymmetricCategory _ _ A.monoidal)
  (h : RingedDerivedTensorCoherence.{c, v, r, w} J R A M β)
set_option maxHeartbeats 5000000 in
-- Elaborating the model coherences unfolds nested sheaf and complex tensor structures.
private def modelCore :
    letI := complexMonoidal.{c, v, r} J R
    letI := kFlatMonoidal.{c, v, r} J R
    @Functor.CoreMonoidal _ _ _ _ _ A.monoidal
      (coefficientKFlatInclusion.{r, c, v} J R ⋙ DerivedCategory.Q.{w}) := by
  letI := complexMonoidal.{c, v, r} J R
  letI := kFlatMonoidal.{c, v, r} J R
  letI := A.monoidal
  letI := complexStruct.{c, v, r} J R
  refine Functor.CoreMonoidal.mk'
    (F := coefficientKFlatInclusion.{r, c, v} J R ⋙ DerivedCategory.Q.{w}) h.unitIso
    (fun P Q ↦ (M.iso J R A P.obj Q.obj P.property Q.property).symm) ?_ ?_ ?_ ?_ ?_
  · intro P P' f Q
    with_unfolding_all change
      (M.iso J R A P.obj Q.obj P.property Q.property).hom ≫
          DerivedCategory.Q.map f.hom ▷ DerivedCategory.Q.obj Q.obj =
        DerivedCategory.Q.map (f.hom ▷ Q.obj) ≫
          (M.iso J R A P'.obj Q.obj P'.property Q.property).hom
    have hh := h.tensorIso_naturality P.obj Q.obj P'.obj Q.obj
      (Or.inl P.property) (Or.inl P'.property) f.hom (𝟙 Q.obj)
    rw [h.tensorIso_both P.obj Q.obj P.property Q.property,
      h.tensorIso_both P'.obj Q.obj P'.property Q.property] at hh
    with_unfolding_all simpa only [coefficientTotalTensor, Functor.uncurry_obj_map, Functor.map_id,
      Category.comp_id, Functor.map₂HomologicalComplex_map_app,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensor, tensorHom_id,
      complex_whiskerRight.{c, v, r} J R] using hh.symm
  · intro Q Q' P f
    with_unfolding_all change
      (M.iso J R A P.obj Q.obj P.property Q.property).hom ≫
          DerivedCategory.Q.obj P.obj ◁ DerivedCategory.Q.map f.hom =
        DerivedCategory.Q.map (P.obj ◁ f.hom) ≫
          (M.iso J R A P.obj Q'.obj P.property Q'.property).hom
    have hh := h.tensorIso_naturality P.obj Q.obj P.obj Q'.obj
      (Or.inl P.property) (Or.inl P.property) (𝟙 P.obj) f.hom
    rw [h.tensorIso_both P.obj Q.obj P.property Q.property,
      h.tensorIso_both P.obj Q'.obj P.property Q'.property] at hh
    with_unfolding_all simpa only [coefficientTotalTensor, Functor.uncurry_obj_map, Functor.map_id,
      NatTrans.id_app, Category.id_comp, Functor.map₂HomologicalComplex_obj_map,
      CoefficientClosedStructure.tensor, MonoidalCategory.tensor, id_tensorHom,
      complex_whiskerLeft.{c, v, r} J R] using hh.symm
  · intro P Q N
    with_unfolding_all change
      (M.iso J R A (P.obj ⊗ Q.obj) N.obj
          (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _ P.property Q.property) N.property).hom ≫
          (M.iso J R A P.obj Q.obj P.property Q.property).hom ▷
            DerivedCategory.Q.obj N.obj ≫
          (α_ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
            (DerivedCategory.Q.obj N.obj)).hom =
        DerivedCategory.Q.map (α_ P.obj Q.obj N.obj).hom ≫
          (M.iso J R A P.obj (Q.obj ⊗ N.obj) P.property
            (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _ Q.property N.property)).hom ≫
          DerivedCategory.Q.obj P.obj ◁
            (M.iso J R A Q.obj N.obj Q.property N.property).hom
    have hh := RingedKFlatModel.associator_model_native.{c, v, r, w} J R A M β h
      P.obj Q.obj N.obj P.property Q.property N.property
    rw [h.tensorIso_both _ _ (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _
      P.property Q.property) N.property,
      h.tensorIso_both _ _ P.property (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _
        Q.property N.property)] at hh
    with_unfolding_all change
      (M.iso J R A (P.obj ⊗ Q.obj) N.obj
          (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _ P.property Q.property) N.property).hom ≫
          ((M.iso J R A P.obj Q.obj P.property Q.property).hom ⊗ₘ
            𝟙 (DerivedCategory.Q.obj N.obj)) ≫
          (α_ (DerivedCategory.Q.obj P.obj) (DerivedCategory.Q.obj Q.obj)
            (DerivedCategory.Q.obj N.obj)).hom =
        DerivedCategory.Q.map (α_ P.obj Q.obj N.obj).hom ≫
          (M.iso J R A P.obj (Q.obj ⊗ N.obj) P.property
            (coefficientTotalTensor_isKFlat.{r, c, v} J R _ _ Q.property N.property)).hom ≫
          (𝟙 (DerivedCategory.Q.obj P.obj) ⊗ₘ
            (M.iso J R A Q.obj N.obj Q.property N.property).hom) at hh
    simpa only [tensorHom_id, id_tensorHom] using hh
  · intro P
    with_unfolding_all change (λ_ (DerivedCategory.Q.obj P.obj)).inv =
      DerivedCategory.Q.map (λ_ P.obj).inv ≫
        (M.iso J R A (𝟙_ _) P.obj (unitKFlat.{c, v, r} J R) P.property).hom ≫
        h.unitIso.inv ▷ DerivedCategory.Q.obj P.obj
    have hh := RingedKFlatModel.leftUnitor_model_native.{c, v, r, w} J R A M β h
      P.obj P.property
    rw [h.tensorIso_both _ _ (unitKFlat.{c, v, r} J R) P.property] at hh
    with_unfolding_all change (M.iso J R A (𝟙_ _) P.obj (unitKFlat.{c, v, r} J R) P.property).hom ≫
      (h.unitIso.inv ⊗ₘ 𝟙 (DerivedCategory.Q.obj P.obj)) ≫
        (λ_ (DerivedCategory.Q.obj P.obj)).hom =
      DerivedCategory.Q.map (λ_ P.obj).hom at hh
    apply (cancel_mono (λ_ (DerivedCategory.Q.obj P.obj)).hom).1
    rw [Category.assoc, Category.assoc, ← tensorHom_id, hh]
    simp [← Functor.map_comp]
  · intro P
    with_unfolding_all change (ρ_ (DerivedCategory.Q.obj P.obj)).inv =
      DerivedCategory.Q.map (ρ_ P.obj).inv ≫
        (M.iso J R A P.obj (𝟙_ _) P.property (unitKFlat.{c, v, r} J R)).hom ≫
        DerivedCategory.Q.obj P.obj ◁ h.unitIso.inv
    have hh := RingedKFlatModel.rightUnitor_model_native.{c, v, r, w} J R A M β h
      P.obj P.property
    rw [h.tensorIso_both _ _ P.property (unitKFlat.{c, v, r} J R)] at hh
    with_unfolding_all change (M.iso J R A P.obj (𝟙_ _) P.property (unitKFlat.{c, v, r} J R)).hom ≫
      (𝟙 (DerivedCategory.Q.obj P.obj) ⊗ₘ h.unitIso.inv) ≫
        (ρ_ (DerivedCategory.Q.obj P.obj)).hom =
      DerivedCategory.Q.map (ρ_ P.obj).hom at hh
    apply (cancel_mono (ρ_ (DerivedCategory.Q.obj P.obj)).hom).1
    rw [Category.assoc, Category.assoc, ← id_tensorHom, hh]
    simp [← Functor.map_comp]

end CategoryTheory.ScalarMonoidalProof

namespace CategoryTheory.ScalarMonoidalProof
private def restrictCore {A B : Type*} [Category* A] [Category* B]
    [MonoidalCategory A] [MonoidalCategory B]
    (P : ObjectProperty A) (Q : ObjectProperty B) [P.IsMonoidal] [Q.IsMonoidal]
    (F : A ⥤ B) (s : F.CoreMonoidal) (hF : ∀ X, P X → Q (F.obj X)) :
    (Q.lift (P.ι ⋙ F) (fun X ↦ hF X.obj X.property)).CoreMonoidal where
  εIso := Q.isoMk s.εIso
  μIso X Y := Q.isoMk (s.μIso X.obj Y.obj)
  μIso_hom_natural_left {X X'} f Y := by
    apply ObjectProperty.hom_ext
    exact s.μIso_hom_natural_left f.hom Y.obj
  μIso_hom_natural_right X f := by
    apply ObjectProperty.hom_ext
    exact s.μIso_hom_natural_right X.obj f.hom
  associativity X Y Z := by
    apply ObjectProperty.hom_ext
    exact s.associativity X.obj Y.obj Z.obj
  left_unitality X := by
    apply ObjectProperty.hom_ext
    exact s.left_unitality X.obj
  right_unitality X := by
    apply ObjectProperty.hom_ext
    exact s.right_unitality X.obj

private theorem normalizedDescent {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (L : C ⥤ D) (W : MorphismProperty C) [L.IsLocalization W]
    [W.ContainsIdentities] [L.Monoidal]
    (F : D ⥤ E) (G : C ⥤ E) [G.Monoidal] (e : L ⋙ F ≅ G)
    (d : tensor D ⋙ F ≅ F.prod F ⋙ tensor E)
    (h : ∀ X Y,
      F.map (Functor.OplaxMonoidal.δ L X Y) ≫ d.hom.app (L.obj X, L.obj Y) ≫
        (e.hom.app X ⊗ₘ e.hom.app Y) =
      e.hom.app (X ⊗ Y) ≫ Functor.OplaxMonoidal.δ G X Y) :
    ∃ m : F.CoreMonoidal, ∀ X Y, (m.μIso X Y).hom = d.inv.app (X, Y) := by
  let : Localization.Lifting L W G F := ⟨e⟩
  let : F.Monoidal := Localization.Monoidal.functorMonoidalOfComp L W F G
  have heq : (Functor.Monoidal.μNatIso F).hom = d.inv := by
    apply Localization.natTrans_ext (L.prod L) (W.prod W)
    rintro ⟨X, Y⟩
    change Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) = d.inv.app (L.obj X, L.obj Y)
    rw [Localization.Monoidal.functorMonoidalOfComp_μ L W F G]
    change (e.hom.app X ⊗ₘ e.hom.app Y) ≫ Functor.LaxMonoidal.μ G X Y ≫
      e.inv.app (X ⊗ Y) ≫ F.map (Functor.OplaxMonoidal.δ L X Y) = _
    apply (cancel_mono (d.hom.app (L.obj X, L.obj Y) ≫
      (e.hom.app X ⊗ₘ e.hom.app Y))).1
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [h, ← Category.assoc, ← Category.assoc]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Functor.Monoidal.μ_δ,
      Category.comp_id]
  let m : F.CoreMonoidal :=
    { εIso := Functor.Monoidal.εIso F
      μIso := Functor.Monoidal.μIso F
      μIso_hom_natural_left := Functor.LaxMonoidal.μ_natural_left F
      μIso_hom_natural_right := Functor.LaxMonoidal.μ_natural_right F
      associativity := Functor.LaxMonoidal.associativity F
      left_unitality := Functor.LaxMonoidal.left_unitality F
      right_unitality := Functor.LaxMonoidal.right_unitality F }
  exact ⟨m, fun X Y ↦ congr_app heq (X, Y)⟩
end CategoryTheory.ScalarMonoidalProof

namespace CategoryTheory
section Site
variable {C : Type c} [Category.{v} C]
  (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  {R S : Sheaf J CommRingCat.{max c v r}} (φ : R ⟶ S)

-- The normalization identifies tensorators through several monoidal functor constructions.
/-- The canonical normalized scalar tensor comparison is strong monoidal.
Source: Stacks Project, sites-cohomology.tex, Tag 07A4, lemma-pullback-tensor-product,
and Tag 0FPT, lemma-symmetric-monoidal-derived
(blueprint: lem-fix-ringed-scalar-tensor-monoidal).

Proof: use the supplied canonical scalar total-tensor comparison and its
normalization. The generator formula uniquely fixes the chain comparison;
the K-flat counit square uniquely fixes its derived comparison. The coefficient unit
is K-flat in degree zero; scalar multiplication identifies its scalar extension with
the target unit.
Localize this map using D's invertible K-flat counit and the recorded unit
identifications to obtain an invertible derived unit comparison. On three
K-flat representatives, the associativity diagram sends every generator
s tensor ((x tensor y) tensor z) to
(s tensor x) tensor ((1 tensor y) tensor (1 tensor z)) on both routes.
The two unit diagrams are the scalar action laws. Sheafification and the
total coproduct summands detect these equalities. The normalization squares, recorded associator
and unitors, and coefficient unit
identifications descend them to derived objects. K-flat resolutions and
naturality give the equations for arbitrary objects. Package the inverse
unit map and inverse tensor comparison with CoreMonoidal.mk'. This gives m
with precisely the displayed tensorator. Neither flatness of the coefficient map
nor boundedness of complexes is required.
-/
theorem ringedScalarTensorMonoidal
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]
    [HasDerivedCategory.{w} (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J S))]
    (D : SheafOfModules.DerivedChangeOfRingsCochainModel.{c, v, max c v r, w, w} φ)
    (AR : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J R))
    (AS : WeilConjectures.CoefficientClosedStructure
      (derivedInternalHomOfUniverses.{c, v, r, w} J S))
    (MR : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J R AR)
    (MS : WeilConjectures.CoefficientTensorModels.{r, c, v, w} J S AS)
    (βR : @SymmetricCategory _ _ AR.monoidal)
    (βS : @SymmetricCategory _ _ AS.monoidal)
    (hR : RingedDerivedTensorCoherence.{c, v, r, w} J R AR MR βR)
    (hS : RingedDerivedTensorCoherence.{c, v, r, w} J S AS MS βS)
    (κ : WeilConjectures.coefficientTotalTensor.{r, c, v} J R ⋙
          D.E.mapHomologicalComplex (ComplexShape.up ℤ) ≅
        (D.E.mapHomologicalComplex (ComplexShape.up ℤ)).prod
          (D.E.mapHomologicalComplex (ComplexShape.up ℤ)) ⋙
            WeilConjectures.coefficientTotalTensor.{r, c, v} J S)
    (μ : AR.tensor ⋙ D.T ≅ D.T.prod D.T ⋙ AS.tensor)
    (hκ : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (p q : ℤ) (U : Cᵒᵖ) (x : (P.X p).val.obj U) (y : (Q.X q).val.obj U),
        ((κ.hom.app (P, Q)).f (p + q)).val.app U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq
            (((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)).X (p + q))
            U 1 (WeilConjectures.coefficientTensorGenerator.{r, c, v} J R
              P Q p q (p + q) rfl U x y)) =
        WeilConjectures.coefficientTensorGenerator.{r, c, v} J S
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P)
          ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q) p q (p + q) rfl U
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (P.X p) U 1 x)
          (ringedFiniteFreeScalarSection.{c, v, r} J φ D.E D.obj_eq (Q.X q) U 1 y))
    (hμ : ∀ (P Q : CochainComplex (SheafOfModules.{max c v r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ)
        (hP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) P)
        (hQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := R) Q),
        ∃ (hEP : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj P))
          (hEQ : CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
            ((D.E.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q)),
          D.T.map ((MR.iso J R AR P Q hP hQ).hom) ≫
              μ.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
              AS.tensor.map (Prod.mkHom (D.ε.app P) (D.ε.app Q)) =
            D.ε.app ((WeilConjectures.coefficientTotalTensor.{r, c, v} J R).obj (P, Q)) ≫
              DerivedCategory.Q.map (κ.hom.app (P, Q)) ≫
              (MS.iso J S AS _ _ hEP hEQ).hom) :
    ∃ (m : @Functor.CoreMonoidal _ _ AR.monoidal _ _ AS.monoidal D.T),
      ∀ P Q, (@Functor.CoreMonoidal.μIso _ _ AR.monoidal _ _ AS.monoidal
        D.T m P Q).hom = μ.inv.app (P, Q) := by
  classical
  let := ScalarMonoidalProof.complexMonoidal.{c, v, r} J R
  let := ScalarMonoidalProof.complexMonoidal.{c, v, r} J S
  let := ScalarMonoidalProof.kFlatMonoidal.{c, v, r} J R
  let := ScalarMonoidalProof.kFlatMonoidal.{c, v, r} J S
  let := AR.monoidal
  let := AS.monoidal
  obtain ⟨mE, hmE⟩ := ScalarMonoidalProof.scalarCoreExists.{c, v, r}
    J φ D.E D.obj_eq D.map_eq κ hκ
  let := mE.toMonoidal
  let K := coefficientKFlatInclusion.{r, c, v} J R
  let KS := coefficientKFlatInclusion.{r, c, v} J S
  let L := K ⋙ DerivedCategory.Q.{w}
  let LS := KS ⋙ DerivedCategory.Q.{w}
  have hk (P : CochainComplex (RingedTensorModules.{c, v, r} J R) ℤ)
      (hP : P.IsKFlatIndependentCoefficients) :
      CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S)
        ((D.E.mapHomologicalComplex (.up ℤ)).obj P) :=
    (hμ P P hP hP).choose
  let E := ObjectProperty.lift
    (CochainComplex.IsKFlatIndependentCoefficients (J := J) (R := S))
    (K ⋙ D.E.mapHomologicalComplex (.up ℤ)) (fun P ↦ hk P.obj P.property)
  let : E.Monoidal := (ScalarMonoidalProof.restrictCore _ _ _ mE hk).toMonoidal
  let : L.Monoidal := (ScalarMonoidalProof.modelCore.{c, v, r, w}
    (M := MR) (β := βR) (h := hR) J R AR).toMonoidal
  let : LS.Monoidal := (ScalarMonoidalProof.modelCore.{c, v, r, w}
    (M := MS) (β := βS) (h := hS) J S AS).toMonoidal
  let W := (HomologicalComplex.quasiIso (RingedTensorModules.{c, v, r} J R)
    (.up ℤ)).inverseImage K
  let : L.IsLocalization W := RingedDerivedNative.kFlatLocalization.{c, v, r, w} J R
  let e : L ⋙ D.T ≅ E ⋙ LS := NatIso.ofComponents
    (fun P ↦ by
      let := D.computes P.obj P.property
      exact asIso (D.ε.app P.obj))
    (fun f ↦ by
      change D.T.map (DerivedCategory.Q.map f.hom) ≫ D.ε.app _ =
        D.ε.app _ ≫ DerivedCategory.Q.map
          ((D.E.mapHomologicalComplex (.up ℤ)).map f.hom)
      exact D.ε.naturality f.hom)
  apply ScalarMonoidalProof.normalizedDescent L W D.T (E ⋙ LS) e μ
  intro P Q
  have hh := (hμ P.obj Q.obj P.property Q.property).choose_spec.choose_spec
  with_unfolding_all change (
    D.T.map (MR.iso J R AR P.obj Q.obj P.property Q.property).hom ≫
      μ.hom.app (DerivedCategory.Q.obj P.obj, DerivedCategory.Q.obj Q.obj) ≫
        (D.ε.app P.obj ⊗ₘ D.ε.app Q.obj) =
    D.ε.app ((coefficientTotalTensor.{r, c, v} J R).obj (P.obj, Q.obj)) ≫
      (DerivedCategory.Q.map ((mE.μIso P.obj Q.obj).inv) ≫
        (MS.iso J S AS _ _ (hk P.obj P.property) (hk Q.obj Q.property)).hom))
  simp only [hmE]
  with_unfolding_all exact hh

end Site
end CategoryTheory

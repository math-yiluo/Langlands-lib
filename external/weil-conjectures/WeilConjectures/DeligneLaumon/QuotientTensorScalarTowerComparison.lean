/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.DeligneLaumon.PrincipalIntrinsicCompletion.PrincipalIntrinsicCompletion
import all Mathlib.Algebra.Category.ModuleCat.Basic
import all WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import all WeilConjectures.DeligneLaumon.PrincipalKoszulStrictReplacement.PrincipalKoszulStrictReplacement
import all WeilConjectures.Algebra.Homology.ProEtaleCoefficients.RestrictedKFlatTensorIdentification
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.Algebra.Homology.Ringed.RingedTensorComplexConstraintsSupplement

/-! # Total tensor and ordinary scalar reduction, with their actual units

Source: Stacks Project, Tags 03EK, 06YY and 012Z.
(blueprint: lem-a1-quotient-tensor-scalar-tower-comparison).
The proof first constructs the balanced scalar comparison on sheaves, then lifts it
through degree-zero totalization, and checks the transition and unit formulas.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped ChangeOfRings
namespace SheafOfModules
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{r}] [HasSheafify J AddCommGrpCat.{r}]
  {R S : Sheaf J CommRingCat.{r}}
open RestrictedTensorProof
attribute [local implicit_reducible] SheafOfModules.restrictScalars SheafOfModules.unit
  CategoryTheory.sheafCompose siteSheafTensorRight
omit [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})] in
private theorem presentation_hom (M N : KFlatTotalTensorModel.Modules R) :
    (tensorRightPresentation R N).hom.app M = (tensorObjIsoSheafification M N).hom := by
  have hi : ((tensorRightPresentation R N).app M).inv =
      (tensorObjIsoSheafification M N).inv := by
    dsimp only [tensorRightPresentation, Iso.trans_inv, NatTrans.comp_app,
      Functor.mapIso_inv, Iso.symm_inv, NatIso.ofComponents_inv_app,
      Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Iso.app_hom,
      NatIso.ofComponents_hom_app]
    simp only [tensorObjIsoSheafification, Iso.trans_inv, Iso.symm_inv,
      tensorIso_hom, tensorHom_def]
    rfl
  exact congrArg Iso.hom (Iso.ext_inv hi)

private def moduleTensorScalarIso (φ : R ⟶ S)
    (M : KFlatTotalTensorModel.Modules R) :
    M ⊗ restrictedTensorCoefficient φ ≅
      (restrictedTensorScalars φ).obj (changeOfRings φ M) :=
  (siteSheafTensorRightIso R (restrictedTensorCoefficient φ)).symm.app M ≪≫
    (swapSheafIso φ M).symm

attribute [local irreducible] moduleTensorScalarIso swapSheafIso
  siteSheafTensorRightIso tensorObjIsoSheafification

private theorem moduleTensorScalarIso_pure (φ : R ⟶ S)
    (M : KFlatTotalTensorModel.Modules R) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (moduleTensorScalarIso φ M).hom.val.app U
        (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) =
      (toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x) := by
  have hswap := swapSheafIso_tmul φ M U s x
  apply (ConcreteCategory.bijective_of_isIso
    (((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _ ⋙
      (CategoryTheory.evaluation Cᵒᵖ AddCommGrpCat).obj U).map (swapSheafIso φ M).hom))).1
  change ((moduleTensorScalarIso φ M).hom ≫ (swapSheafIso φ M).hom).val.app U
      (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) = _
  simp only [moduleTensorScalarIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change ((siteSheafTensorRightIso R (restrictedTensorCoefficient φ)).symm.app M).hom.val.app U
      (CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s) =
    (swapSheafIso φ M).hom.val.app U
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x))
  conv_rhs => rw [hswap]
  let a := PresheafOfModules.sheafification (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙
    ((sheafCompose J (forget₂ CommRingCat.{r} RingCat.{r})).obj R).obj)
  let N := restrictedTensorCoefficient φ
  have he : (tensorObjIsoSheafification M N).inv ≫
      ((siteSheafTensorRightIso R N).symm.app M).hom =
        a.map ((siteTensorRightIso R N.val).inv.app M.val) := by
    simp only [siteSheafTensorRightIso, Iso.app_hom, NatTrans.comp_app,
      Iso.symm_hom, Iso.trans_inv,
      Iso.symm_inv, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
      Functor.whiskerRight_app]
    rw [presentation_hom, Iso.inv_hom_id_assoc]
    rfl
  change ((adj.unit.app (M.val ⊗ N.val) ≫
    ((tensorObjIsoSheafification M N).inv ≫
      ((siteSheafTensorRightIso R N).symm.app M).hom).val).app U) (x ⊗ₜ[R.obj.obj U] s) = _
  rw [he]
  have hn := congrArg (fun k ↦ k.app U (x ⊗ₜ[R.obj.obj U] s))
    (adj.unit.naturality ((siteTensorRightIso R N.val).inv.app M.val))
  exact hn.symm
private theorem moduleTensorScalarIso_inv_pure (φ : R ⟶ S)
    (M : KFlatTotalTensorModel.Modules R) (U : Cᵒᵖ)
    (x : M.val.obj U) (s : S.obj.obj U) :
    (moduleTensorScalarIso φ M).inv.val.app U
      ((toSheafify J (changeOfRingsPresheaf φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] x)) =
      CochainPullback.moduleTmul M (restrictedTensorCoefficient φ) U x s := by
  have h := congrArg ((moduleTensorScalarIso φ M).inv.val.app U)
    (moduleTensorScalarIso_pure φ M U x s)
  simpa only [← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
    ← comp_val, Iso.hom_inv_id, id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply] using h.symm

end SheafOfModules

namespace SheafOfModules
attribute [local instance] isMonoidal_W_independentCoefficients monoidalCategory
attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.sheafCompose
private theorem unitor_inv_pure
    {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
    [HasSheafify J AddCommGrpCat.{max c v r}]
    (R : Sheaf J CommRingCat.{max c v r})
    (M : SheafOfModules.{max c v r}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (ρ_ M).inv.val.app U x =
      CochainPullback.moduleTmul (R := R) M
        (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
        U x (1 : R.obj.obj U) := by
  have h := CategoryTheory.RingedDerivedNative.pureTensor_rightUnitor.{c, v, r}
    J R M U 1 x
  have hh := congrArg ((ρ_ M).inv.val.app U) h
  have hh' := (by
    simpa only [CategoryTheory.RingedDerivedNative.pureTensor,
      CategoryTheory.RingedDerivedNative.moduleMonoidal,
      SheafOfModules.cochainModulesMonoidal,
      one_smul, ← ModuleCat.comp_apply, ← PresheafOfModules.comp_app,
      ← comp_val, Iso.hom_inv_id, id_val, PresheafOfModules.id_app,
      ModuleCat.id_apply] using hh.symm : _)
  convert hh' using 1
end SheafOfModules

universe t u
namespace WeilConjectures
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
open PrincipalKoszulStrictReplacement PrincipalIntrinsicCompletion
attribute [local implicit_reducible] completedIntegralCommRingSheafUnrestricted
  CategoryTheory.sheafCompose IntegralOnSlice.Site IntegralOnSlice.siteCategory
  IntegralOnSlice.topology IntegralOnSlice.restrict IntegralOnSlice.ring
  IntegralOnSlice.finite IntegralOnSlice.projection
  PrincipalKoszulStrictReplacement.residue SheafOfModules.restrictScalars SheafOfModules.unit
  completedIntegralCommRingProjectionUnrestricted integralCoefficientSheaf
  integralCoefficientCommRingSheaf
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted
  IntegralOnSlice.reductionWitness IntegralOnSlice.reduction
private theorem iso_square_of_inverse
    {D : Type*} [Category* D] {X Y X' Y' : D}
    (a : X ≅ X') (b : Y ≅ Y') (f : X ⟶ Y) (g : X' ⟶ Y')
    (h : a.inv ≫ f = g ≫ b.inv) : f ≫ b.hom = a.hom ≫ g := by
  apply a.inv_comp_eq.mp
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private theorem iso_unit_of_inverse
    {D : Type*} [Category* D] {A X Y Z : D} (e : Y ≅ Z)
    (f : A ⟶ X) (g : X ⟶ Y) (u : A ⟶ Z)
    (h : f ≫ g = u ≫ e.inv) : f ≫ g ≫ e.hom = u := by
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (W : AlgebraicGeometry.Scheme.{t})
open SheafOfModules SheafOfModules.RestrictedTensorProof
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
  SheafOfModules.monoidalCategory

private abbrev TensorModules := Modules l E W

private abbrev concreteTensor : TensorModules l E W ⥤
    TensorModules l E W ⥤ TensorModules l E W :=
  KFlatTotalTensorModel.tensor (completedIntegralCommRingSheafUnrestricted l E W)

section TensorProof
variable [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}]

private local instance tensorMonoidal : MonoidalCategory (TensorModules l E W) :=
  KFlatTotalTensorModel.monoidal (completedIntegralCommRingSheafUnrestricted l E W)

private local instance tensorZero :
    (concreteTensor l E W).PreservesZeroMorphisms :=
  KFlatTotalTensorModel.tensor_preservesZeroMorphisms
    (completedIntegralCommRingSheafUnrestricted l E W)

private local instance tensorPreadditive : MonoidalPreadditive (TensorModules l E W) :=
  cochainModulesPreadditive (completedIntegralCommRingSheafUnrestricted l E W)

private local instance tensorObjZero :
    ∀ M : TensorModules l E W, ((concreteTensor l E W).obj M).PreservesZeroMorphisms :=
  fun M ↦ KFlatTotalTensorModel.tensor_obj_preservesZeroMorphisms
    (completedIntegralCommRingSheafUnrestricted l E W) M

private local instance tensorHasTotal
    (P Q : CochainComplex (TensorModules l E W) ℤ) :
    CochainComplex.HasMapBifunctor P Q (concreteTensor l E W) :=
  KFlatTotalTensorModel.hasTotal (completedIntegralCommRingSheafUnrestricted l E W) P Q

attribute [local implicit_reducible] PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj
  ModuleCat.restrictScalars ModuleCat.RestrictScalars.obj'
  PresheafOfModules.unit SheafOfModules.changeOfRingsPresheaf
  ModuleCat.extendScalars ModuleCat.ExtendScalars.obj'

attribute [local implicit_reducible] tensorWith targetTower targetTowerMap
  CategoryTheory.Functor.map₂HomologicalComplex CategoryTheory.Functor.ofOpSequence
  CategoryTheory.Functor.ofSequence

attribute [local implicit_reducible] tensorMonoidal
  KFlatTotalTensorModel.tensor KFlatTotalTensorModel.monoidal

omit
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem single_tensor_inv (M : TensorModules l E W)
    (P : CochainComplex (TensorModules l E W) ℤ) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso
      (concreteTensor l E W)
      M P).inv.f i =
      (P.X i ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv) ≫
        HomologicalComplex.ιMapBifunctor P
          ((CochainComplex.singleFunctor (TensorModules l E W) 0).obj M)
          (concreteTensor l E W)
          (.up ℤ) i 0 i (by simp) := by
  let : MonoidalCategory (TensorModules l E W) := KFlatTotalTensorModel.monoidal
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) := cochainModulesPreadditive
    (completedIntegralCommRingSheafUnrestricted l E W)
  dsimp only [CochainComplex.mapBifunctorSingle₂Iso, Iso.trans_inv,
    HomologicalComplex.comp_f, Iso.symm_inv]
  rw [CochainComplex.mapBifunctorSingle₁Iso_inv_f]
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorFlipIso_hom]
  simp
  rfl

omit
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem single_tensor_second_naturality
    {M N : TensorModules l E W} (f : M ⟶ N)
    (P : CochainComplex (TensorModules l E W) ℤ) (i : ℤ) :
    (CochainComplex.mapBifunctorSingle₂Iso
      (concreteTensor l E W)
      M P).inv.f i ≫
        ((tensorWith l E W P).map
          ((CochainComplex.singleFunctor (TensorModules l E W) 0).map f)).f i =
      (P.X i ◁ f) ≫ (CochainComplex.mapBifunctorSingle₂Iso
        (concreteTensor l E W)
        N P).inv.f i := by
  let : MonoidalCategory (TensorModules l E W) := KFlatTotalTensorModel.monoidal
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) := cochainModulesPreadditive
    (completedIntegralCommRingSheafUnrestricted l E W)
  rw [single_tensor_inv l E W M P i, single_tensor_inv l E W N P i]
  change (_ ≫ _) ≫ (HomologicalComplex.mapBifunctorMap (𝟙 P)
    ((CochainComplex.singleFunctor (TensorModules l E W) 0).map f)
    (concreteTensor l E W)
    (.up ℤ)).f i = _
  rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
  rw [HomologicalComplex.id_f, CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  dsimp only [CochainComplex.singleFunctor, CochainComplex.singleFunctors]
  rw [HomologicalComplex.single_map_f_self]
  change (P.X i ◁ (HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).inv) ≫
      (P.X i ◁ ((HomologicalComplex.singleObjXSelf (.up ℤ) 0 M).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 N).inv)) ≫ _ = _
  simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc,
    MonoidalCategory.whiskerLeft_inv_hom_assoc]

private def residueCoefficientIso (n : ℕ) :
    restrictedTensorCoefficient.{t + 1, t, max u (t + 1)}
      (IntegralOnSlice.projection l E W none n) ≅ residue l E W n :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun U ↦
      { hom := { hom' :=
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl } }
        inv := { hom' :=
          { toFun := fun x ↦ x
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl } }
        hom_inv_id := by ext x; rfl
        inv_hom_id := by ext x; rfl }) (by intros; ext x; rfl)

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem residueCoefficientIso_hom_apply (n : ℕ) (U : W.ProEtᵒᵖ)
    (s : (IntegralOnSlice.finite l E W none n).obj.obj U) :
    (residueCoefficientIso l E W n).hom.val.app U s = s := rfl

attribute [local irreducible] residueCoefficientIso

private def sliceSwapIso (n : ℕ) :
    IntegralOnSlice.reduction l E W none n ⋙
        restrictedTensorScalars.{t + 1, t, max u (t + 1)}
          (IntegralOnSlice.projection l E W none n) ≅
      (concreteTensor l E W).flip.obj (residue l E W n) := by
  let φ := IntegralOnSlice.projection l E W none n
  let A := restrictedTensorCoefficient.{t + 1, t, max u (t + 1)} φ
  let e : IntegralOnSlice.reduction l E W none n ⋙
      restrictedTensorScalars.{t + 1, t, max u (t + 1)} φ ≅
      siteSheafTensorRight
        (A := completedIntegralCommRingSheafUnrestricted l E W) A :=
    NatIso.ofComponents (fun M ↦
      (restrictedTensorScalars.{t + 1, t, max u (t + 1)} φ).mapIso
          (eqToIso (IntegralOnSlice.reduction_obj l E W none n M)) ≪≫
        swapSheafIso.{t + 1, t, max u (t + 1)} φ M) (by
          intro M N a
          dsimp only [Functor.comp_map, Iso.trans_hom, Functor.mapIso_hom]
          have hmap := IntegralOnSlice.unrestrictedReduction_map.{t, u}
            l E W none n (M := M) (N := N) a
          rw [hmap]
          simp only [Functor.map_comp, Category.assoc, eqToIso.hom, eqToHom_map,
            eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
          rw [swapSheafIso_naturality.{t + 1, t, max u (t + 1)} φ a])
  exact e ≪≫ siteSheafTensorRightIso.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W) A ≪≫
    (concreteTensor l E W).flip.mapIso
        (residueCoefficientIso l E W n)

attribute [local irreducible] HomologicalComplex₂.total HomologicalComplex.mapBifunctorMap

private def tensorScalarLevelIso (n : ℕ) (P : CochainComplex (TensorModules l E W) ℤ) :
    (targetTower l E W P).obj (op n) ≅ (IntegralOnSlice.level l E W none n).obj P :=
  letI : MonoidalCategory (TensorModules l E W) :=
    SheafOfModules.KFlatTotalTensorModel.monoidal
      (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) :=
    SheafOfModules.cochainModulesPreadditive
      (completedIntegralCommRingSheafUnrestricted l E W)
  let := IntegralOnSlice.reductionAdditive l E W none n
  let : (restrictedTensorScalars.{t + 1, t, max u (t + 1)}
      (IntegralOnSlice.projection l E W none n)).Additive := by
    dsimp only [restrictedTensorScalars]
    infer_instance
  CochainComplex.mapBifunctorSingle₂Iso (concreteTensor l E W)
      (residue l E W n) P ≪≫
    (NatIso.mapHomologicalComplex
      (sliceSwapIso l E W n).symm (.up ℤ)).app P
private theorem sliceSwapIso_hom_generator (n : ℕ) (M : TensorModules l E W)
    (U : W.ProEtᵒᵖ) (s : (IntegralOnSlice.finite l E W none n).obj.obj U)
    (x : M.val.obj U) :
    ((sliceSwapIso l E W n).hom.app M).val.app U
        (IntegralOnSlice.generator l E W none n M U s x) =
      CochainPullback.moduleTmul
        (R := completedIntegralCommRingSheafUnrestricted l E W) M (residue l E W n) U x s := by
  simp only [sliceSwapIso, Iso.trans_hom, NatTrans.comp_app,
    NatIso.ofComponents_hom_app, Functor.mapIso_hom, IntegralOnSlice.generator,
    comp_val, PresheafOfModules.comp_app]
  change ((M ◁ (residueCoefficientIso l E W n).hom).val.app U)
    (((siteSheafTensorRightIso.{t + 1, t, max u (t + 1)}
      (completedIntegralCommRingSheafUnrestricted l E W)
      (restrictedTensorCoefficient.{t + 1, t, max u (t + 1)}
        (IntegralOnSlice.projection l E W none n))).hom.app
        M).val.app U
      ((swapSheafIso.{t + 1, t, max u (t + 1)}
        (IntegralOnSlice.projection l E W none n) M).hom.val.app U
        (((eqToHom (IntegralOnSlice.reduction_obj l E W none n M).symm ≫
          eqToHom (IntegralOnSlice.reduction_obj l E W none n M)).val.app U) _))) = _
  simp only [eqToHom_trans, eqToHom_refl, id_val, PresheafOfModules.id_app,
    ModuleCat.id_apply]
  change ((M ◁ (residueCoefficientIso l E W n).hom).val.app U)
    ((SheafOfModules.moduleTensorScalarIso
      (IntegralOnSlice.projection l E W none n) M).inv.val.app U
      ((toSheafify (AlgebraicGeometry.Scheme.ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf
          (IntegralOnSlice.projection l E W none n) M).presheaf).app U
        (s ⊗ₜ[(completedIntegralCommRingSheafUnrestricted l E W).obj.obj U,
          ((IntegralOnSlice.projection l E W none n).hom.app U).hom] x))) = _
  have h := congrArg ((M ◁ (residueCoefficientIso l E W n).hom).val.app U)
    (SheafOfModules.moduleTensorScalarIso_inv_pure.{t + 1, t, max u (t + 1)}
      (IntegralOnSlice.projection l E W none n) M U x s)
  refine h.trans ?_
  rw [← MonoidalCategory.id_tensorHom]
  erw [CochainPullback.moduleTmul_map (R := completedIntegralCommRingSheafUnrestricted l E W)
    (𝟙 M) (residueCoefficientIso l E W n).hom U x s]
  simp only [id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  exact congrArg (CochainPullback.moduleTmul
    (R := completedIntegralCommRingSheafUnrestricted l E W) M (residue l E W n) U x)
    (residueCoefficientIso_hom_apply l E W n U s)

attribute [local irreducible] sliceSwapIso

private theorem tensorScalarLevelIso_inv_generator (n : ℕ)
    (P : CochainComplex (TensorModules l E W) ℤ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (s : (IntegralOnSlice.finite l E W none n).obj.obj U) (x : (P.X i).val.obj U) :
    ((tensorScalarLevelIso l E W n P).inv.f i).val.app U
        (IntegralOnSlice.generator l E W none n (P.X i) U s x) =
      ((CochainComplex.mapBifunctorSingle₂Iso
          (concreteTensor l E W)
          (residue l E W n) P).inv.f i).val.app U
        (CochainPullback.moduleTmul (R := completedIntegralCommRingSheafUnrestricted l E W)
          (P.X i) (residue l E W n) U x s) := by
  let : MonoidalCategory (TensorModules l E W) :=
    SheafOfModules.KFlatTotalTensorModel.monoidal
      (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) :=
    SheafOfModules.cochainModulesPreadditive
      (completedIntegralCommRingSheafUnrestricted l E W)
  dsimp only [tensorScalarLevelIso, Iso.trans_inv, HomologicalComplex.comp_f,
    Iso.app_inv, NatIso.mapHomologicalComplex_inv_app_f, Iso.symm_inv,
    Iso.trans_hom, NatTrans.comp_app]
  change ((CochainComplex.mapBifunctorSingle₂Iso (concreteTensor l E W)
      (residue l E W n) P).inv.f i).val.app U _ = _
  apply congrArg (((CochainComplex.mapBifunctorSingle₂Iso
    (concreteTensor l E W) (residue l E W n) P).inv.f i).val.app U)
  exact sliceSwapIso_hom_generator l E W n (P.X i) U s x

attribute [local irreducible] tensorScalarLevelIso

section GeneratorChecks
attribute [local implicit_reducible] IntegralOnSlice.tower IntegralOnSlice.level

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem ordinary_transition_apply (n : ℕ)
    (P : CochainComplex (TensorModules l E W) ℤ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (s : (IntegralOnSlice.finite l E W none (n + 1)).obj.obj U)
    (x : (P.X i).val.obj U) :
    (((IntegralOnSlice.transition l E W none n).app P).f i).val.app U
        (IntegralOnSlice.generator l E W none (n + 1) (P.X i) U s x) =
      IntegralOnSlice.generator l E W none n (P.X i) U
        ((IntegralOnSlice.rho l E W none n).hom.app U s) x :=
  (IntegralOnSlice.transition_existsUnique l E W none n).exists.choose_spec P i U s x

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem ordinary_augmentation_apply (n : ℕ)
    (P : CochainComplex (TensorModules l E W) ℤ) (i : ℤ) (U : W.ProEtᵒᵖ)
    (x : (P.X i).val.obj U) :
    (((((IntegralOnSlice.augmentation l E W none).app P).app (op n)).f i).val.app U x) =
      IntegralOnSlice.generator l E W none n (P.X i) U 1 x :=
  (IntegralOnSlice.augmentation_existsUnique l E W none).exists.choose_spec P n i U x

omit [EssentiallySmall.{max u (t + 1)} W.ProEt]
  [HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology W) AddCommGrpCat.{max u (t + 1)}]
  [(AlgebraicGeometry.Scheme.ProEt.topology W).WEqualsLocallyBijective
    AddCommGrpCat.{max u (t + 1)}] in
private theorem targetTower_map_step (n : ℕ)
    (P : CochainComplex (TensorModules l E W) ℤ) :
    (targetTower l E W P).map (homOfLE n.le_succ).op =
      (tensorWith l E W P).map
        ((CochainComplex.singleFunctor (TensorModules l E W) 0).map
          (residueStep l E W n)) := by
  dsimp only [targetTower, Functor.comp_map]
  rw [Functor.ofOpSequence_map_homOfLE_succ]

private theorem tensorScalarLevelIso_transition
    (n : ℕ) (P : CochainComplex (TensorModules l E W) ℤ) :
    (targetTower l E W P).map (homOfLE n.le_succ).op ≫
        (tensorScalarLevelIso l E W n P).hom =
      (tensorScalarLevelIso l E W (n + 1) P).hom ≫
        (IntegralOnSlice.transition l E W none n).app P := by
  let : MonoidalCategory (TensorModules l E W) := KFlatTotalTensorModel.monoidal
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) := cochainModulesPreadditive
    (completedIntegralCommRingSheafUnrestricted l E W)
  refine iso_square_of_inverse
    (tensorScalarLevelIso l E W (n + 1) P) (tensorScalarLevelIso l E W n P)
    ((targetTower l E W P).map (homOfLE n.le_succ).op)
    ((IntegralOnSlice.transition l E W none n).app P) ?_
  rw [targetTower_map_step]
  apply HomologicalComplex.hom_ext
  intro i
  apply IntegralOnSlice.unrestrictedReduction_hom_ext l E W none (n + 1) (P.X i)
  intro U s x
  change (((tensorWith l E W P).map
      ((CochainComplex.singleFunctor (TensorModules l E W) 0).map
        (residueStep l E W n))).f i).val.app U
      (((tensorScalarLevelIso l E W (n + 1) P).inv.f i).val.app U
        (IntegralOnSlice.generator l E W none (n + 1) (P.X i) U s x)) =
    ((tensorScalarLevelIso l E W n P).inv.f i).val.app U
      ((((IntegralOnSlice.transition l E W none n).app P).f i).val.app U
        (IntegralOnSlice.generator l E W none (n + 1) (P.X i) U s x))
  rw [tensorScalarLevelIso_inv_generator l E W (n + 1) P i U s x,
    ordinary_transition_apply l E W n P i U s x,
    tensorScalarLevelIso_inv_generator l E W n P i U
      ((IntegralOnSlice.rho l E W none n).hom.app U s) x]
  change (((CochainComplex.mapBifunctorSingle₂Iso
      (concreteTensor l E W)
      (residue l E W (n + 1)) P).inv.f i) ≫
    ((tensorWith l E W P).map
      ((CochainComplex.singleFunctor (TensorModules l E W) 0).map
        (residueStep l E W n))).f i).val.app U
      (CochainPullback.moduleTmul
        (R := completedIntegralCommRingSheafUnrestricted l E W)
          (P.X i) (residue l E W (n + 1)) U x s) = _
  rw [single_tensor_second_naturality l E W (residueStep l E W n) P i]
  change ((CochainComplex.mapBifunctorSingle₂Iso
      (concreteTensor l E W)
      (residue l E W n) P).inv.f i).val.app U
        ((P.X i ◁ residueStep l E W n).val.app U
          (CochainPullback.moduleTmul
        (R := completedIntegralCommRingSheafUnrestricted l E W)
          (P.X i) (residue l E W (n + 1)) U x s)) = _
  apply congrArg (((CochainComplex.mapBifunctorSingle₂Iso
    (concreteTensor l E W)
    (residue l E W n) P).inv.f i).val.app U)
  rw [← MonoidalCategory.id_tensorHom]
  erw [CochainPullback.moduleTmul_map
    (R := completedIntegralCommRingSheafUnrestricted l E W)
    (𝟙 (P.X i)) (residueStep l E W n) U x s]
  rfl

private theorem tensorScalarLevelIso_unit
    (n : ℕ) (P : CochainComplex (TensorModules l E W) ℤ) :
    (tensorUnit l E W P).inv ≫ (tensorWith l E W P).map
        ((CochainComplex.singleFunctor (TensorModules l E W) 0).map (projection l E W n)) ≫
          (tensorScalarLevelIso l E W n P).hom =
      ((IntegralOnSlice.augmentation l E W none).app P).app (op n) := by
  let : MonoidalCategory (TensorModules l E W) := KFlatTotalTensorModel.monoidal
    (completedIntegralCommRingSheafUnrestricted l E W)
  let : MonoidalPreadditive (TensorModules l E W) := cochainModulesPreadditive
    (completedIntegralCommRingSheafUnrestricted l E W)
  refine iso_unit_of_inverse (tensorScalarLevelIso l E W n P)
    (tensorUnit l E W P).inv ((tensorWith l E W P).map
      ((CochainComplex.singleFunctor (TensorModules l E W) 0).map (projection l E W n)))
    (((IntegralOnSlice.augmentation l E W none).app P).app (op n)) ?_
  apply HomologicalComplex.hom_ext
  intro i
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (((tensorUnit l E W P).inv.f i) ≫
      ((tensorWith l E W P).map
        ((CochainComplex.singleFunctor (TensorModules l E W) 0).map
          (projection l E W n))).f i).val.app U x =
    ((tensorScalarLevelIso l E W n P).inv.f i).val.app U
      (((((IntegralOnSlice.augmentation l E W none).app P).app (op n)).f i).val.app U x)
  rw [ordinary_augmentation_apply]
  rw [tensorScalarLevelIso_inv_generator]
  have hu : (tensorUnit l E W P).inv.f i = (ρ_ (P.X i)).inv ≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (concreteTensor l E W)
        (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) P).inv.f i := by
    conv_rhs => rw [single_tensor_inv l E W
      (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W)) P i]
    exact HomologicalComplex.rightUnitor'_inv P i
  rw [hu, Category.assoc,
    single_tensor_second_naturality l E W (projection l E W n) P i]
  change ((CochainComplex.mapBifunctorSingle₂Iso
      (concreteTensor l E W)
      (residue l E W n) P).inv.f i).val.app U
    ((P.X i ◁ projection l E W n).val.app U ((ρ_ (P.X i)).inv.val.app U x)) = _
  apply congrArg (((CochainComplex.mapBifunctorSingle₂Iso
    (concreteTensor l E W)
    (residue l E W n) P).inv.f i).val.app U)
  erw [SheafOfModules.unitor_inv_pure.{t + 1, t, u}
    (completedIntegralCommRingSheafUnrestricted l E W) (P.X i) U x,
    ← MonoidalCategory.id_tensorHom]
  erw [CochainPullback.moduleTmul_map (R := completedIntegralCommRingSheafUnrestricted l E W)
    (𝟙 (P.X i)) (projection l E W n) U x
      (1 : (completedIntegralCommRingSheafUnrestricted l E W).obj.obj U)]
  simp only [id_val, PresheafOfModules.id_app, ModuleCat.id_apply]
  apply congrArg (CochainPullback.moduleTmul
    (R := completedIntegralCommRingSheafUnrestricted l E W) (P.X i) (residue l E W n) U x)
  refine (PrincipalKoszulStrictReplacement.projection_apply l E W n U 1).trans ?_
  change (completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U 1 = 1
  exact map_one ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U).hom

end GeneratorChecks
end TensorProof

end WeilConjectures

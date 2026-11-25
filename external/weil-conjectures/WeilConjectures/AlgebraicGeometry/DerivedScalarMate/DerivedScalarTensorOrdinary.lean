/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.FourCornersSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
public import WeilConjectures.CategoryTheory.RingObjects.Ab
public import WeilConjectures.CategoryTheory.Sites.MonObj
public import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.Algebra.Homology.IndependentExtensionTensor.ExtensionTensorComparisonIndependent
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement

/-! # Normalized ordinary scalar tensor comparison

The ordinary part of the scalar mate construction, extracted as a separate module
so that the ordinary and derived comparisons compile independently.
Source: Stacks Tags 03EK and 06YY
(blueprint: lem-sfb-scalar-tensor-ordinary-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ChangeOfRings
namespace AlgebraicGeometry.Scheme.DerivedScalarMate
attribute [local irreducible] SheafOfModules.monoidalCategory

/-- The actual scalar restriction, with unchanged underlying abelian sheaf.
Source: Stacks 03EK (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable abbrev restriction {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  Scheme.proEtaleRingRestrictScalars φ

/-- The coefficient B_W with its A_W action, without deriving or resolving B.
Source: Stacks 0B56 (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable abbrev coefficient {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (restriction φ).obj (SheafOfModules.unit
    ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B))

/-- The degree-zero coefficient complex B_W, as an A_W-module complex.
Source: Stacks 0B56 (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable abbrev coefficientComplex {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (CochainComplex.singleFunctor (Scheme.proEtaleRingModules W
    A) (0 : ℤ)).obj (coefficient φ)

/-- The existing ordinary tensor with B as its last factor.
Source: Stacks 03EK (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable abbrev ordinaryTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  (Scheme.proEtaleOrdinaryTensor W A).flip.obj
    (coefficient φ)

/-- The original sheafification image of b tensor m in scalar extension.
Source: Stacks 03EK (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable def pureSection {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U)
    (m : M.val.obj U) :
    (SheafOfModules.changeOfRings φ M).val.obj U :=
  (((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B)
    (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1}
            φ M)).app U)
    (b ⊗ₜ[_, (φ.hom.app U).hom] m)

/-- The normalization on all sectionwise pure tensors, including nonconstant local scalars.
Source: Stacks 03EK (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
def IsOrdinaryTensor {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (e : Scheme.proEtaleRingExtension φ ⋙
      restriction φ ≅ ordinaryTensor φ) : Prop :=
  ∀ (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U)
    (m : M.val.obj U),
    ((restriction φ).map
      (eqToHom (Scheme.proEtaleRingExtension_obj
        φ M).symm) ≫
      e.hom.app M).val.app U (pureSection φ M U b m) =
        Scheme.proEtaleTensorPair W A M
          (coefficient φ) U m b

private theorem tensorPair_hom_ext {W : Scheme.{u}}
    (A : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1})
    {M N H : Scheme.proEtaleRingModules W A}
    {v w : ((Scheme.proEtaleOrdinaryTensor W A).obj M).obj N ⟶ H}
    (h : ∀ U m n, v.val.app U (Scheme.proEtaleTensorPair W A M N U m n) =
      w.val.app U (Scheme.proEtaleTensorPair W A M N U m n)) : v = w := by
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply ((PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj A).obj)).homEquiv
        (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  exact h U

private theorem pureSection_toSheafify {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
    pureSection φ M U b m =
      (toSheafify (Scheme.ProEt.topology W)
        (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
          (b ⊗ₜ[_, (φ.hom.app U).hom] m) := by
  have h :=
    PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app.{u + 1, u, u + 1, u + 1}
    (J := Scheme.ProEt.topology W)
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M)
  exact congrArg (fun q ↦ q.app U (b ⊗ₜ[_, (φ.hom.app U).hom] m)) h

private theorem pureSection_map {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N)
    (U : W.ProEtᵒᵖ) (b : B.obj.obj U) (m : M.val.obj U) :
    (SheafOfModules.changeOfRingsHom φ M v).val.app U (pureSection φ M U b m) =
      pureSection φ N U b (v.val.app U m) := by
  let adj := PresheafOfModules.sheafificationAdjunction.{u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology W)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj B).obj)
  let q : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M ⟶
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ N :=
    { app := fun V ↦ (ModuleCat.extendScalars (φ.hom.app V).hom).map (v.val.app V)
      naturality := SheafOfModules.changeOfRingsHom_naturality φ M v }
  exact (congrArg (fun k ↦ k.app U (b ⊗ₜ[_, (φ.hom.app U).hom] m))
    (adj.unit.naturality q)).symm

private theorem extension_map_eq {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N) :
    (Scheme.proEtaleRingExtension φ).map v =
      eqToHom (Scheme.proEtaleRingExtension_obj φ M) ≫
        SheafOfModules.changeOfRingsHom φ M v ≫
          eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm := by
  exact (Scheme.reductionChangeExistence W φ).choose_spec.choose_spec.choose v

private noncomputable def ordinaryComponent {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A) :
    (ordinaryTensor φ).obj M ≅
      (restriction φ).obj ((Scheme.proEtaleRingExtension φ).obj M) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  exact (BraidedCategory.braiding M (coefficient φ)) ≪≫
    (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M).choose ≪≫
      (restriction φ).mapIso (eqToIso (Scheme.proEtaleRingExtension_obj φ M).symm)

private theorem ordinaryComponent_hom {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A) :
    letI := SheafOfModules.monoidalCategory A
    letI := SheafOfModules.symmetricCategory A
    (ordinaryComponent φ M).hom =
      (BraidedCategory.braiding M (coefficient φ)).hom ≫
        (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
          φ M).choose.hom ≫
        (restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm) := by
  simp only [ordinaryComponent, Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]

attribute [local irreducible] ordinaryComponent

private theorem ordinaryComponent_pure {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) (M : Scheme.proEtaleRingModules W A)
    (U : W.ProEtᵒᵖ) (m : M.val.obj U) (b : B.obj.obj U) :
    (ordinaryComponent φ M).hom.val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
      ((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m) := by
  let := SheafOfModules.monoidalCategory A
  let := SheafOfModules.symmetricCategory A
  have he :=
    (SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison φ M).choose_spec
      U b m
  have hb := CategoryTheory.CochainPullback.moduleTmul_braiding M (coefficient φ) U m b
  rw [ordinaryComponent_hom]
  change ((restriction φ).map
      (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
    (((SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
      φ M).choose).hom.val.app U
      ((BraidedCategory.braiding M (coefficient φ)).hom.val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))) = _
  rw [show (BraidedCategory.braiding M (coefficient φ)).hom.val.app U
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
        Scheme.proEtaleTensorPair W A (coefficient φ) M U b m from hb]
  rw [show ((SheafOfModules.IndependentExtensionTensor.exists_extensionTensorComparison
      φ M).choose).hom.val.app U
        (Scheme.proEtaleTensorPair W A (coefficient φ) M U b m) = _ from he]
  rw [pureSection_toSheafify]

private theorem ordinaryComponent_naturality {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) {M N : Scheme.proEtaleRingModules W A} (v : M ⟶ N) :
    (ordinaryTensor φ).map v ≫ (ordinaryComponent φ N).hom =
      (ordinaryComponent φ M).hom ≫
        (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v) := by
  let := SheafOfModules.monoidalCategory A
  apply tensorPair_hom_ext A
  intro U m b
  have ht := CategoryTheory.CochainPullback.moduleTmul_map v (𝟙 (coefficient φ)) U m b
  simp only [MonoidalCategory.tensorHom_id, SheafOfModules.id_val,
    PresheafOfModules.id_app, ModuleCat.id_apply] at ht
  change (ordinaryComponent φ N).hom.val.app U
      (((ordinaryTensor φ).map v).val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) =
    ((restriction φ).map ((Scheme.proEtaleRingExtension φ).map v)).val.app U
      ((ordinaryComponent φ M).hom.val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))
  rw [show (((ordinaryTensor φ).map v).val.app U)
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
        Scheme.proEtaleTensorPair W A N (coefficient φ) U (v.val.app U m) b from ht]
  rw [ordinaryComponent_pure, ordinaryComponent_pure]
  have hcomp :
      (restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm) ≫
        (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v) =
      (restriction φ).map (SheafOfModules.changeOfRingsHom φ M v) ≫
        (restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm) := by
    rw [← Functor.map_comp, extension_map_eq]
    simp only [← Category.assoc, eqToHom_trans, eqToHom_refl, Category.id_comp,
      Functor.map_comp]
  change _ = (((restriction φ).map
    (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm) ≫
      (restriction φ).map ((Scheme.proEtaleRingExtension φ).map v)).val.app U)
        (pureSection φ M U b m)
  rw [hcomp]
  change _ = (eqToHom (Scheme.proEtaleRingExtension_obj φ N).symm).val.app U
    ((SheafOfModules.changeOfRingsHom φ M v).val.app U (pureSection φ M U b m))
  rw [pureSection_map]
  rfl

/-- The canonical ordinary identification, uniquely fixed by balanced pure tensors.
Source: Stacks 03EK, 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-normalization).
Proof: the restricted scalar extension and tensor have the same balanced tensor
abelian presheaf, with factors reversed. Sheafify this identification. The inverse
reverses the factors back; both composites fix pure tensors. The balancing relation
proves linearity, and id tensor a proves naturality. Sheafification uniqueness proves
that the displayed formula determines the natural isomorphism uniquely. This is
step 1 of the node, retaining its specified normalization. -/
theorem ordinaryTensorIso_existsUnique
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :
    ∃! e : Scheme.proEtaleRingExtension φ ⋙
        restriction φ ≅ ordinaryTensor φ,
      IsOrdinaryTensor φ e := by
  let c : ordinaryTensor φ ≅ Scheme.proEtaleRingExtension φ ⋙ restriction φ :=
    NatIso.ofComponents (ordinaryComponent φ) (fun v ↦ ordinaryComponent_naturality φ v)
  have hc : ∀ (M : Scheme.proEtaleRingModules W A) (U : W.ProEtᵒᵖ)
      (b : B.obj.obj U) (m : M.val.obj U),
      (c.hom.app M).val.app U
        (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b) =
      ((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m) := fun M U b m ↦ ordinaryComponent_pure φ M U m b
  have hn : IsOrdinaryTensor φ c.symm := by
    intro M U b m
    change (c.inv.app M).val.app U
      (((restriction φ).map (eqToHom (Scheme.proEtaleRingExtension_obj φ M).symm)).val.app U
        (pureSection φ M U b m)) = _
    rw [← hc]
    exact congrArg (fun v ↦ v.val.app U
      (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) (c.hom_inv_id_app M)
  refine ⟨c.symm, hn, ?_⟩
  intro e he
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (cancel_epi (c.hom.app M)).mp
  change c.hom.app M ≫ e.hom.app M = c.hom.app M ≫ c.inv.app M
  apply tensorPair_hom_ext A
  intro U m b
  change (e.hom.app M).val.app U
      ((c.hom.app M).val.app U (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b)) =
    (c.inv.app M).val.app U
      ((c.hom.app M).val.app U (Scheme.proEtaleTensorPair W A M (coefficient φ) U m b))
  rw [hc]
  exact (he M U b m).trans (hn M U b m).symm

/-- The uniquely normalized ordinary identification; its data are determined by the formula.
Source: Stacks 03EK (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable def ordinaryTensorIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B) :=
  Classical.choose (ordinaryTensorIso_existsUnique φ).exists

/-- On complexes, reverse the balanced tensors degreewise and use the degree-zero
single-factor identification. This is an actual chain isomorphism.
Source: Stacks 06YY (blueprint: lem-sfb-scalar-tensor-ordinary-normalization). -/
noncomputable def ordinaryComplexIso
    {W : Scheme.{u}}
    {A B : Sheaf (Scheme.ProEt.topology W) CommRingCat.{u + 1}}
    (φ : A ⟶ B)
    (P : CochainComplex (Scheme.proEtaleRingModules W A) ℤ) :=
  (Functor.mapHomologicalComplexCompIso (ordinaryTensorIso φ)
    (ComplexShape.up ℤ)).app P ≪≫
      (CochainComplex.mapBifunctorSingle₂Iso
        (Scheme.proEtaleOrdinaryTensor W A)
        (coefficient φ) P).symm

end AlgebraicGeometry.Scheme.DerivedScalarMate

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedCalculusSupplement
import all WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
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
/-!
# Tensor compatibility of ordinary horizontal reduction adjoints

Source: Zheng Construction 4.1; Stacks 03EK, 03CZ, 06YY.
(blueprint: lem-pur-system-ordinary-tensor-reduction).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe c v r a b
open CategoryTheory CategoryTheory.Limits
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
open Opposite MonoidalCategory
open scoped ChangeOfRings
namespace WeilConjectures.SemilinearSections
variable {C : Type c} [Category.{v} C] [EssentiallySmall.{max c v r} C]
  (J : GrothendieckTopology C) {R R' : Sheaf J CommRingCat.{max c v r}}
  (φ : R ⟶ R') (S : ScalarData.{c, v, max c v r} φ)

private theorem unit_section' (M : Mod.{c, v, max c v r} J R) (U : Cᵒᵖ)
    (x : M.val.obj U) :
    (S.ordinaryAdjunction.unit.app M).val.app U x =
      scalarExtensionSection.{c, v, r} φ S M U x := by
  have h := S.unit_section M U x
  dsimp only [scalarExtensionSection]
  rw [← h]
  change _ = ((eqToHom (S.model.obj_eq M) ≫
    eqToHom (S.model.obj_eq M).symm).val.app U) _
  simp

private theorem tensor_hom_ext (M N H : Mod.{c, v, max c v r} J R)
    {f g : ordinaryTensor.{c, v, r} J R M N ⟶ H}
    (h : ∀ U x y, f.val.app U (tensorSection.{c, v, r} J R M N U x y) =
      g.val.app U (tensorSection.{c, v, r} J R M N U x y)) : f = g := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let adj := PresheafOfModules.sheafificationAdjunction
    (𝟙 (ring.{c, v, max c v r} J R).obj)
  apply (cancel_epi (SheafOfModules.tensorObjIsoSheafification M N).inv).mp
  apply (adj.homEquiv (M.val ⊗ N.val) H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  exact h U x y

private theorem tensorSection_restrict (M N : Mod.{c, v, max c v r} J R)
    {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.val.obj U) (y : N.val.obj U) :
    (ordinaryTensor.{c, v, r} J R M N).val.map f
        (tensorSection.{c, v, r} J R M N U x y) =
      tensorSection.{c, v, r} J R M N V (M.val.map f x) (N.val.map f y) := by
  let := SheafOfModules.isMonoidal_W_independentCoefficients R
  let := SheafOfModules.monoidalCategory R
  let a : M.val ⊗ N.val ⟶ (ordinaryTensor.{c, v, r} J R M N).val :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (ring.{c, v, max c v r} J R).obj)).unit.app (M.val ⊗ N.val) ≫
        (SheafOfModules.tensorObjIsoSheafification M N).inv.val
  have h := (PresheafOfModules.naturality_apply a f (x ⊗ₜ[R.obj.obj U] y)).symm
  erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at h
  exact h

private theorem tensorSection_map
    {M N M' N' : Mod.{c, v, max c v r} J R} (f : M ⟶ M') (g : N ⟶ N')
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (ordinaryTensorHom.{c, v, r} J R f g).val.app U
        (tensorSection.{c, v, r} J R M N U x y) =
      tensorSection.{c, v, r} J R M' N' U (f.val.app U x) (g.val.app U y) := by
  exact SheafOfModules.CochainScalarConstruction.pure_map R f g U x y

private theorem transpose_section (M : Mod.{c, v, max c v r} J R)
    (N : Mod.{c, v, max c v r} J R') (f : S.model.E.obj M ⟶ N)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    ((S.ordinaryAdjunction.homEquiv M N) f).val.app U x =
      f.val.app U (scalarExtensionSection.{c, v, r} φ S M U x) := by
  rw [Adjunction.homEquiv_unit]
  change f.val.app U ((S.ordinaryAdjunction.unit.app M).val.app U x) = _
  rw [unit_section'.{c, v, r} J φ S]

private theorem scalar_tensor_transpose_section
    (ordinary : ∀ M N : Mod.{c, v, max c v r} J R,
      S.model.E.obj (ordinaryTensor.{c, v, r} J R M N) ≅
        ordinaryTensor.{c, v, r} J R' (S.model.E.obj M) (S.model.E.obj N))
    (hpure : ScalarTensorPure.{c, v, r} φ S ordinary)
    (M N : Mod.{c, v, max c v r} J R) (X Y : Mod.{c, v, max c v r} J R')
    (f : S.model.E.obj M ⟶ X) (g : S.model.E.obj N ⟶ Y)
    (U : Cᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    ((S.ordinaryAdjunction.homEquiv _ _)
      ((ordinary M N).hom ≫ ordinaryTensorHom.{c, v, r} J R' f g)).val.app U
        (tensorSection.{c, v, r} J R M N U x y) =
      tensorSection.{c, v, r} J R' X Y U
        (((S.ordinaryAdjunction.homEquiv _ _) f).val.app U x)
        (((S.ordinaryAdjunction.homEquiv _ _) g).val.app U y) := by
  rw [transpose_section.{c, v, r} J φ S]
  change (ordinaryTensorHom.{c, v, r} J R' f g).val.app U
      ((ordinary M N).hom.val.app U _) = _
  rw [hpure M N U x y, tensorSection_map.{c, v, r} J]
  rw [transpose_section.{c, v, r} J φ S, transpose_section.{c, v, r} J φ S]

attribute [local irreducible] evaluation
variable (B : ℕ → Sheaf J CommRingCat.{max c v r})
  (τ : ∀ n : ℕ, B (n + 1) ⟶ B n)

private theorem evaluation_carrier (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) :
    (↑(((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) : Type (max c v r)) =
      ↑(M.val.obj (op (n, U.unop))) := by
  unfold evaluation
  rfl

private theorem evaluation_pure (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop)))
    (x' : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U)
    (y' : ((evaluation.{c, v, max c v r} J B τ n).obj N).val.obj U)
    (z : ((evaluation.{c, v, max c v r} J B τ n).obj
      (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
        (systemRing.{c, v, max c v r} J B τ) M N)).val.obj U)
    (hx : HEq x x') (hy : HEq y y')
    (hz : HEq z (tensorSection.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop)) x y)) :
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U z =
      tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U x' y' := by
  exact (ordinaryEvaluationTensor_existsUnique.{c, v, r} J B τ n).exists.choose_spec
    M N U x y x' y' z hx hy hz

private def evalSection (n : ℕ) (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) :
    ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U :=
  cast (evaluation_carrier.{c, v, r} J B τ n M U).symm x

private theorem evalSection_heq (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    HEq (evalSection.{c, v, r} J B τ n M U x) x := by
  exact cast_heq _ _

private theorem evaluation_pure_cast (n : ℕ) (M N : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (x : M.val.obj (op (n, U.unop)))
    (y : N.val.obj (op (n, U.unop))) :
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
      (evalSection.{c, v, r} J B τ n _ U
        (tensorSection.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop)) x y)) =
      tensorSection.{c, v, r} J (B n)
        ((evaluation.{c, v, max c v r} J B τ n).obj M)
        ((evaluation.{c, v, max c v r} J B τ n).obj N) U
        (evalSection.{c, v, r} J B τ n M U x)
        (evalSection.{c, v, r} J B τ n N U y) := by
  exact evaluation_pure.{c, v, r} J B τ n M N U x y _ _ _
    (evalSection_heq.{c, v, r} J B τ n M U x).symm
    (evalSection_heq.{c, v, r} J B τ n N U y).symm
    (evalSection_heq.{c, v, r} J B τ n _ U _)

private theorem heq_apply {A A' : Type a} {B B' : Type b} {f : A → B} {g : A' → B'}
    (hB : B = B') (hf : HEq f g) {x : A} {x' : A'} (hx : HEq x x') : HEq (f x) (g x') := by
  cases hB
  exact heq_of_eq (congr_heq hf hx)

private theorem transition_apply_cast {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (m, U.unop))) :
    ((transition.{c, v, max c v r} J B τ h).app M).val.app U
        (evalSection.{c, v, r} J B τ m M U x) =
      evalSection.{c, v, r} J B τ n M U
        (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x) := by
  have ht := (transition_exists.{c, v, max c v r} J B τ h).exists.choose_spec M U
  have hx := evalSection_heq.{c, v, r} J B τ m M U x
  have hn := evaluation_carrier.{c, v, r} J B τ n M U
  have hh := heq_apply hn ht hx
  have hy := evalSection_heq.{c, v, r} J B τ n M U
    (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
  exact eq_of_heq (hh.trans hy.symm)

/-- The ordinary scalar-adjunction transpose of the actual horizontal restriction.
Source: Zheng Construction 4.1; Stacks 03CZ, 06YY
(blueprint: lem-pur-system-ordinary-tensor-reduction). -/
def ordinaryReduction (A : Data.{c, v, r} J B τ) {m n : ℕ} (h : n ≤ m)
    (M : Systems.{c, v, max c v r} J B τ) :
    (A.scalar h).model.E.obj ((evaluation.{c, v, max c v r} J B τ m).obj M) ⟶
      (evaluation.{c, v, max c v r} J B τ n).obj M :=
  ((A.scalar h).ordinaryAdjunction.homEquiv _ _).symm
    ((transition.{c, v, max c v r} J B τ h).app M)

private theorem evalSection_surjective (n : ℕ) (M : Systems.{c, v, max c v r} J B τ)
    (U : Cᵒᵖ) (x' : ((evaluation.{c, v, max c v r} J B τ n).obj M).val.obj U) :
    ∃ x, evalSection.{c, v, r} J B τ n M U x = x' := by
  refine ⟨cast (evaluation_carrier.{c, v, r} J B τ n M U) x', ?_⟩
  simp only [evalSection, cast_cast, cast_eq]

private theorem evaluation_inv_pure_cast (n : ℕ)
    (M N : Systems.{c, v, max c v r} J B τ) (U : Cᵒᵖ)
    (x : M.val.obj (op (n, U.unop))) (y : N.val.obj (op (n, U.unop))) :
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv.val.app U
        (tensorSection.{c, v, r} J (B n)
          ((evaluation.{c, v, max c v r} J B τ n).obj M)
          ((evaluation.{c, v, max c v r} J B τ n).obj N) U
          (evalSection.{c, v, r} J B τ n M U x)
          (evalSection.{c, v, r} J B τ n N U y)) =
      evalSection.{c, v, r} J B τ n _ U
        (tensorSection.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N (op (n, U.unop)) x y) := by
  rw [← evaluation_pure_cast.{c, v, r} J B τ n M N U x y]
  change (((ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom ≫
    (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).inv).val.app U) _ = _
  rw [Iso.hom_inv_id]
  rfl

attribute [local irreducible] ordinaryTensorHom tensorSection

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Ordinary reduction commutes with tensor under the canonical comparisons.
Source: Zheng Construction 4.1; Stacks 03EK, 03CZ, 06YY
(blueprint: lem-pur-system-ordinary-tensor-reduction).
Proof: transpose both maps through extension/restriction adjunction. Precompose with
inverse tensor evaluation and test on pure tensors, which generate the sheafified
module tensor. The adjunction unit sends x to its scalar-extension section. The
ordinary scalar comparison sends the extension of x tensor y to the tensor of the
two extended sections. Horizontal restriction commutes with pure tensor sections,
and evaluation's comparison is the identity on these sections. Thus the two
transposes agree on pure sections, hence on the whole tensor sheaf. -/
theorem ordinary_tensor_reduction (A : Data.{c, v, r} J B τ) {m n : ℕ}
    (h : n ≤ m) (M N : Systems.{c, v, max c v r} J B τ) :
    ordinaryReduction.{c, v, r} J B τ A h
        (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
          (systemRing.{c, v, max c v r} J B τ) M N) ≫
      (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom =
    (A.scalar h).model.E.map
        (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).hom ≫
      ((A.scalarTensorModel h).ordinary
        ((evaluation.{c, v, max c v r} J B τ m).obj M)
        ((evaluation.{c, v, max c v r} J B τ m).obj N)).hom ≫
      ordinaryTensorHom.{c, v, r} J (B n)
        (ordinaryReduction.{c, v, r} J B τ A h M)
        (ordinaryReduction.{c, v, r} J B τ A h N) := by
  apply ((A.scalar h).ordinaryAdjunction.homEquiv _ _).injective
  rw [(A.scalar h).ordinaryAdjunction.homEquiv_naturality_right,
    (A.scalar h).ordinaryAdjunction.homEquiv_naturality_left]
  simp only [ordinaryReduction, Equiv.apply_symm_apply]
  apply (cancel_epi (ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv).1
  simp only [Iso.inv_hom_id_assoc]
  apply tensor_hom_ext.{c, v, r} J
  intro U x y
  obtain ⟨x, rfl⟩ := evalSection_surjective.{c, v, r} J B τ m M U x
  obtain ⟨y, rfl⟩ := evalSection_surjective.{c, v, r} J B τ m N U y
  change (ordinaryEvaluationTensor.{c, v, r} J B τ n M N).hom.val.app U
    (((transition.{c, v, max c v r} J B τ h).app _).val.app U
      ((ordinaryEvaluationTensor.{c, v, r} J B τ m M N).inv.val.app U
        (tensorSection.{c, v, r} J (B m) _ _ U _ _))) = _
  rw [evaluation_inv_pure_cast.{c, v, r} J B τ m M N U x y]
  rw [transition_apply_cast.{c, v, r} J B τ h
    (ordinaryTensor.{c, v, r} (coefficientSequenceTopology J)
      (systemRing.{c, v, max c v r} J B τ) M N) U]
  rw [tensorSection_restrict.{c, v, r} (coefficientSequenceTopology J)
    (R := systemRing.{c, v, max c v r} J B τ) M N
    (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x y]
  erw [evaluation_pure_cast.{c, v, r} J B τ n M N U
    (M.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op x)
    (N.val.map (Prod.mkHom (homOfLE h) (𝟙 U.unop)).op y)]
  have ht := scalar_tensor_transpose_section.{c, v, r} J (coefficientMap J B τ h)
    (A.scalar h) (A.scalarTensorModel h).ordinary (A.scalarTensorModel h).ordinary_pure
    ((evaluation.{c, v, max c v r} J B τ m).obj M)
    ((evaluation.{c, v, max c v r} J B τ m).obj N)
    ((evaluation.{c, v, max c v r} J B τ n).obj M)
    ((evaluation.{c, v, max c v r} J B τ n).obj N)
    (ordinaryReduction.{c, v, r} J B τ A h M)
    (ordinaryReduction.{c, v, r} J B τ A h N) U
    (evalSection.{c, v, r} J B τ m M U x) (evalSection.{c, v, r} J B τ m N U y)
  simp only [ordinaryReduction, Equiv.apply_symm_apply] at ht
  have hx := transition_apply_cast.{c, v, r} J B τ h M U x
  have hy := transition_apply_cast.{c, v, r} J B τ h N U y
  rw [hx, hy] at ht
  exact ht.symm

end WeilConjectures.SemilinearSections

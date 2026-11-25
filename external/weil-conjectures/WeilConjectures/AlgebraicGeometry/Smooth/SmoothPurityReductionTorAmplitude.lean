/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerData
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.CategoryTheory.RingObjects.Ab
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.CategoryTheory.SheafTensor
import WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor

set_option linter.privateModule false

/-! Tor-amplitude transport for the normalized smooth-purity reduction tower.
Source: blueprint latest, normalized-towers, uniform Tor and cohomological bounds.
(blueprint: lem-sp-reduction-tower-tor-intervals).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

private theorem integral_coefficient_iso :
    ∃ F : PadicAlgCl.FiniteIntermediateField l,
      Nonempty (Mon.mk (spIntegralCondensed l E) ≅
        Mon.mk (Profinite.padicIntegersRingObj l F)) := by
  let f : E →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  let F : PadicAlgCl.FiniteIntermediateField l :=
    ⟨f.fieldRange, f.equivFieldRange.toLinearEquiv.finiteDimensional⟩
  let : FiniteDimensional ℚ_[l] F := F.property
  let e : E ≃ₐ[ℚ_[l]] F := f.equivFieldRange
  let := spectralNorm.normedField ℚ_[l] E
  let := PadicAlgCl.normedFieldOfAlgebra l F
  have hn (x : E) : Padic.coefficientExtensionAbsoluteValue l E x = ‖f x‖ := by
    let a : AbsoluteValue E ℝ :=
      { toFun := fun x ↦ ‖f x‖
        map_mul' := fun x y ↦ by rw [map_mul, norm_mul]
        nonneg' := fun x ↦ norm_nonneg _
        eq_zero' := fun x ↦ by simp only [norm_eq_zero, map_eq_zero_iff f f.injective]
        add_le' := fun x y ↦ by rw [map_add]; exact norm_add_le _ _ }
    have ha (y : ℚ_[l]) : a (algebraMap ℚ_[l] E y) = ‖y‖ := by
      change ‖f (algebraMap ℚ_[l] E y)‖ = ‖y‖
      rw [f.commutes]
      exact PadicAlgCl.norm_extends l y
    exact (spectralNorm_unique_field_norm_ext ha x).symm
  have hm (x : E) : x ∈ Padic.coefficientExtensionIntegers l E ↔
      e x ∈ PadicAlgCl.integers l F := by
    have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec.1 x
    rw [hn] at h
    exact h.trans (by
      rw [PadicAlgCl.mem_integers_iff, ← NNReal.coe_le_coe]
      rfl)
  let t : Padic.coefficientExtensionIntegers l E ≃+* PadicAlgCl.integers l F :=
    { toFun := fun x ↦ ⟨e x.val, (hm x.val).mp x.property⟩
      invFun := fun x ↦ ⟨e.symm x.val, (hm _).mpr (by
        simpa only [e.apply_symm_apply] using x.property)⟩
      left_inv := fun x ↦ Subtype.ext (e.symm_apply_apply x.val)
      right_inv := fun x ↦ Subtype.ext (e.apply_symm_apply x.val)
      map_add' := fun x y ↦ Subtype.ext (e.map_add x.val y.val)
      map_mul' := fun x y ↦ Subtype.ext (e.map_mul x.val y.val) }
  have ht : Isometry t := by
    apply Isometry.of_dist_eq
    intro x y
    change ‖f x.val - f y.val‖ = Padic.coefficientExtensionAbsoluteValue l E (x.val - y.val)
    rw [← map_sub, hn]
  have hti : Continuous t.symm := (show _ ≃ᵢ _ from ⟨t.toEquiv, ht⟩).symm.continuous
  let q : Profinite.continuousMapRingSheafOfUniverse.{u, u}
        (Padic.coefficientExtensionIntegers l E) ≅
      Profinite.padicIntegersCondensedRing.{u} l F :=
    { hom := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.toRingHom.compLeftContinuous _ ht.continuous).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      inv := ⟨{
        app := fun _ ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((t.symm.toRingHom.compLeftContinuous _ hti).comp ULift.ringEquiv.toRingHom))
        naturality := by intros; rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.symm_apply_apply (x.down z)
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro z
        exact t.apply_symm_apply (x.down z) }
  let G := sheafCompose (coherentTopology Profinite.{u}) (forget₂ RingCat Ab)
  have : IsMonHom (G.mapIso q).hom :=
    Sheaf.isMonHom_sheafCompose_map (coherentTopology Profinite.{u}) q.hom
  exact ⟨F, ⟨Mon.mkIso' (G.mapIso q)⟩⟩

end AlgebraicGeometry.ProEtale

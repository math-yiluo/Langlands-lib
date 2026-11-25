/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.StrictCompletionRestriction.StrictCompletionRestrictionData
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
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
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import all WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import all Mathlib.RingTheory.Ideal.Quotient.Index
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import all WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import all Mathlib.Topology.Category.Profinite.EffectiveEpi
import all WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import all Mathlib.Condensed.TopComparison
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import all Mathlib.Topology.Algebra.Ring.Ideal
import all Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import all WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import all WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import all Mathlib.Algebra.Homology.ShortComplex.Ab
import all WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import all Mathlib.Topology.Bases
import all Mathlib.Topology.MetricSpace.Pseudo.Defs
import all Mathlib.Analysis.SpecificLimits.Basic
import all Mathlib.Topology.LocallyConstant.Basic
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import all WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import all Mathlib.CategoryTheory.Center.Linear
import all Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import all WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import all Mathlib.Topology.Algebra.Order.Field
import all WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import all Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import all Mathlib.Algebra.Order.AbsoluteValue.Basic
import all Mathlib.LinearAlgebra.FiniteDimensional.Basic
import all Mathlib.NumberTheory.Padics.PadicNumbers
import all Mathlib.RingTheory.DiscreteValuationRing.Basic
import all Mathlib.RingTheory.Localization.FractionRing
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import all Mathlib.Analysis.Normed.Algebra.Ultra
import all Mathlib.Analysis.Normed.Module.FiniteDimension
import all Mathlib.NumberTheory.Padics.ProperSpace
import all Mathlib.Topology.Algebra.Valued.LocallyCompact
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import all WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import all WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
/-! # StrictCompletionFiniteConstantModels -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe a b c d
namespace AlgebraicGeometry.ProEtale.StrictCompletionRestriction
variable {A : Type a} [Category.{b} A] [Abelian A] [HasFiniteBiproducts A]
  {B : Type c} [Category.{d} B] [Abelian B] [HasFiniteBiproducts B]
  (G : A ⥤ B) [G.Additive] [PreservesFiniteColimits G]
  {R : A} {U : B} (e : G.obj R ≅ U)
private def freeComparison (n : ℕ) :
    G.obj (⨁ fun _ : Fin n ↦ R) ≅ ⨁ fun _ : Fin n ↦ U :=
  G.mapBiproduct _ ≪≫ biproduct.mapIso (fun _ ↦ e)

omit [PreservesFiniteColimits G] in
private theorem freeComparison_π (n : ℕ) (i : Fin n) :
    (freeComparison G e n).hom ≫ biproduct.π (fun _ : Fin n ↦ U) i =
      G.map (biproduct.π (fun _ : Fin n ↦ R) i) ≫ e.hom := by
  simp [freeComparison]

omit [PreservesFiniteColimits G] in
private theorem freeComparison_ι (n : ℕ) (i : Fin n) :
    G.map (biproduct.ι (fun _ : Fin n ↦ R) i) ≫ (freeComparison G e n).hom =
      e.hom ≫ biproduct.ι (fun _ : Fin n ↦ U) i := by
  apply biproduct.hom_ext
  intro j
  simp only [Category.assoc, freeComparison_π]
  rw [← G.map_comp_assoc, biproduct.ι_π, biproduct.ι_π]
  split_ifs <;> simp_all

omit [PreservesFiniteColimits G] in
private theorem matrix_entries {m n : ℕ}
    (f : (⨁ fun _ : Fin m ↦ R) ⟶ ⨁ fun _ : Fin n ↦ R) (j : Fin m) (k : Fin n) :
    biproduct.ι (fun _ : Fin m ↦ U) j ≫
      (freeComparison G e m).inv ≫ G.map f ≫ (freeComparison G e n).hom ≫
      biproduct.π (fun _ : Fin n ↦ U) k =
    e.inv ≫ G.map (biproduct.ι (fun _ : Fin m ↦ R) j ≫ f ≫
      biproduct.π (fun _ : Fin n ↦ R) k) ≫ e.hom := by
  have hι : biproduct.ι (fun _ : Fin m ↦ U) j ≫ (freeComparison G e m).inv =
      e.inv ≫ G.map (biproduct.ι (fun _ : Fin m ↦ R) j) := by
    apply (cancel_mono (freeComparison G e m).hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, freeComparison_ι,
      Iso.inv_hom_id_assoc]
  rw [← Category.assoc, ← Category.assoc, ← Category.assoc, hι]
  rw [Category.assoc, Category.assoc, freeComparison_π]
  simp only [Functor.map_comp, Category.assoc]

private theorem matrix_models (M : B) :
    (∃ (P : A) (n m : ℕ)
      (f : (⨁ fun _ : Fin m ↦ R) ⟶ ⨁ fun _ : Fin n ↦ R),
      Nonempty (P ≅ cokernel f) ∧ Nonempty (M ≅ G.obj P)) ↔
    ∃ (m n : ℕ) (a : Fin m → Fin n → End R)
      (f : (⨁ fun _ : Fin m ↦ U) ⟶ ⨁ fun _ : Fin n ↦ U),
      (∀ j k, biproduct.ι _ j ≫ f ≫ biproduct.π _ k = e.inv ≫ G.map (a j k).asHom ≫ e.hom) ∧
      Nonempty (M ≅ cokernel f) := by
  constructor
  · rintro ⟨P, n, m, f, ⟨hP⟩, ⟨hM⟩⟩
    let f' := (freeComparison G e m).inv ≫ G.map f ≫ (freeComparison G e n).hom
    refine ⟨m, n, (fun j k ↦ .of (biproduct.ι (fun _ : Fin m ↦ R) j ≫ f ≫
      biproduct.π (fun _ : Fin n ↦ R) k)), f', ?_, ?_⟩
    · intro j k
      simpa only [f', Category.assoc] using matrix_entries G e f j k
    · exact ⟨hM ≪≫ G.mapIso hP ≪≫ PreservesCokernel.iso G f ≪≫
        cokernel.mapIso (G.map f) f' (freeComparison G e m) (freeComparison G e n)
          (by simp [f'])⟩
  · rintro ⟨m, n, a, f, ha, ⟨hM⟩⟩
    let f₀ : (⨁ fun _ : Fin m ↦ R) ⟶ ⨁ fun _ : Fin n ↦ R :=
      biproduct.desc fun j ↦ biproduct.lift (fun k ↦ (a j k).asHom)
    have hf : (freeComparison G e m).inv ≫ G.map f₀ ≫
        (freeComparison G e n).hom = f := by
      apply biproduct.hom_ext'
      intro j
      apply biproduct.hom_ext
      intro k
      simp only [Category.assoc]
      rw [matrix_entries G e f₀ j k, ha j k]
      simp [f₀]
    refine ⟨cokernel f₀, n, m, f₀, ⟨Iso.refl _⟩, ?_⟩
    exact ⟨hM ≪≫ (cokernel.mapIso (G.map f₀) f
      (freeComparison G e m) (freeComparison G e n)
      (by rw [← hf]; simp)).symm ≪≫ (PreservesCokernel.iso G f₀).symm⟩
section ProEtale
universe u
open CategoryTheory.InternalAbelianSheafModule
open CategoryTheory.MonoidalCategory
open WeilConjectures
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
private abbrev pointSectionFunctor (X : Scheme.{u}) :=
  DerivedNakayama.pullback l E X ⋙
    (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor
attribute [local instance] DerivedNakayama.pullbackFiniteLimits
  DerivedNakayama.pullbackFiniteColimits

private instance pointFunctorAdditive (X : Scheme.{u}) :
    (pointSectionFunctor l E X).Additive :=
  Functor.additive_of_preserves_binary_products _

private def pointRegularIso (X : Scheme.{u}) :
    (pointSectionFunctor l E X).obj (Mod.regular (DerivedNakayama.integerRing l E)) ≅
      SheafOfModules.unit
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X)) :=
  (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E) X).functor.mapIso
    (DerivedNakayama.regularPullbackIso l E X) ≪≫
      comparison_unitIso (Scheme.ProEt.topology X)
        (condensedRingObj (DerivedNakayama.integerRing l E) X)

private theorem pointScalarValue (X : Scheme.{u})
    (d : End (Mod.regular (DerivedNakayama.integerRing l E))) (U : X.ProEtᵒᵖ)
    (x : (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U) :
    (((pointRegularIso l E X).inv ≫ (pointSectionFunctor l E X).map d.asHom ≫
      (pointRegularIso l E X).hom).val.app U) x = sectionScalarValue l E X d U * x := by
  let f := (pointRegularIso l E X).inv ≫ (pointSectionFunctor l E X).map d.asHom ≫
    (pointRegularIso l E X).hom
  have hf : (f.val.app U) (1 :
    (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U) =
      sectionScalarValue l E X d U := by
    dsimp only [f, pointRegularIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.comp_map, Category.assoc]
    rfl
  change (f.val.app U) x = _
  calc
    (f.val.app U) x = (f.val.app U) (x • (1 :
      (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U)) := by
      simp only [smul_eq_mul, mul_one]
    _ = x • (f.val.app U) (1 :
        (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U) :=
      (f.val.app U).hom.map_smul x (1 :
        (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U)
    _ = sectionScalarValue l E X d U * x := by
      rw [hf]
      change x * sectionScalarValue l E X d U = _
      exact mul_comm _ _
private theorem pointMatrixModels (X : Scheme.{u})
    (M : ModuleObjectRingedComparison.Modules (DerivedNakayama.integerRing l E) X) :
    (∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
        (DerivedNakayama.integerRing l E),
      Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
      Nonempty (M ≅ (pointSectionFunctor l E X).obj P)) ↔
    ∃ (m n : ℕ) (a : Fin m → Fin n → End (Mod.regular (DerivedNakayama.integerRing l E)))
      (f : (⨁ fun _ : Fin m ↦ SheafOfModules.unit
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X))) ⟶
        ⨁ fun _ : Fin n ↦ SheafOfModules.unit
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X))),
      (∀ j k (U : X.ProEtᵒᵖ)
        (x : (ModuleObjectRingedComparison.ring (DerivedNakayama.integerRing l E) X).obj.obj U),
        ((biproduct.ι _ j ≫ f ≫ biproduct.π _ k).val.app U) x =
        sectionScalarValue l E X (a j k) U * x) ∧ Nonempty (M ≅ cokernel f) := by
  rw [show (∃ P, Mod.IsFinitelyPresented (DerivedNakayama.integerRing l E) P ∧
      Nonempty (M ≅ (pointSectionFunctor l E X).obj P)) ↔
    (∃ P, ∃ n m, ∃ (f : (⨁ fun _ : Fin m ↦ Mod.regular (DerivedNakayama.integerRing l E)) ⟶
      ⨁ fun _ : Fin n ↦ Mod.regular (DerivedNakayama.integerRing l E)),
      Nonempty (P ≅ cokernel f) ∧ Nonempty (M ≅ (pointSectionFunctor l E X).obj P)) by
        simp only [Mod.IsFinitelyPresented, Mod.finiteFree, exists_and_right]]
  rw [matrix_models (pointSectionFunctor l E X) (pointRegularIso l E X) M]
  apply exists_congr
  intro m
  apply exists_congr
  intro n
  apply exists_congr
  intro a
  apply exists_congr
  intro f
  apply and_congr_left
  intro _
  constructor
  · intro h j k U x
    rw [h j k]
    exact pointScalarValue l E X (a j k) U x
  · intro h j k
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (h j k U x).trans (pointScalarValue l E X (a j k) U x).symm

/-- The section-action equivalence identifies finite constant local models with the
specified finite scalar-matrix cokernel models on the actual pro-etale cover.

Source: blueprint Locality paragraph and Stacks Tags 03D7 and 03EK
(blueprint: lem-sfb-strict-completion-finite-constant-models).

Proof: An exact additive functor carries finite free biproducts and the cokernel of
any finite presentation to their canonical comparisons. Entries of the transported
matrix are the transported regular-module endomorphisms. On the section unit every
endomorphism is multiplication by its value at one, which is sectionScalarValue.
Conversely use the same matrix of point endomorphisms and cokernel preservation.
Full faithfulness reflects these cokernel models. Apply the inverse-image comparison
on every chart of the cover; the same cover proves both directions. -/
theorem strictCompletionFiniteConstantModels (X : Scheme.{u}) (M : AdicCompletion.Modules l E X) :
    HasFiniteConstantLocalModel (DerivedNakayama.integerRing l E) X M ↔
      HasSectionFiniteConstantLocalModel l E X
        ((ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E)
          X).functor.obj M) := by
  classical
  unfold HasFiniteConstantLocalModel HasSectionFiniteConstantLocalModel
  apply exists_congr
  intro 𝒰
  apply forall_congr'
  intro i
  rw [← pointMatrixModels]
  apply exists_congr
  intro P
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨e⟩
    exact ⟨((InternalModuleOperations.upperComparison (DerivedNakayama.integerRing l E)
      (𝒰.f i)).app M).symm ≪≫
      (ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E)
        (𝒰.X i)).functor.mapIso e⟩
  · rintro ⟨e⟩
    exact ⟨(ModuleObjectRingedComparison.equivalence (DerivedNakayama.integerRing l E)
      (𝒰.X i)).functor.preimageIso
        (((InternalModuleOperations.upperComparison (DerivedNakayama.integerRing l E)
          (𝒰.f i)).app M) ≪≫ e)⟩

end ProEtale

end AlgebraicGeometry.ProEtale.StrictCompletionRestriction

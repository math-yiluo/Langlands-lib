/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.StrictTower.StrictConstantTowerOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnityInverseImageSupplement
public import WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
public import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleRootsOfUnitySheafSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
public import Mathlib.Topology.Category.Profinite.EffectiveEpi
public import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
public import Mathlib.Condensed.TopComparison
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.Algebra.Homology.SignedLineDerivedBaseChange.SignedLineDerivedBaseChange
import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import all WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.AlgebraicGeometry.IntegralResidueOrdinaryTensorSquare
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.ProEtaleToposFunctorialityInverseImage
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasLeftKanExtension
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying

import all WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteScalarRestrictionConstructible
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.RootsOfUnityInverseImageIso
import all WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.AlgebraicGeometry.ProEtaleModelRingPresentation
import all WeilConjectures.CategoryTheory.SheafPullbackUnitPresentation
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all WeilConjectures.CategoryTheory.ModuleInverseImageAdjunction
import all WeilConjectures.CategoryTheory.ModuleInverseImageAction
import all Mathlib.Algebra.Category.Ring.Limits
import all WeilConjectures.CategoryTheory.ModuleInverseImageActionOfPresentations
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageUnitComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.CategoryTheory.TorsionSheafConstantModule
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Module.ZMod
import all WeilConjectures.AlgebraicGeometry.Tate.TateInverseLimitBaseChangeSupplement
import all WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import all WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import all WeilConjectures.CategoryTheory.Monoidal.Conjugate
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.EquivalenceAdjunctionComparisonSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.AlgebraicGeometry.CartesianCoefficientTwists
import WeilConjectures.AlgebraicGeometry.Native.NativeIntegralTateTowerLimit

/-! # Cartesian coefficients and Tate twists

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`sk-prop-sfb-cartesian-coefficients-twists.md`
(blueprint: lemma-inverse-image-coefficient-sheaves--2).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048

universe u u₁ v₁ u₂ v₂ uI vI uJ vJ

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj CategoryTheory.MonObj ChangeOfRings

private theorem comparisonIntoPreservedLimit
    {A B C D J : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category J]
    (U : A ⥤ C) (V : B ⥤ D) (F : C ⥤ D)
    (a : J ⥤ A) (b : J ⥤ B) [HasLimit a] [HasLimit b]
    [PreservesLimit b V] (α : a ⋙ U ⋙ F ⟶ b ⋙ V) :
    ∃! c : F.obj (U.obj (limit a)) ⟶ V.obj (limit b),
      ∀ j, c ≫ V.map (limit.π b j) = F.map (U.map (limit.π a j)) ≫ α.app j := by
  let s : Cone (b ⋙ V) :=
    { pt := F.obj (U.obj (limit a))
      π :=
        { app := fun j ↦ F.map (U.map (limit.π a j)) ≫ α.app j
          naturality := by
            intro i j g
            dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
            rw [Category.id_comp, Category.assoc, ← α.naturality g, ← Category.assoc]
            simp only [Functor.comp_map]
            rw [← F.map_comp, ← U.map_comp, limit.w] } }
  exact (isLimitOfPreserves V (limit.isLimit b)).existsUnique s

private theorem comparisonIntoPreservedLimit_isIso
    {A B C D J : Type*} [Category A] [Category B] [Category C] [Category D]
    [Category J]
    (U : A ⥤ C) (V : B ⥤ D) (F : C ⥤ D)
    (a : J ⥤ A) (b : J ⥤ B) [HasLimit a] [HasLimit b]
    [PreservesLimit b V] (α : a ⋙ U ⋙ F ⟶ b ⋙ V) [IsIso α]
    (hy : IsLimit (F.mapCone (U.mapCone (limit.cone a))))
    (c : F.obj (U.obj (limit a)) ⟶ V.obj (limit b))
    (hc : ∀ j, c ≫ V.map (limit.π b j) =
      F.map (U.map (limit.π a j)) ≫ α.app j) : IsIso c := by
  let cx := V.mapCone (limit.cone b)
  let cy := F.mapCone (U.mapCone (limit.cone a))
  let s := (Cone.postcompose α).obj cy
  have hx : IsLimit cx := isLimitOfPreserves V (limit.isLimit b)
  have hs : IsLimit s := (IsLimit.postcomposeHomEquiv (asIso α) cy).symm hy
  have he : c = hx.lift s := by
    apply hx.hom_ext
    intro j
    rw [hx.fac]
    exact hc j
  rw [he]
  exact (hx.nonempty_isLimit_iff_isIso_lift).mp ⟨hs⟩

private theorem conjugate_postcompose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B K L : C} {A' B' K' L' : D}
    (a : F.obj A ⟶ A') [IsIso a] (b : F.obj B ⟶ B')
    (k : F.obj K ⟶ K') (l : F.obj L ⟶ L')
    (p : A ⟶ K) (q : B ⟶ L) (p' : A' ⟶ K') (q' : B' ⟶ L')
    (s : A ⟶ B) (t : K ⟶ L) (t' : K' ⟶ L')
    (hp : F.map p ≫ k = a ≫ p') (hq : F.map q ≫ l = b ≫ q')
    (ht : F.map t ≫ l = k ≫ t') (hs : s ≫ q = p ≫ t) :
    (inv a ≫ F.map s ≫ b) ≫ q' = p' ≫ t' := by
  calc
    (inv a ≫ F.map s ≫ b) ≫ q' = inv a ≫ F.map s ≫ (b ≫ q') := by
      simp only [Category.assoc]
    _ = inv a ≫ F.map s ≫ (F.map q ≫ l) := by rw [hq]
    _ = inv a ≫ F.map (s ≫ q) ≫ l := by
      simp only [Functor.map_comp, Category.assoc]
    _ = inv a ≫ F.map (p ≫ t) ≫ l := by rw [hs]
    _ = inv a ≫ F.map p ≫ (F.map t ≫ l) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = inv a ≫ F.map p ≫ (k ≫ t') := by rw [ht]
    _ = inv a ≫ (F.map p ≫ k) ≫ t' := by simp only [Category.assoc]
    _ = inv a ≫ (a ≫ p') ≫ t' := by rw [hp]
    _ = p' ≫ t' := by simp only [Category.assoc, IsIso.inv_hom_id_assoc]

private theorem conjugate_precompose
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {A B K L : C} {A' B' K' L' : D}
    (a : F.obj A ⟶ A') [IsIso a] (b : F.obj B ⟶ B')
    (k : F.obj K ⟶ K') [IsIso k] (l : F.obj L ⟶ L')
    (p : K ⟶ A) (q : L ⟶ B) (p' : K' ⟶ A') (q' : L' ⟶ B')
    (s : A ⟶ B) (t : K ⟶ L) (t' : K' ⟶ L')
    (hp : F.map p ≫ a = k ≫ p') (hq : F.map q ≫ b = l ≫ q')
    (ht : F.map t ≫ l = k ≫ t') (hs : p ≫ s = t ≫ q) :
    p' ≫ (inv a ≫ F.map s ≫ b) = t' ≫ q' := by
  have hpi : p' ≫ inv a = inv k ≫ F.map p := by
    apply (cancel_mono a).1
    rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Category.assoc,
      hp, IsIso.inv_hom_id_assoc]
  calc
    p' ≫ (inv a ≫ F.map s ≫ b) = (p' ≫ inv a) ≫ F.map s ≫ b := by
      simp only [Category.assoc]
    _ = inv k ≫ F.map p ≫ F.map s ≫ b := by
      simp only [hpi, Category.assoc]
    _ = inv k ≫ F.map (p ≫ s) ≫ b := by
      simp only [Functor.map_comp, Category.assoc]
    _ = inv k ≫ F.map (t ≫ q) ≫ b := by rw [hs]
    _ = inv k ≫ F.map t ≫ (F.map q ≫ b) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = inv k ≫ F.map t ≫ (l ≫ q') := by rw [hq]
    _ = (inv k ≫ (F.map t ≫ l)) ≫ q' := by simp only [Category.assoc]
    _ = (inv k ≫ (k ≫ t')) ≫ q' := by rw [ht]
    _ = t' ≫ q' := by simp only [IsIso.inv_hom_id_assoc]

private theorem conjugate_isMonHom
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {A B : C} [MonObj A] [MonObj B] {A' B' : D} [MonObj A'] [MonObj B']
    (a : F.obj A ⟶ A') [IsIso a] [IsMonHom a]
    (b : F.obj B ⟶ B') [IsMonHom b] (s : A ⟶ B) [IsMonHom s] :
    IsMonHom (inv a ≫ F.map s ≫ b) := by
  change IsMonHom ((asIso a).inv ≫ F.map s ≫ b)
  infer_instance

private theorem tensorProjection_natural
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal]
    {A B R S T : C} {A' B' R' S' T' : D}
    (m : A ⟶ B) (m' : A' ⟶ B') (r : R ⟶ S) (r' : R' ⟶ S')
    (p : A ⟶ R ⊗ T) (q : B ⟶ S ⊗ T)
    (p' : A' ⟶ R' ⊗ T') (q' : B' ⟶ S' ⊗ T')
    (c : F.obj A ⟶ A') (d : F.obj B ⟶ B')
    (a : F.obj R ⟶ R') (b : F.obj S ⟶ S') (t : F.obj T ⟶ T')
    (hp : c ≫ p' = F.map p ≫ Functor.OplaxMonoidal.δ F R T ≫ (a ⊗ₘ t))
    (hq : d ≫ q' = F.map q ≫ Functor.OplaxMonoidal.δ F S T ≫ (b ⊗ₘ t))
    (hY : m ≫ q = p ≫ (r ⊗ₘ 𝟙 T)) (hX : m' ≫ q' = p' ≫ (r' ⊗ₘ 𝟙 T'))
    (hr : F.map r ≫ b = a ≫ r') :
    (F.map m ≫ d) ≫ q' = (c ≫ m') ≫ q' := by
  calc
    (F.map m ≫ d) ≫ q' =
        F.map m ≫ F.map q ≫ Functor.OplaxMonoidal.δ F S T ≫ (b ⊗ₘ t) := by
      simpa only [Category.assoc] using congrArg (fun z ↦ F.map m ≫ z) hq
    _ = F.map (m ≫ q) ≫ Functor.OplaxMonoidal.δ F S T ≫ (b ⊗ₘ t) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map (p ≫ (r ⊗ₘ 𝟙 T)) ≫ Functor.OplaxMonoidal.δ F S T ≫ (b ⊗ₘ t) := by
      rw [hY]
    _ = F.map p ≫ Functor.OplaxMonoidal.δ F R T ≫ ((F.map r ≫ b) ⊗ₘ t) := by
      simp only [Functor.map_comp, Category.assoc]
      rw [← Functor.OplaxMonoidal.δ_natural_assoc F]
      simp only [tensorHom_comp_tensorHom]
      rw [F.map_id T, Category.id_comp]
    _ = F.map p ≫ Functor.OplaxMonoidal.δ F R T ≫ ((a ≫ r') ⊗ₘ t) := by rw [hr]
    _ = (F.map p ≫ Functor.OplaxMonoidal.δ F R T ≫ (a ⊗ₘ t)) ≫
        (r' ⊗ₘ 𝟙 T') := by
      simp only [tensorHom_comp_tensorHom, Category.assoc, Category.comp_id]
    _ = (c ≫ p') ≫ (r' ⊗ₘ 𝟙 T') := by rw [hp]
    _ = (c ≫ m') ≫ q' := by
      simp only [Category.assoc]
      rw [hX]

private theorem tensorQuotient_natural
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.OplaxMonoidal]
    {I J R S Q P : C} {I' J' R' S' Q' P' : D}
    (i : I ⟶ J) (i' : I' ⟶ J') (r : R ⟶ S) (r' : R' ⟶ S')
    (q : Q ⟶ P) (q' : Q' ⟶ P')
    (p : R ⊗ I ⟶ Q) (s : S ⊗ J ⟶ P)
    (p' : R' ⊗ I' ⟶ Q') (s' : S' ⊗ J' ⟶ P')
    (c : F.obj I ⟶ I') (d : F.obj J ⟶ J')
    (a : F.obj R ⟶ R') (b : F.obj S ⟶ S')
    (ρ : F.obj Q ⟶ Q') (σ : F.obj P ⟶ P') [Epi (F.map p)]
    (hp : F.map p ≫ ρ = Functor.OplaxMonoidal.δ F R I ≫ (a ⊗ₘ c) ≫ p')
    (hs : F.map s ≫ σ = Functor.OplaxMonoidal.δ F S J ≫ (b ⊗ₘ d) ≫ s')
    (hY : p ≫ q = (r ⊗ₘ i) ≫ s) (hX : p' ≫ q' = (r' ⊗ₘ i') ≫ s')
    (hr : F.map r ≫ b = a ≫ r') (hi : F.map i ≫ d = c ≫ i') :
    F.map q ≫ σ = ρ ≫ q' := by
  apply (cancel_epi (F.map p)).1
  calc
    F.map p ≫ (F.map q ≫ σ) = F.map (p ≫ q) ≫ σ := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map ((r ⊗ₘ i) ≫ s) ≫ σ := by rw [hY]
    _ = F.map (r ⊗ₘ i) ≫ (F.map s ≫ σ) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = F.map (r ⊗ₘ i) ≫ Functor.OplaxMonoidal.δ F S J ≫ (b ⊗ₘ d) ≫ s' := by
      rw [hs]
    _ = Functor.OplaxMonoidal.δ F R I ≫
        ((F.map r ≫ b) ⊗ₘ (F.map i ≫ d)) ≫ s' := by
      rw [← Functor.OplaxMonoidal.δ_natural_assoc F]
      simp only [tensorHom_comp_tensorHom_assoc]
    _ = Functor.OplaxMonoidal.δ F R I ≫ ((a ≫ r') ⊗ₘ (c ≫ i')) ≫ s' := by
      rw [hr, hi]
    _ = Functor.OplaxMonoidal.δ F R I ≫ (a ⊗ₘ c) ≫ (r' ⊗ₘ i') ≫ s' := by
      simp only [tensorHom_comp_tensorHom_assoc]
    _ = Functor.OplaxMonoidal.δ F R I ≫ (a ⊗ₘ c) ≫ (p' ≫ q') := by rw [hX]
    _ = (F.map p ≫ ρ) ≫ q' := by
      simpa only [Category.assoc] using congrArg (fun z ↦ z ≫ q') hp.symm
    _ = F.map p ≫ (ρ ≫ q') := by simp only [Category.assoc]

private theorem uniqueMonExtension_natural
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {A B K L : C} [MonObj A] [MonObj B]
    {A' B' K' L' : D} [MonObj A'] [MonObj B']
    (a : F.obj A ⟶ A') [IsIso a] [IsMonHom a]
    (b : F.obj B ⟶ B') [IsMonHom b]
    (k : F.obj K ⟶ K') (l : F.obj L ⟶ L')
    (p : A ⟶ K) (q : B ⟶ L) (p' : A' ⟶ K') (q' : B' ⟶ L')
    (s : A ⟶ B) [IsMonHom s] (s' : A' ⟶ B')
    (t : K ⟶ L) (t' : K' ⟶ L')
    (hp : F.map p ≫ k = a ≫ p') (hq : F.map q ≫ l = b ≫ q')
    (ht : F.map t ≫ l = k ≫ t') (hs : s ≫ q = p ≫ t)
    (hu : ∀ z : A' ⟶ B', IsMonHom z → z ≫ q' = p' ≫ t' → z = s') :
    F.map s ≫ b = a ≫ s' := by
  have hz : inv a ≫ F.map s ≫ b = s' :=
    hu _ (conjugate_isMonHom F a b s)
      (conjugate_postcompose F a b k l p q p' q' s t t' hp hq ht hs)
  apply (cancel_epi (inv a)).1
  simpa only [Category.assoc, IsIso.inv_hom_id_assoc] using hz

section ModuleComparisons

universe w₁ vM₁ w₂ vM₂
variable {C : Type w₁} [Category.{vM₁} C] [MonoidalCategory C]
  {D : Type w₂} [Category.{vM₂} D] [MonoidalCategory D]
  (F : C ⥤ D) [F.Monoidal] (R : C) [MonObj R]
private def mapFreeIso (A : C) :
    ((F.mapMod R).obj ((Mod.free R).obj A)) ≅
      (Mod.free (F.obj R)).obj (F.obj A) := by
  refine Mod.isoMk (Functor.Monoidal.μIso F R A).symm ?_
  rw [Iso.symm_hom, Functor.Monoidal.μIso_inv]
  dsimp +instances only [Mod.act, Functor.mapMod, Mod.free, Functor.modObjObj, Mod.freeModObj,
    ModObj.mk']
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.OplaxMonoidal.δ_natural_left]
  rw [Functor.Monoidal.map_associator_inv]
  simp only [Category.assoc, Functor.Monoidal.μ_δ_assoc]
  rw [Functor.obj.μ_def, comp_whiskerRight]

private def freeMap {R S : C} [MonObj R] [MonObj S] (ρ : R ⟶ S) [IsMonHom ρ]
    {A B : C} (a : A ⟶ B) :
    (Mod.free R).obj A ⟶ (Mod.comap ρ).obj ((Mod.free S).obj B) := by
  refine Mod.homMk (ρ ⊗ₘ a) ?_
  change ((α_ R R A).inv ≫ μ[R] ▷ A) ≫ (ρ ⊗ₘ a) =
    R ◁ (ρ ⊗ₘ a) ≫ ρ ▷ (S ⊗ B) ≫ (α_ S S B).inv ≫ μ[S] ▷ B
  have hs : R ◁ (ρ ⊗ₘ a) ≫ ρ ▷ (S ⊗ B) = ρ ⊗ₘ (ρ ⊗ₘ a) := by
    rw [← id_tensorHom, ← tensorHom_id, tensorHom_comp_tensorHom]
    simp only [Category.id_comp, Category.comp_id]
  rw [← Category.assoc (R ◁ (ρ ⊗ₘ a)), hs]
  rw [associator_inv_naturality_assoc]
  simp only [Category.assoc]
  apply congrArg ((α_ R R A).inv ≫ ·)
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.id_comp, IsMonHom.mul_hom]
  rw [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id]

private def restrictedFreeMap {R B : C} [MonObj R] [MonObj B]
    {R' B' : D} [MonObj R'] [MonObj B']
    (r : R ⟶ B) [IsMonHom r] (s : R' ⟶ B') [IsMonHom s]
    (a : F.obj R ⟶ R') [IsMonHom a] (b : F.obj B ⟶ B') [IsMonHom b]
    (hsq : F.map r ≫ b = a ≫ s) {M : C} {N : D} (t : F.obj M ⟶ N) :
    (F.mapMod R).obj ((Mod.comap r).obj ((Mod.free B).obj M)) ⟶
      (Mod.comap a).obj ((Mod.comap s).obj ((Mod.free B').obj N)) :=
  (F.mapModComapIso r).hom.app ((Mod.free B).obj M) ≫
    (Mod.comap (F.map r)).map ((mapFreeIso F B M).hom) ≫
    (Mod.comap (F.map r)).map (freeMap b t) ≫
    (Mod.comapComp (F.map r) b).inv.app ((Mod.free B').obj N) ≫
    (Mod.comapCongr hsq).hom.app ((Mod.free B').obj N) ≫
    (Mod.comapComp a s).hom.app ((Mod.free B').obj N)

private theorem restrictedFreeMap_hom {R B : C} [MonObj R] [MonObj B]
    {R' B' : D} [MonObj R'] [MonObj B']
    (r : R ⟶ B) [IsMonHom r] (s : R' ⟶ B') [IsMonHom s]
    (a : F.obj R ⟶ R') [IsMonHom a] (b : F.obj B ⟶ B') [IsMonHom b]
    (hsq : F.map r ≫ b = a ≫ s) {M : C} {N : D} (t : F.obj M ⟶ N) :
    (restrictedFreeMap F r s a b hsq t).hom =
      Functor.OplaxMonoidal.δ F B M ≫ (b ⊗ₘ t) := by
  change 𝟙 _ ≫ Functor.OplaxMonoidal.δ F B M ≫ (b ⊗ₘ t) ≫
    𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

open CategoryTheory.Limits
private noncomputable def linearIntoLimit {R S : D} [MonObj R] [MonObj S]
    {J : Type*} [Category J] (K : J ⥤ Mod D S) [HasLimit K] [PreservesLimit K (Mod.forget S)]
    (M : Mod D R) (a : R ⟶ S) [IsMonHom a]
    (g : M.X ⟶ (limit K).X)
    (c : ∀ j, M ⟶ (Mod.comap a).obj (K.obj j))
    (hc : ∀ j, g ≫ (limit.π K j).hom = (c j).hom) :
    M ⟶ (Mod.comap a).obj (limit K) := by
  refine Mod.homMk g ?_
  apply (isLimitOfPreserves (Mod.forget S) (limit.isLimit K)).hom_ext
  intro j
  change (Mod.act M.X ≫ g) ≫ (limit.π K j).hom =
    (R ◁ g ≫ a ▷ (limit K).X ≫ Mod.act (limit K).X) ≫ (limit.π K j).hom
  rw [Category.assoc, hc, Mod.act_hom]
  change R ◁ (c j).hom ≫ a ▷ (K.obj j).X ≫ Mod.act (K.obj j).X = _
  rw [← hc, whiskerLeft_comp, Category.assoc]
  erw [whisker_exchange_assoc, ← Mod.act_hom]
  simp only [Category.assoc]

private noncomputable def inverseSemilinear
    {R S : D} [MonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (M : Mod D R) (N : Mod D S) (c : M ⟶ (Mod.comap a).obj N) :
    (Mod.comap (asIso a).inv).obj M ⟶ N := by
  refine Mod.homMk c.hom ?_
  change ((asIso a).inv ▷ M.X ≫ Mod.act M.X) ≫ c.hom =
    S ◁ c.hom ≫ Mod.act N.X
  rw [Category.assoc, Mod.act_hom]
  change (asIso a).inv ▷ M.X ≫ R ◁ c.hom ≫ a ▷ N.X ≫ Mod.act N.X = _
  rw [← whisker_exchange_assoc]
  change S ◁ c.hom ≫ (asIso a).inv ▷ N.X ≫ a ▷ N.X ≫ Mod.act N.X = _
  rw [← comp_whiskerRight_assoc, asIso_inv, IsIso.inv_hom_id,
    id_whiskerRight, Category.id_comp]

private theorem inverseSemilinear_hom
    {R S : D} [MonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (M : Mod D R) (N : Mod D S) (c : M ⟶ (Mod.comap a).obj N) :
    (inverseSemilinear a M N c).hom = c.hom := rfl

private theorem moduleIso_cancel {R : D} [MonObj R]
    {M N P : Mod D R} (e : M ≅ N) (g : N ⟶ P) :
    e.inv.hom ≫ (e.hom ≫ g).hom = g.hom := by
  change (Mod.forget R).map e.inv ≫ (Mod.forget R).map (e.hom ≫ g) =
    (Mod.forget R).map g
  rw [← Functor.map_comp, Iso.inv_hom_id_assoc]

attribute [local irreducible] inverseSemilinear

end ModuleComparisons

attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory

-- Keep the scalar-extension object abstract; its coequalizer equations are the API.
attribute [local irreducible] Mod.extendScalarsObj Mod.extendScalarsIsoComapInv
  AlgebraicGeometry.ProEtale.CondensedRing.pullIso

namespace AlgebraicGeometry.ProEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

-- Fixed-universe presentations cache the categorical instance arguments.
private abbrev AbSheaf (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}
private abbrev ModSheaf (T : Scheme.{u}) (R : AbSheaf T) [MonObj R] :=
  Mod (AbSheaf T) R
private abbrev PointAb := Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}

-- Cache these propositional instances: reconstructing the internal-module limit
-- through its condensed coefficient presentation is expensive at each projection.
-- Cache the sheafification proofs used throughout the section.
private instance proEtSmall (T : Scheme.{u}) : EssentiallySmall.{u + 1} T.ProEt :=
  essentiallySmallSelf.{0, u, u + 1} _
private instance abelianSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} := inferInstance
private instance abelianWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} := inferInstance
private instance ringSheafify (T : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology T) RingCat.{u + 1} := inferInstance
private instance ringWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) RingCat.{u + 1} := inferInstance
private instance commRingWeakSheafify (T : Scheme.{u}) :
    HasWeakSheafify (Scheme.ProEt.topology T) CommRingCat.{u + 1} := inferInstance
private instance abelianForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget AddCommGrpCat.{u + 1}) := inferInstance
private instance ringForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget RingCat.{u + 1}) := inferInstance
private instance commRingForgetSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget CommRingCat.{u + 1}) := inferInstance
private instance commRingToRingSheafification (T : Scheme.{u}) :
    (Scheme.ProEt.topology T).PreservesSheafification
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1}) := inferInstance

private instance integralSystem_hasLimit (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) : HasLimit (spIntegralTwistSystem T ℓ E) :=
  inferInstance

private instance integralSystem_forget_preservesLimit
    (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    PreservesLimit (spIntegralTwistSystem T ℓ E)
      (Mod.forget (C := AbSheaf T)
        (D := AbSheaf T)
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) T)) :=
  inferInstance

private instance rationalDiagram_hasColimit (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime] :
    HasColimit (spRationalTwistDiagram T ℓ) := inferInstance

private instance rationalDiagram_pull_preservesColimit (ℓ : ℕ) [Fact ℓ.Prime] :
    PreservesColimit (spRationalTwistDiagram Y ℓ) (upperStar Ab.{u + 1} f) := inferInstance

private theorem globalPrimeUnit (S : Scheme.{u}) (l : ℕ)
    [∀ x : S, Invertible (l : S.residueField x)] : IsUnit (l : Γ(S, ⊤)) := by
  apply S.toRingedSpace.isUnit_of_isUnit_germ
  intro x hx
  rw [map_natCast]
  apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
  change (S.residue x).hom (l : S.presheaf.stalk x) ≠ 0
  simpa only [map_natCast] using (isUnit_of_invertible (l : S.residueField x)).ne_zero

/-- Roots of unity commute with inverse image along every scheme morphism where ell
is invertible, including exponent zero. Source: blueprint Roots of unity paragraph
(blueprint: lemma-inverse-image-coefficient-sheaves--2).
Proof: invertibility in every residue field makes ell a unit of global sections,
and hence ell^n is a unit as well. Apply the root square of finiteRootSiteComparison
with the finite auxiliary ring ULift (ZMod (ell^n)). The etale root comparison,
the comparison of the etale and pro-etale inverse images, and the etale-to-pro-etale
root identifications are isomorphisms. Thus so is their composite, and cancellation
of the pulled-back root identification gives the prescribed pro-etale root map.
This argument also applies to n=0, where the auxiliary ring is the zero ring. -/
theorem spRoots_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (n : ℕ) :
    IsIso (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n)) := by
  let N := ℓ ^ n
  have hN : 0 < N := pow_pos (Fact.out : ℓ.Prime).pos _
  let : NeZero N := ⟨Nat.ne_of_gt hN⟩
  let A := ULift.{u + 1} (ZMod N)
  have hA : (N : A) = 0 := by
    apply ULift.ext
    exact ZMod.natCast_self N
  have hX : IsUnit (N : Γ(X, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (globalPrimeUnit X ℓ).pow n
  have hY : IsUnit (N : Γ(Y, ⊤)) := by
    simpa only [N, Nat.cast_pow] using (globalPrimeUnit Y ℓ).pow n
  have h := (Scheme.finiteRootSiteComparison A).choose_spec.choose_spec.2.2.2.2.2.2.1
    N hN hA f hY hX
  have : IsIso ((Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
      (cartierRootsIso Y N hN hY).hom ≫
        Scheme.proEtaleRootsOfUnityInverseImageMap f N) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
      (cartierRootsIso Y N hN hY).hom) _

private instance pullback_forget_kan
    {D : Type (u + 2)} [Category.{u + 1} D]
    [HasColimitsOfSize.{u + 1, u + 1} D]
    (G : D ⥤ Type (u + 1)) [PreservesFilteredColimitsOfSize.{u + 1, u + 1} G]
    (P : Y.ProEtᵒᵖ ⥤ D) :
    G.PreservesPointwiseLeftKanExtension P (Scheme.proEtaleBaseChange f).op := by
  let U := Scheme.proEtaleBaseChange f
  have : RepresentablyFlat U := flat_of_preservesFiniteLimits _
  intro W
  have : IsFiltered (CostructuredArrow U.op W) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence U W.unop)
  have : PreservesColimit (CostructuredArrow.proj U.op W ⋙ P) G := by
    have hG : PreservesFilteredColimitsOfSize.{u, u + 1} G :=
      preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u + 1} G
    have := hG.preserves_filtered_colimits (CostructuredArrow U.op W)
    infer_instance
  exact Functor.preservesPointwiseLeftKanExtensionAtOfPreservesColimit G P U.op W

private def abelianPullbackForgetIso :
    upperStar AddCommGrpCat.{u + 1} f ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1})

private theorem abelianPullbackForgetIso_unit
    (R : AbSheaf Y)
    (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) :
    ((abelianPullbackForgetIso f).hom.app R).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app R).hom.app V a) =
      ((setPullbackAdjunction f).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj R)).hom.app
          V a := by
  exact congrArg (fun q ↦ q.hom.app V a)
    (sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (forget AddCommGrpCat.{u + 1}) R)

private def ringPullbackForgetIso :
    Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget CommRingCat.{u + 1})

private theorem ringPullbackForgetIso_unit
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) :
    ((ringPullbackForgetIso f).hom.app R).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app V a) =
      ((setPullbackAdjunction f).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1})).obj R)).hom.app
          V a := by
  exact congrArg (fun q ↦ q.hom.app V a)
    (sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (forget CommRingCat.{u + 1}) R)

private def noncommPullbackForgetIso :
    Scheme.proEtaleSheafInverseImage f RingCat.{u + 1} ⋙
        sheafCompose (Scheme.ProEt.topology X) (forget RingCat.{u + 1}) ≅
      sheafCompose (Scheme.ProEt.topology Y) (forget RingCat.{u + 1}) ⋙
        setPullback f := by
  exact sheafPullbackForgetIso (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
    (Scheme.proEtaleBaseChange f) (forget RingCat.{u + 1})

private theorem noncommPullbackForgetIso_unit
    (R : Sheaf (Scheme.ProEt.topology Y) RingCat.{u + 1})
    (V : Y.ProEtᵒᵖ) (a : R.obj.obj V) :
    ((noncommPullbackForgetIso f).hom.app R).hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R).hom.app V a) =
      ((setPullbackAdjunction f).unit.app
        ((sheafCompose (Scheme.ProEt.topology Y) (forget RingCat.{u + 1})).obj R)).hom.app
          V a := by
  exact congrArg (fun q ↦ q.hom.app V a)
    (sheafPullbackForgetIso_unit (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)
      (Scheme.proEtaleBaseChange f) (forget RingCat.{u + 1}) R)

attribute [local irreducible] abelianPullbackForgetIso ringPullbackForgetIso
  noncommPullbackForgetIso
  condensedPushforwardHom

private theorem sectionRingPullbackIso_existsUnique
    (RY : AbSheaf Y)
    (RX : AbSheaf X)
    [MonObj RY] [IsCommMonObj RY] [MonObj RX] [IsCommMonObj RX]
    (α : (upperStar AddCommGrpCat.{u + 1} f).obj RY ⟶ RX) [IsIso α]
    (eta : RY ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj RX)
    (heta : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
      (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) α).hom.app
        V a = eta.hom.app V a)
    (β : InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
        (Scheme.ProEt.topology Y) RY ⟶
      (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX))
    (hβ : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V), β.hom.app V a = eta.hom.app V a) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) RY) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX,
      ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = eta.hom.app V a := by
  let R := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology Y) RY
  let S := InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) RX
  let c := ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).symm β
  have hc : ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) c).hom.app V a =
        eta.hom.app V a := by
    intro V a
    change (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S)
      (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).symm β)).hom.app
        V a = _
    rw [Equiv.apply_symm_apply]
    exact hβ V a
  clear_value c
  have hi : IsIso c := by
    let U := sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})
    let UR := sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})
    let e := ((ringPullbackForgetIso f).app R).symm
    let d := (abelianPullbackForgetIso f).app RY
    have heunit (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V) :
        e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app
              V a) = (((setPullbackAdjunction f).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget CommRingCat.{u + 1})).obj R)).hom.app
            V a) := by
      exact ringPullbackForgetIso_unit f R V a
    have hdunit (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V) :
        d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
              RY).hom.app V a) = (((setPullbackAdjunction f).unit.app
          ((sheafCompose (Scheme.ProEt.topology Y) (forget AddCommGrpCat.{u + 1})).obj RY)).hom.app
            V a) := by
      exact abelianPullbackForgetIso_unit f RY V a
    clear_value e d
    have he : e.hom ≫ UR.map c =
        d.inv ≫ U.map α := by
      apply ((setPullbackAdjunction f).homEquiv _ _).injective
      ext V a
      change (UR.map c).hom.app _
          (e.hom.hom.app _ (((setPullbackAdjunction f).unit.app _).hom.app V a)) = _
      have hr₀ := heunit V a
      have hr := congrArg (fun z ↦ e.hom.hom.app
        ((Scheme.proEtaleBaseChange f).op.obj V) z) hr₀
      have hidr : ∀ x, e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x := by
        intro x
        exact congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
          e.inv_hom_id
      change e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app
            V a)) = _ at hr
      rw [hidr] at hr
      have hr := hr.symm
      erw [hr]
      change (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _) c).hom.app
        V a = _
      rw [hc V a]
      have hd := hdunit V a
      have hd' := congrArg (fun z ↦ d.inv.hom.app _ z) hd
      have hid : ∀ x, d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x := by
        intro x
        exact congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
          d.hom_inv_id
      change d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).unit.app
            RY).hom.app V a)) = _ at hd'
      rw [hid] at hd'
      rw [Adjunction.homEquiv_unit]
      change eta.hom.app V a =
        α.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
          (d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
            (((setPullbackAdjunction f).unit.app _).hom.app V a))
      rw [← hd']
      exact (heta V a).symm
    have : IsIso (e.hom ≫ UR.map c) := by
      rw [he]
      infer_instance
    have : IsIso (UR.map c) := IsIso.of_isIso_comp_left e.hom _
    exact isIso_of_reflects_iso c
      (sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1}))
  have := hi
  refine ⟨asIso c, hc, ?_⟩
  intro c' hc'
  apply Iso.ext
  apply ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv R S).injective
  ext V a
  exact (hc' V a).trans (hc V a).symm

private theorem abelianAdjunct_eq
    (R : AbSheaf Y)
    (S : AbSheaf X)
    (g : (upperStar AddCommGrpCat.{u + 1} f).obj R ⟶ S) :
    ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) g =
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app R ≫
        (lowerStar AddCommGrpCat.{u + 1} f).map g := by
  rw [Adjunction.homEquiv_unit]
  rfl

private def liftRingSheafMap
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (φ : (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
      (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) :
    R ⟶ (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).obj S :=
  ⟨{ app := fun V ↦
       (show R.obj.obj V ⟶ S.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V) from
         ConcreteCategory.ofHom (C := CommRingCat) (φ.hom.app V).hom)
     naturality := by
       intro V W g
       ext x
       exact ConcreteCategory.congr_hom (φ.hom.naturality g) x }⟩

private theorem sectionRingPullbackIso_ofMonHom
    (RY : AbSheaf Y)
    (RX : AbSheaf X)
    [MonObj RY] [IsCommMonObj RY] [MonObj RX] [IsCommMonObj RX]
    (α : (upperStar AddCommGrpCat.{u + 1} f).obj RY ⟶ RX) [IsIso α]
    (eta : RY ⟶ (lowerStar AddCommGrpCat.{u + 1} f).obj RX) [IsMonHom eta]
    (heta : ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) α = eta) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) RY) ≅
        InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) RX,
      ∀ (V : Y.ProEtᵒᵖ) (a : RY.obj.obj V),
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
          c.hom).hom.app V a = eta.hom.app V a := by
  obtain ⟨φ, hφ, _⟩ := InternalModuleOperations.sectionRingMap_existsUnique
    (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) (Scheme.proEtaleBaseChange f)
    RX RY eta
  exact sectionRingPullbackIso_existsUnique f RY RX α eta
    (fun V a ↦ congrArg (fun q ↦ q.hom.app V a) heta) (liftRingSheafMap f _ _ φ) hφ

/-- Alpha, in commutative ring sheaves, selected by its unique adjunct normalization.
Source: blueprint coefficient compatibility
(blueprint: lemma-inverse-image-coefficient-sheaves--2). -/
def spCoefficientIso
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] :=
  Classical.choose (spCoefficientIso_existsUnique f Λ)

private theorem coefficientIso_adjunct
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (V : Y.ProEtᵒᵖ) (a : (condensedRingObj Λ Y).obj.obj V) :
    (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
      (spCoefficientIso f Λ).hom).hom.app V a =
        (condensedPushforwardHom Λ f).hom.app V a := by
  unfold spCoefficientIso
  exact (Classical.choose_spec (spCoefficientIso_existsUnique f Λ)).1 V a

attribute [local irreducible] spCoefficientIso

private def integralLevelComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).obj (spIntegralTwistLevel Y ℓ E n).X ⟶
      (spIntegralTwistLevel X ℓ E n).X :=
  Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
    (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f ⊗ₘ
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1)))

private def integralComparisonSystem (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    spIntegralTwistSystem Y ℓ E ⋙ Mod.forget _ ⋙ upperStar AddCommGrpCat.{u + 1} f ⟶
      spIntegralTwistSystem X ℓ E ⋙ Mod.forget _ :=
    NatTrans.ofOpSequence (integralLevelComparison f ℓ E) (by
      intro n
      simp only [Functor.comp_map, spIntegralTwistSystem,
        Functor.ofOpSequence_map_homOfLE_succ]
      change (upperStar AddCommGrpCat.{u + 1} f).map (spIntegralLevelTransition Y ℓ E n).hom ≫ _ =
        _ ≫ (spIntegralLevelTransition X ℓ E n).hom
      have hY := (spIntegralLevelTransition_existsUnique Y ℓ E n).exists.choose_spec
      have hX := (spIntegralLevelTransition_existsUnique X ℓ E n).exists.choose_spec
      change (spIntegralLevelTransition Y ℓ E n).hom = _ at hY
      change (spIntegralLevelTransition X ℓ E n).hom = _ at hX
      rw [hY, hX]
      unfold integralLevelComparison
      rw [← Functor.OplaxMonoidal.δ_natural_assoc (upperStar AddCommGrpCat.{u + 1} f)]
      simp only [Category.assoc]
      apply congrArg (fun k ↦ Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫ k)
      simp only [MonoidalCategory.tensorHom_comp_tensorHom]
      apply congrArg₂ (fun a b ↦ a ⊗ₘ b)
      · exact map_coefficientMap_comp_condensedPullbackHom _ _
      · exact (Scheme.proEtaleRootsOfUnityInverseImageIso f).1 _ _ _ _ _)

private theorem integralComparisonSystem_app (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    (integralComparisonSystem f ℓ E).app (op n) = integralLevelComparison f ℓ E n := rfl

attribute [local irreducible] integralComparisonSystem

/-- The integral comparison is uniquely determined by every finite root projection.
Source: blueprint Integral twist paragraph
(blueprint: lemma-inverse-image-coefficient-sheaves--2).
Proof: tensor the canonical coefficient comparison with the canonical root map,
using the strong monoidal inverse image. These maps commute with reductions and
Kummer transitions. They give a cone on the finite-level system. The forgetful
functor creates its limit, hence the cone has exactly one induced abelian map.
This characterization does not assert preservation of arbitrary inverse limits. -/
theorem spIntegralComparison_existsUnique (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃! c : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
        (spIntegralTwist.{u} Y ℓ E).X ⟶ (spIntegralTwist.{u} X ℓ E).X,
      ∀ n : ℕ,
        c ≫ (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom =
          (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
            (limit.π (spIntegralTwistSystem Y ℓ E) (op n)).hom ≫
          (Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
            (condensedRingObj (spEllPointRingObj.{u} ℓ E n) Y)
            (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (n + 1)))) ≫
          (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f ⊗ₘ
            Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1))) := by
  let F := upperStar AddCommGrpCat.{u + 1} f
  let UY := Mod.forget (C := AbSheaf Y)
    (D := AbSheaf Y)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)
  let UX := Mod.forget (C := AbSheaf X)
    (D := AbSheaf X)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
  obtain ⟨c, hc, hu⟩ :=
    comparisonIntoPreservedLimit UY UX F (spIntegralTwistSystem Y ℓ E)
      (spIntegralTwistSystem X ℓ E) (integralComparisonSystem f ℓ E)
  refine ⟨c, ?_, ?_⟩
  · intro n
    change c ≫ UX.map (limit.π (spIntegralTwistSystem X ℓ E) (op n)) =
      F.map (UY.map (limit.π (spIntegralTwistSystem Y ℓ E) (op n))) ≫
        integralLevelComparison f ℓ E n
    rw [← integralComparisonSystem_app]
    exact hc (op n)
  · intro c' hc'
    apply hu c'
    rintro ⟨n⟩
    rw [integralComparisonSystem_app]
    exact hc' n

/-- The integral comparison, with all finite-level projections specified.
Source: blueprint Integral twist paragraph
(blueprint: lemma-inverse-image-coefficient-sheaves--2). -/
def spIntegralComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
      (spIntegralTwist.{u} Y ℓ E).X ⟶ (spIntegralTwist.{u} X ℓ E).X :=
  Classical.choose (spIntegralComparison_existsUnique f ℓ E)

private theorem ordinaryLift_exists
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (c : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj L ⟶
      (Mod.comap (condensedPullbackHom Λ f)).obj M) :
    ∃ g : (CondensedRing.upperStar Λ f).obj L ⟶ M,
      (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom = c.hom := by
  refine ⟨(Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app _ ≫
    inverseSemilinear (condensedPullbackHom Λ f) _ _ c, ?_⟩
  dsimp only [profinitePointModuleForgetPullbackIso]
  change ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app _).hom ≫
    (((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).hom.app _) ≫
      inverseSemilinear (condensedPullbackHom Λ f) _ _ c).hom = c.hom
  exact (moduleIso_cancel
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).app _)
    (inverseSemilinear (condensedPullbackHom Λ f) _ _ c)).trans
      (inverseSemilinear_hom _ _ _ _)

private theorem ordinaryLift_iso
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (c : ((upperStar Ab.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj L ⟶
      (Mod.comap (condensedPullbackHom Λ f)).obj M) [IsIso c.hom] :
    ∃ g : (CondensedRing.upperStar Λ f).obj L ≅ M,
      (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom.hom = c.hom := by
  obtain ⟨g, hg⟩ := ordinaryLift_exists f Λ L M c
  have : IsIso ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom) := by
    rw [hg]
    infer_instance
  have : IsIso g.hom := IsIso.of_isIso_comp_left
    ((profinitePointModuleForgetPullbackIso Λ f).inv.app L) _
  have : IsIso ((Mod.forget (condensedRingObj Λ X)).map g) := ‹IsIso g.hom›
  have : IsIso g := isIso_of_reflects_iso g (Mod.forget (condensedRingObj Λ X))
  exact ⟨asIso g, hg⟩

private theorem integralModuleComparison_exists (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ c : ((upperStar AddCommGrpCat.{u + 1} f).mapMod
        (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)).obj
        (spIntegralTwist Y ℓ E) ⟶
      (Mod.comap (condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ E.1) f)).obj
        (spIntegralTwist X ℓ E), c.hom = spIntegralComparison f ℓ E := by
  let F := upperStar AddCommGrpCat.{u + 1} f
  let RY := condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y
  let a := condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ E.1) f
  have hlevel (n : ℕ) :
      ∃ c : (F.mapMod RY).obj (spIntegralTwistLevel Y ℓ E n) ⟶
          (Mod.comap a).obj (spIntegralTwistLevel X ℓ E n),
        c.hom = integralLevelComparison f ℓ E n := by
    refine ⟨restrictedFreeMap F
      (spEllReduction Y ℓ E n) (spEllReduction X ℓ E n) a
      (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f)
      (map_coefficientMap_comp_condensedPullbackHom (spEllPointReduction ℓ E n) f)
      (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1))), ?_⟩
    exact restrictedFreeMap_hom F _ _ _ _ _ _
  choose c hc using hlevel
  have hp (j : ℕᵒᵖ) :
      spIntegralComparison f ℓ E ≫ (limit.π (spIntegralTwistSystem X ℓ E) j).hom =
        ((F.mapMod RY).map (limit.π (spIntegralTwistSystem Y ℓ E) j) ≫ c j.unop).hom := by
    rcases j with ⟨n⟩
    change spIntegralComparison f ℓ E ≫ _ =
      F.map (limit.π (spIntegralTwistSystem Y ℓ E) (op n)).hom ≫ (c n).hom
    rw [hc]
    exact (Classical.choose_spec (spIntegralComparison_existsUnique f ℓ E)).1 n
  exact ⟨linearIntoLimit (spIntegralTwistSystem X ℓ E)
    ((F.mapMod RY).obj (spIntegralTwist Y ℓ E)) a (spIntegralComparison f ℓ E)
    (fun j ↦ (F.mapMod RY).map (limit.π (spIntegralTwistSystem Y ℓ E) j) ≫ c j.unop)
    hp, rfl⟩

private theorem ordinaryIntegralComparison_iso_exists (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) [IsIso (spIntegralComparison f ℓ E)] :
    ∃ g : (CondensedRing.upperStar (Profinite.padicIntegersRingObj.{u} ℓ E.1) f).obj
        (spIntegralTwist Y ℓ E) ≅ spIntegralTwist X ℓ E,
      (profinitePointModuleForgetPullbackIso (Profinite.padicIntegersRingObj.{u} ℓ E.1) f).inv.app
        (spIntegralTwist Y ℓ E) ≫ g.hom.hom = spIntegralComparison f ℓ E := by
  obtain ⟨c, hc⟩ := integralModuleComparison_exists f ℓ E
  have : IsIso c.hom := by rw [hc]; infer_instance
  obtain ⟨g, hg⟩ := ordinaryLift_iso f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
    (spIntegralTwist Y ℓ E) (spIntegralTwist X ℓ E) c
  exact ⟨g, hg.trans hc⟩

attribute [local irreducible] profinitePointModuleForgetPullbackIso

private theorem extendedComparison_normalized
    (Λ A : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ]
    (M : ModSheaf Y
      (condensedRingObj Λ Y))
    (N : ModSheaf X
      (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj M ⟶ N) :
    let c : (upperStar AddCommGrpCat.{u + 1} f).obj
        ((Mod.extendScalars (coefficientMap φ Y)).obj M).X ⟶
      ((Mod.extendScalars (coefficientMap φ X)).obj N).X :=
      (profinitePointModuleForgetPullbackIso A f).inv.app
        ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≫
      ((CondensedRing.pullIso φ f).inv.app M).hom ≫
      ((Mod.extendScalars (coefficientMap φ X)).map g).hom
    (upperStar AddCommGrpCat.{u + 1} f).map
      (Mod.extendπ (coefficientMap φ Y) M) ≫ c =
        Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
          (condensedRingObj A Y) M.X ≫
        (condensedPullbackHom A f ⊗ₘ
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ g.hom)) ≫
        Mod.extendπ (coefficientMap φ X) N := by
  dsimp only
  slice_lhs 1 3 => exact CondensedRing.pull_extend_π Λ A φ f M
  rw [Category.assoc, Category.assoc, Mod.extendScalars_map,
    Mod.extendπ_extendScalarsMap]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_def, whiskerLeft_comp]

private theorem extendedComparison_iso_exists
    (Λ A : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ]
    (M : ModSheaf Y (condensedRingObj Λ Y))
    (N : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj M ⟶ N) [IsIso g] :
    ∃ e : (CondensedRing.upperStar A f).obj
        ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≅
      (Mod.extendScalars (coefficientMap φ X)).obj N,
      (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap φ Y) M) ≫
        ((profinitePointModuleForgetPullbackIso A f).inv.app
          ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≫ e.hom.hom) =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj A Y) M.X ≫
        (condensedPullbackHom A f ⊗ₘ
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ g.hom)) ≫
        Mod.extendπ (coefficientMap φ X) N := by
  let c := (CondensedRing.pullIso φ f).inv.app M ≫
    (Mod.extendScalars (coefficientMap φ X)).map g
  have : IsIso c := inferInstance
  refine ⟨asIso c, ?_⟩
  have h := extendedComparison_normalized f Λ A φ M N g
  simpa only [asIso_hom, c, Mod.comp_hom', Category.assoc] using h

attribute [local irreducible] spIntegralComparison

/-- The derived twist functor is tensor with the recorded signed line in degree zero.
Its object function is spComplexTwistOfUniverses. Source: blueprint derived consequence
(blueprint: lemma-inverse-image-coefficient-sheaves--2). -/
def spTwistFunctor (Z : Scheme.{u})
    (R : Sheaf (Scheme.ProEt.topology Z) CommRingCat.{u + 1})
    (L : Scheme.proEtaleRingModules Z R) (d : ℤ) :=
  Scheme.tateTensorRight
    (SheafOfModules.siteDerivedTensorIndependentCoefficients.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Z) R)
    ((DerivedCategory.singleFunctor.{u + 2, u + 1, u + 2}
      (Scheme.proEtaleRingModules Z R) 0).obj
        (WeilConjectures.coefficientTwistLine Z (R := R) L d))

attribute [local irreducible] spTwistFunctor

section SignedComparisonStatement
attribute [local irreducible] Scheme.proEtaleRingModulePullback
  Scheme.proEtaleRingModuleAdjunction
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in

/-- The signed comparisons with their coefficient, tensor and evaluation normalizations.
Here the unit section is the canonical unit of the module pullback adjunction;
thus the formulas determine maps on all inverse-image generators, not just global
sections. Negative powers are normalized by evaluation of the pulled-back functional
on the pulled-back section. Source: blueprint Powers and duals paragraph
(blueprint: lemma-inverse-image-coefficient-sheaves--2). -/
structure SpSignedComparison
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (L : Scheme.proEtaleRingModules Y R) (M : Scheme.proEtaleRingModules X S) where
  signed : ∀ d : ℤ,
    (Scheme.proEtaleRingModulePullback f R S c).obj
        (WeilConjectures.coefficientTwistLine Y (R := R) L d) ≅
      WeilConjectures.coefficientTwistLine X (R := S) M d
  zero : ∀ (V : Y.ProEt) (a : R.obj.obj (op V)),
    (signed 0).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistLine Y (R := R) L 0)).val.app (op V) a) =
      (Scheme.proEtaleRingDirectImageMap f R S c).hom.app (op V) a
  positive : ∀ (n : ℕ) (V : Y.ProEt) (a : L.val.obj (op V))
    (b : (WeilConjectures.coefficientTwistPower Y L (n + 1)).val.obj (op V)),
    (signed (n + 2)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistPower Y L (n + 2))).val.app (op V)
          (SheafOfModules.siteSheafTensorTmul
            (WeilConjectures.coefficientTwistPower Y L (n + 1)) L (op V) b a)) =
      SheafOfModules.siteSheafTensorTmul
        (WeilConjectures.coefficientTwistPower X M (n + 1)) M
        (op ((Scheme.proEtaleBaseChange f).obj V))
        ((signed (n + 1)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
          (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
            (WeilConjectures.coefficientTwistPower Y L (n + 1))).val.app (op V) b))
        ((signed 1).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
          (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app L).val.app (op V) a))
  negative : ∀ (n : ℕ) (V : Y.ProEt)
    (φ : (WeilConjectures.coefficientTwistLine Y (R := R) L (Int.negSucc n)).val.obj (op V))
    (a : (WeilConjectures.coefficientTwistPower Y L (n + 1)).val.obj (op V)),
    (((signed (Int.negSucc n)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
        (WeilConjectures.coefficientTwistLine Y (R := R) L (Int.negSucc n))).val.app
          (op V) φ)).app (op (Over.mk (𝟙 ((Scheme.proEtaleBaseChange f).obj V)))))
      ((signed (n + 1)).hom.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app
          (WeilConjectures.coefficientTwistPower Y L (n + 1))).val.app (op V) a)) =
      (Scheme.proEtaleRingDirectImageMap f R S c).hom.app (op V)
        (φ.app (op (Over.mk (𝟙 V))) a)
  derived : ∀ d : ℤ,
    spTwistFunctor Y R L d ⋙ Scheme.proEtaleRingDerivedPullback f R S c ≅
      Scheme.proEtaleRingDerivedPullback f R S c ⋙ spTwistFunctor X S M d

end SignedComparisonStatement

section SignedPullbackProof

attribute [local irreducible] Scheme.proEtaleModuleInverseImage
  Scheme.proEtaleRingModuleAdjunction Scheme.proEtaleRingModulePullback
  SheafOfModules.siteSheafTensorRight

private def moduleStructuralMap
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R ⟶
    ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous RingCat.{u + 1}
      (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
        ((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S) :=
  (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (Scheme.proEtaleRingDirectImageMap f R S c)

private theorem moduleStructuralMap_apply
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (V : Y.ProEt) (r : R.obj.obj (op V)) :
    (moduleStructuralMap f R S c).hom.app (op V) r =
      (Scheme.proEtaleRingDirectImageMap f R S c).hom.app (op V) r := rfl

private theorem moduleStructuralMap_isIso
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    IsIso (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
      (moduleStructuralMap f R S c)) := by
  let R' := (sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S' := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let k := ((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv R' S').symm
    (moduleStructuralMap f R S c)
  change IsIso k
  have hkadj : ((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv R' S') k =
      moduleStructuralMap f R S c := Equiv.apply_symm_apply _ _
  clear_value k
  let UR := sheafCompose (Scheme.ProEt.topology X) (forget RingCat.{u + 1})
  let UC := sheafCompose (Scheme.ProEt.topology X) (forget CommRingCat.{u + 1})
  let e := (noncommPullbackForgetIso f).app R'
  let d := (ringPullbackForgetIso f).app R
  have hk : e.inv ≫ UR.map k = d.inv ≫ UC.map c.hom := by
    apply ((setPullbackAdjunction f).homEquiv _ _).injective
    ext V a
    have hηr := noncommPullbackForgetIso_unit f R' V a
    have hηc := ringPullbackForgetIso_unit f R V a
    have hηri := congrArg (fun z ↦ e.inv.hom.app
      ((Scheme.proEtaleBaseChange f).op.obj V) z) hηr
    have hηci := congrArg (fun z ↦ d.inv.hom.app
      ((Scheme.proEtaleBaseChange f).op.obj V) z) hηc
    have hei : ∀ x, e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x :=
      fun x ↦ congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
        e.hom_inv_id
    have hdi : ∀ x, d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x) = x :=
      fun x ↦ congrArg (fun q ↦ q.hom.app ((Scheme.proEtaleBaseChange f).op.obj V) x)
        d.hom_inv_id
    change e.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
      (e.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).unit.app R').hom.app V a)) =
        _ at hηri
    change d.inv.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
      (d.hom.hom.app ((Scheme.proEtaleBaseChange f).op.obj V)
        (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom.app V a)) =
        _ at hηci
    rw [hei] at hηri
    rw [hdi] at hηci
    change k.hom.app _ (e.inv.hom.app _
      (((setPullbackAdjunction f).unit.app _).hom.app V a)) =
      c.hom.hom.app _ (d.inv.hom.app _
        (((setPullbackAdjunction f).unit.app _).hom.app V a))
    rw [← hηri, ← hηci]
    change (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _) k).hom.app
      V a = (Scheme.proEtaleRingDirectImageMap f R S c).hom.app V a
    exact congrArg (fun q ↦ q.hom.app V a)
      hkadj
  have : IsIso (e.inv ≫ UR.map k) := by rw [hk]; infer_instance
  have : IsIso (UR.map k) := IsIso.of_isIso_comp_left e.inv _
  exact isIso_of_reflects_iso k UR

private def modulePullbackComparison
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    Scheme.proEtaleRingModulePullback f R S c ≅
      SheafOfModules.SignedLineDerivedBaseChange.pull.{u + 1, u, u + 1}
        (U := Scheme.proEtaleBaseChange f) (moduleStructuralMap f R S c) :=
  (Scheme.proEtaleRingModuleAdjunction f R S c).leftAdjointUniq
    (@SheafOfModules.pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _
      (moduleStructuralMap f R S c)
      (SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
        (U := Scheme.proEtaleBaseChange f) _))

private theorem modulePullbackComparison_unit
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : Scheme.proEtaleRingModules Y R) (V : Y.ProEt) (m : M.val.obj (op V)) :
    ((modulePullbackComparison f R S c).hom.app M).val.app
        (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M).val.app (op V) m) =
    SheafOfModules.ringedSitePullbackSection.{u + 1, u, u + 1}
      (U := Scheme.proEtaleBaseChange f) (moduleStructuralMap f R S c)
      (SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
        (U := Scheme.proEtaleBaseChange f) _) M V m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.proEtaleRingModuleAdjunction f R S c)
    (@SheafOfModules.pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _
      (moduleStructuralMap f R S c)
      (SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
        (U := Scheme.proEtaleBaseChange f) _)) M
  exact congrArg (fun k ↦ k.val.app (op V) m) h

attribute [local irreducible] moduleStructuralMap modulePullbackComparison

private theorem signedComparison_exists
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (L : Scheme.proEtaleRingModules Y R) (M : Scheme.proEtaleRingModules X S)
    (t : (Scheme.proEtaleRingModulePullback f R S c).obj L ≅ M)
    (hL : ∃ (I : Type (u + 1)) (V : I → Y.ProEt),
      (Scheme.ProEt.topology Y).CoversTop V ∧
      ∀ i, Nonempty (L.over (V i) ≅ SheafOfModules.unit
        (((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R).over (V i))))
    (hM : ∃ (I : Type (u + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (M.over (V i) ≅ SheafOfModules.unit
        (((sheafCompose (Scheme.ProEt.topology X)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).over (V i)))) :
    ∃ β : SpSignedComparison f R S c L M, (β.signed 1).hom = t.hom := by
  let a := moduleStructuralMap f R S c
  let e := modulePullbackComparison f R S c
  have hu (N : Scheme.proEtaleRingModules Y R) (V : Y.ProEt)
      (n : N.val.obj (op V)) :
      ((e.hom.app N).val.app (op ((Scheme.proEtaleBaseChange f).obj V)))
        (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app N).val.app (op V) n) =
      SheafOfModules.ringedSitePullbackSection.{u + 1, u, u + 1}
        (U := Scheme.proEtaleBaseChange f) a
        (SheafOfModules.module_pushforward_isRightAdjoint_of_universes.{u + 1, u, u + 1}
          (U := Scheme.proEtaleBaseChange f) _) N V n := by
    exact modulePullbackComparison_unit f R S c N V n
  -- The unit formula is the interface; keep the adjunction comparison abstract.
  clear_value e
  let t' := (e.app L).symm ≪≫ t
  have ht' : (e.app L).hom ≫ t'.hom = t.hom := (e.app L).hom_inv_id_assoc t.hom
  clear_value t'
  have hh :=
    SheafOfModules.SignedLineDerivedBaseChange.signed_line_derived_base_change.{
      u + 1, u, u + 1, u + 2}
      (U := Scheme.proEtaleBaseChange f) a L M t'
      (Scheme.proEtaleBaseChangeCoverPreserving f)
      (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1})
      (Scheme.proEtaleSheafAdjunction f RingCat.{u + 1})
      (moduleStructuralMap_isIso f R S c) hL hM
  obtain ⟨hAdd, hLim, hCol, T,
    ⟨⟨hzero, hone, hpos, hneg⟩, _, _, _, hDerived⟩, _⟩ := hh
  let := hAdd
  let := hLim
  let := hCol
  obtain ⟨gammaComp, _, b, _, _⟩ := hDerived
  let Ts : ∀ d : ℤ, (Scheme.proEtaleRingModulePullback f R S c).obj
      (WeilConjectures.coefficientTwistLine Y (R := R) L d) ≅
        WeilConjectures.coefficientTwistLine X (R := S) M d :=
    fun d ↦ e.app _ ≪≫ T d
  have hOne : (Ts 1).hom = t.hom := by
    change (e.app L).hom ≫ (T 1).hom = t.hom
    rw [hone]
    exact ht'
  refine ⟨{ signed := Ts, zero := ?_, positive := ?_, negative := ?_, derived := ?_ }, hOne⟩
  · intro V r
    simp only [Ts, Iso.trans_hom, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [hu]
    exact (hzero V r).trans (moduleStructuralMap_apply f R S c V r)
  · intro n V x y
    simp only [Ts, Iso.trans_hom,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [hu, hu, hu]
    have h := hpos n V y x
    rw [hone]
    exact h
  · intro n V φ x
    simp only [Ts, Iso.trans_hom,
      SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply]
    erw [hu, hu]
    exact (hneg n V φ x).trans (moduleStructuralMap_apply f R S c V
      (φ.app (op (Over.mk (𝟙 V))) x))
  · intro d
    let ed := Functor.mapDerivedCategoryNatIso e
    have hb := (b d).2.2
    dsimp only [SheafOfModules.SignedLineDerivedBaseChange.derivedLine] at hb
    unfold spTwistFunctor
    change SheafOfModules.SignedLineDerivedBaseChange.derivedLine.{u + 1, u, u + 1, u + 2} R _ ⋙
        (Scheme.proEtaleRingModulePullback f R S c).mapDerivedCategory ≅
      (Scheme.proEtaleRingModulePullback f R S c).mapDerivedCategory ⋙
        SheafOfModules.SignedLineDerivedBaseChange.derivedLine.{u + 1, u, u + 1, u + 2} S _
    exact Functor.isoWhiskerLeft _ ed ≪≫ hb ≪≫
      Functor.isoWhiskerRight ed.symm _

end SignedPullbackProof

private theorem commonCover_coversTop (T : Scheme.{u})
    {I : Type (u + 1)} (V : I → T.ProEt)
    (v : ∀ i : I, V i ⟶ Scheme.ProEt.mk (𝟙 T))
    (hc : Presieve.ofArrows V v ∈ (Scheme.ProEt.precoverage T).coverings _) :
    (Scheme.ProEt.topology T).CoversTop V := by
  rw [GrothendieckTopology.coversTop_iff_of_isTerminal _ (Scheme.ProEt.mk (𝟙 T))
    (MorphismProperty.Over.mkIdTerminal _ _)]
  apply (Scheme.ProEt.topology T).superset_covering (Sieve.ofArrows_le_ofObjects V v)
  exact Precoverage.generate_mem_toGrothendieck hc

private theorem finiteLine_commonCover (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty ((Scheme.tateFiniteLine T ℓ A r a).over (V i) ≅
        (SheafOfModules.unit (Scheme.purTwistRing T
          (Scheme.tateFiniteCoefficient T A))).over (V i)) := by
  obtain ⟨I, V, v, ζ, e, hc, _, _, hf, _, _⟩ := spTwists_commonCover T ℓ
  have hA : (ℓ ^ (r + 1) : A) = 0 := by
    have h := congrArg a (ZMod.natCast_self (ℓ ^ (r + 1)))
    simpa only [map_natCast, map_zero, Nat.cast_pow, map_pow] using h
  have ha : a = ZMod.castHom (ringChar.dvd
      (by simpa only [Nat.cast_pow] using hA)) A := Subsingleton.elim _ _
  refine ⟨I, V, commonCover_coversTop T V v hc, ?_⟩
  intro i
  simpa only [spFiniteTwist, ← ha] using hf A r hA i

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
attribute [local irreducible] Scheme.proEtaleModuleInverseImage
private def extensionPresheafIso
    (R S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1}) (a : R ⟶ S)
    (M : Scheme.proEtaleRingModules X R) :
    SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a M ≅
      SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, u + 1, u + 1} a M := by
  refine PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) ?_
  intro U W g
  change SheafOfModules.changeOfRingsMap.{u, u + 1, u + 1} a M g =
    SheafOfModules.changeOfRingsMapOfUniverses.{u, u + 1, u + 1, u + 1} a M g
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  exact (SheafOfModules.changeOfRingsMap_tmul a M g 1 m).trans
    (SheafOfModules.changeOfRingsMap_tmulOfUniverses a M g 1 m).symm

-- Compare the two scalar-extension presentations and their sheafification units.
private theorem pullback_unit_mate_isIso
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (M : Scheme.proEtaleRingModules Y R) :
    IsIso (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).obj M)
      ((SheafOfModules.toSheaf.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)).obj
          ((Scheme.proEtaleRingModulePullback f R S c).obj M))).symm
        ((SheafOfModules.toSheaf.{u + 1} ((sheafCompose (Scheme.ProEt.topology Y)
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)).map
            ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M))) := by
  let ai := Scheme.canonicalAdjunction f R
  let N := (Scheme.proEtaleModuleInverseImage f R).obj M
  let P := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R)
  let Q := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)
  let Q' := SheafOfModules.toSheaf ((sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R))
  let a := Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  let k₀ := (a.homEquiv (P.obj M) (Q'.obj N)).symm (P.map (ai.unit.app M))
  have hk₀ : IsIso k₀ :=
    Scheme.proEtaleModuleInverseImage_unitComparison_isIso f R ai M
  have hk₀adj : (a.homEquiv _ _) k₀ = P.map (ai.unit.app M) :=
    Equiv.apply_symm_apply _ _
  clear_value k₀
  obtain ⟨theta, ht, _, _⟩ :=
    SheafOfModules.exists_scalarExtensionRingIso.{u + 1, u, u + 1, u + 1} c
  let ec := extensionPresheafIso _ _ c.hom N
  let sh := PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
    (𝟙 ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S).obj)
  let es := sh.mapIso ec
  let et : Q.obj ((Scheme.proEtaleRingModulePullback f R S c).obj M) ≅ Q'.obj N :=
    by
      dsimp only [Scheme.proEtaleRingModulePullback, Scheme.proEtaleRingModulePullbackObj,
        SheafOfModules.changeOfRings]
      exact Q.mapIso (es ≪≫ theta N)
  have hs (W : X.ProEtᵒᵖ)
      (m : N.val.obj W) (s : S.obj.obj W) :
      es.hom.val.app W
        (((PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (R := ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) (𝟙 _)).unit.app
          (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c.hom N)).app W
            (s ⊗ₜ[_, (c.hom.hom.app W).hom] m)) =
      SheafOfModules.scalarExtensionRingIsoTmul.{u + 1, u, u + 1, u + 1} c.hom N W m s := by
    have h := (PresheafOfModules.sheafificationAdjunction.{u + 1, u, u + 1, u + 1}
          (R := ((sheafCompose (Scheme.ProEt.topology X)
            (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S)) (𝟙 _)).unit.naturality ec.hom
    exact congrArg (fun k ↦ k.app W (s ⊗ₜ[_, (c.hom.hom.app W).hom] m)) h.symm
  clear_value es
  have hu : P.map ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M) ≫
      (Scheme.proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map et.hom =
        P.map (ai.unit.app M) := by
    ext V m
    obtain ⟨g, hg, h⟩ := (Scheme.proEtaleRingModuleAdjunction_existsUnique f R S c).choose_spec.1
      M _ (𝟙 _)
    have hh := h V m
    rw [Adjunction.homEquiv_id, Adjunction.homEquiv_unit] at hh
    change (theta N).hom.val.app ((Scheme.proEtaleBaseChange f).op.obj V)
      (es.hom.val.app _
        (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m)) =
        (ai.unit.app M).val.app V m
    change (((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M).val.app V m) = _
      at hh
    erw [hh]
    erw [hg]
    erw [hs, ht]
    simp only [map_one, one_smul]
    exact (Scheme.canonicalUnit_sections f R M V m).symm
  clear_value et
  let k := (a.homEquiv (P.obj M)
    (Q.obj ((Scheme.proEtaleRingModulePullback f R S c).obj M))).symm
    (P.map ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M))
  have hkadj : (a.homEquiv _ _) k =
      P.map ((Scheme.proEtaleRingModuleAdjunction f R S c).unit.app M) :=
    Equiv.apply_symm_apply _ _
  change IsIso k
  clear_value k a
  have hk : k ≫ et.hom = k₀ := by
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_naturality_right, hkadj, hk₀adj]
    exact hu
  have : IsIso (k ≫ et.hom) := by rw [hk]; infer_instance
  exact IsIso.of_isIso_comp_right k et.hom

end

section

variable (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
include T
private theorem zmodModule_normalized
    (M : SheafOfModules.{u + 1} (constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N)) :
    IsConstantZModSheafModuleStructure.{u + 1, u, u + 1} (Scheme.ProEt.topology T) N
      ((SheafOfModules.toSheaf.{u + 1} _).obj M)
      (fun V ↦ (M.val.obj V).isModule) := by
  constructor
  · intro V z x
    let := (M.val.obj V).isModule
    change @SMul.smul
      ((constantZModRingSheaf (Scheme.ProEt.topology T) N).obj.obj V)
      (M.val.obj V) (M.val.obj V).isModule.toSMul
      (((toSheafify (Scheme.ProEt.topology T) ((Functor.const T.ProEtᵒᵖ).obj
        (RingCat.of (ULift.{u + 1} (ZMod N))))).app V).hom
          (z : ULift.{u + 1} (ZMod N))) x = z • x
    rw [map_intCast]
    exact Int.cast_smul_eq_zsmul
      ((constantZModRingSheaf (Scheme.ProEt.topology T) N).obj.obj V) z (show M.val.obj V from x)
  · intro V W a r x
    exact PresheafOfModules.map_smul M.val a r x
include hN
private def zmodModuleHom
    (M M' : SheafOfModules.{u + 1}
      (constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N))
    (a : (SheafOfModules.toSheaf.{u + 1} _).obj M ⟶ (SheafOfModules.toSheaf.{u + 1} _).obj M') :
    M ⟶ M' :=
  ⟨PresheafOfModules.homMk a.hom
    (torsionSheaf_hom_linear (Scheme.ProEt.topology T) N hN _ _
      (constantZModModuleSheaf_nsmul (Scheme.ProEt.topology T) N hN M)
      (constantZModModuleSheaf_nsmul (Scheme.ProEt.topology T) N hN M') a _ _
      (zmodModule_normalized T N M) (zmodModule_normalized T N M'))⟩

private def finiteRingModuleHom
    (R : Sheaf (Scheme.ProEt.topology T) RingCat.{u + 1})
    (e : R ≅ constantZModRingSheaf.{u, u + 1} (Scheme.ProEt.topology T) N)
    (M M' : SheafOfModules.{u + 1} R)
    (a : (SheafOfModules.toSheaf R).obj M ⟶ (SheafOfModules.toSheaf R).obj M') : M ⟶ M' := by
  let P := (SheafOfModules.restrictScalars e.inv).obj M
  let Q := (SheafOfModules.restrictScalars e.inv).obj M'
  let b := zmodModuleHom T N hN P Q a
  refine ⟨PresheafOfModules.homMk a.hom ?_⟩
  intro V r x
  let := (M.val.obj V).isModule
  let := (M'.val.obj V).isModule
  have h := ((b.val.app V).hom.map_smul (e.hom.hom.app V r) x)
  change a.hom.app V (e.inv.hom.app V (e.hom.hom.app V r) • x) =
    e.inv.hom.app V (e.hom.hom.app V r) • (show M'.val.obj V from a.hom.app V x) at h
  have he : e.inv.hom.app V (e.hom.hom.app V r) = r :=
    congrArg (fun k ↦ k.hom.app V r) e.hom_inv_id
  rw [he] at h
  exact h

end

section

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
private abbrev restr (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S) :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map p)
private abbrev tens (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) :=
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, u + 1, u + 1} p M
private abbrev tensorUnit' (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) : M ⟶ (restr T p).obj (tens T p M) :=
  Scheme.tensorHomEquiv T p M (tens T p M) (𝟙 _)
private theorem tensorUnit'_apply (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) (V : T.ProEt) (x : M.val.obj (op V)) :
    (tensorUnit' T p M).val.app (op V) x = Scheme.purScalarSection R S p M V 1 x :=
  Scheme.tensorHomEquiv_apply T p M _ _ (op V) x
variable
    (RY SY : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (RX SX : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (cR : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RY ≅ RX)
    (cS : (Scheme.proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SY ≅ SX)
    (pY : RY ⟶ SY) (pX : RX ⟶ SX)
    (hsq : pY ≫ Scheme.proEtaleRingDirectImageMap f SY SX cS =
      Scheme.proEtaleRingDirectImageMap f RY RX cR ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map pX)
private def directScalarIso'
    (H : Scheme.proEtaleRingModules X SX) :
    (restr Y pY).obj ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H) ≅
      (Scheme.proEtaleRingModuleDirectImage f RY RX cR).obj ((restr X pX).obj H) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun V ↦ LinearEquiv.toModuleIso
      (X₁ := (((restr Y pY).obj
        ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H)).val.obj V))
      (X₂ := (((Scheme.proEtaleRingModuleDirectImage f RY RX cR).obj
        ((restr X pX).obj H)).val.obj V))
      { __ := AddEquiv.refl _
        map_smul' := fun r m ↦ by
          change @SMul.smul (SX.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul
            ((Scheme.proEtaleRingDirectImageMap f SY SX cS).hom.app V
              (pY.hom.app V r)) (show H.val.obj _ from m) =
            @SMul.smul (SX.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul
              (pX.hom.app _ ((Scheme.proEtaleRingDirectImageMap f RY RX cR).hom.app V r))
                (show H.val.obj _ from m)
          exact congrArg (fun z ↦ @SMul.smul _ (H.val.obj
            ((Scheme.proEtaleBaseChange f).op.obj V))
            (H.val.obj ((Scheme.proEtaleBaseChange f).op.obj V)).isModule.toSMul z m)
            (congrArg (fun k ↦ k.hom.app V r) hsq) })
      (by intro V W a; ext m; rfl))
private def tensorPullbackHomEquiv'
    (M : Scheme.proEtaleRingModules Y RY) (H : Scheme.proEtaleRingModules X SX) :
    ((Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ H) ≃
      ((Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ (restr X pX).obj H) :=
  ((Scheme.proEtaleRingModuleAdjunction f SY SX cS).homEquiv (tens Y pY M) H).trans
    ((Scheme.tensorHomEquiv Y pY M
      ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H)).trans
      ((Iso.homCongr (Iso.refl M) (directScalarIso' f RY SY RX SX cR cS pY pX hsq H)).trans
        ((Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv M
          ((restr X pX).obj H)).symm))
private theorem tensorPullbackHomEquiv'_apply
    (M : Scheme.proEtaleRingModules Y RY) (H : Scheme.proEtaleRingModules X SX)
    (b : (Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ H)
    (V : Y.ProEt) (x : M.val.obj (op V)) :
    (tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H b).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app (op V) x) =
    b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app
    (tens Y pY M)).val.app
        (op V) (Scheme.purScalarSection RY SY pY M V 1 x)) := by
  have he := ((Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv _ _).apply_symm_apply
      ((Scheme.tensorHomEquiv Y pY M
        ((Scheme.proEtaleRingModuleDirectImage f SY SX cS).obj H)
        (((Scheme.proEtaleRingModuleAdjunction f SY SX cS).homEquiv _ _) b)) ≫
          (directScalarIso' f RY SY RX SX cR cS pY pX hsq H).hom)
  rw [Adjunction.homEquiv_unit] at he
  exact congrArg (fun k ↦ k.val.app (op V) x) he

private theorem pullback_unit_ext'
    (M : Scheme.proEtaleRingModules Y RY) (H : Scheme.proEtaleRingModules X RX)
    {a b : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ H}
    (h : ∀ (V : Y.ProEt) (x : M.val.obj (op V)),
      a.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app (op V) x) =
      b.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app (op V) x)) :
    a = b := by
  apply ((Scheme.proEtaleRingModuleAdjunction f RY RX cR).homEquiv M H).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  ext V x
  exact h V.unop x
private theorem tensorPullbackHomEquiv'_naturality
    (M : Scheme.proEtaleRingModules Y RY) (H H' : Scheme.proEtaleRingModules X SX)
    (b : (Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ H)
    (g : H ⟶ H') :
    tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H' (b ≫ g) =
      tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H b ≫
        (restr X pX).map g := by
  apply pullback_unit_ext' f RY RX cR M ((restr X pX).obj H')
  intro V x
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app, ModuleCat.comp_apply,
    tensorPullbackHomEquiv'_apply]
  rfl
attribute [local irreducible] tensorPullbackHomEquiv' directScalarIso'

private theorem tensorHomEquiv'_naturality (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) (H H' : Scheme.proEtaleRingModules T S)
    (b : tens T p M ⟶ H) (g : H ⟶ H') :
    Scheme.tensorHomEquiv T p M H' (b ≫ g) =
      Scheme.tensorHomEquiv T p M H b ≫ (restr T p).map g := by
  apply SheafOfModules.hom_ext
  ext V x
  unfold Scheme.tensorHomEquiv Scheme.tensorPresheafHomEquiv Scheme.tensorToRestriction
  rfl
private def tensorMap'
    (M : Scheme.proEtaleRingModules Y RY) (N : Scheme.proEtaleRingModules X RX)
    (c : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ N) :
    (Scheme.proEtaleRingModulePullback f SY SX cS).obj (tens Y pY M) ⟶ tens X pX N :=
  (tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M (tens X pX N)).symm
    (c ≫ tensorUnit' X pX N)
private theorem tensorMap'_homEquiv
    (M : Scheme.proEtaleRingModules Y RY) (N : Scheme.proEtaleRingModules X RX)
    (c : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ N) :
    tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M (tens X pX N)
        (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c) =
      c ≫ tensorUnit' X pX N := Equiv.apply_symm_apply _ _

attribute [local irreducible] tensorMap'

private theorem tensorMap'_isIso
    (M : Scheme.proEtaleRingModules Y RY) (N : Scheme.proEtaleRingModules X RX)
    (c : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ N) [IsIso c] :
    IsIso (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c) := by
  apply isIso_of_coyoneda_map_bijective
  intro H
  let e := (Scheme.tensorHomEquiv X pX N H).trans
    ((Iso.homCongr (asIso c).symm (Iso.refl _)).trans
      (tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H).symm)
  have hh : (fun g ↦ tensorMap' f RY SY RX SX cR cS pY pX hsq M N c ≫ g) = e := by
    funext g
    apply (tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H).injective
    rw [tensorPullbackHomEquiv'_naturality]
    have hm : tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M
        (tens X pX N) (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c) =
        c ≫ tensorUnit' X pX N :=
      tensorMap'_homEquiv f RY SY RX SX cR cS pY pX hsq M N c
    rw [hm]
    change c ≫ tensorUnit' X pX N ≫ (restr X pX).map g = _
    erw [← tensorHomEquiv'_naturality X pX N _ H (𝟙 _) g]
    exact ((tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M H).apply_symm_apply _).symm
  rw [hh]
  exact e.bijective
private theorem purScalarSection_smul (T : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1}} (p : R ⟶ S)
    (M : Scheme.proEtaleRingModules T R) (V : T.ProEt)
    (a : S.obj.obj (op V)) (x : M.val.obj (op V)) :
    Scheme.purScalarSection R S p M V a x =
      a • Scheme.purScalarSection R S p M V 1 x := by
  have h := Scheme.tensorHomEquiv_tmul T p M (tens T p M) (𝟙 _) (op V) a x
  change Scheme.purScalarSection R S p M V a x =
    a • (show (tens T p M).val.obj (op V) from
      (tensorUnit' T p M).val.app (op V) x) at h
  rw [tensorUnit'_apply] at h
  exact h
private theorem tensorMap'_apply
    (M : Scheme.proEtaleRingModules Y RY) (N : Scheme.proEtaleRingModules X RX)
    (c : (Scheme.proEtaleRingModulePullback f RY RX cR).obj M ⟶ N)
    (V : Y.ProEt) (a : SY.obj.obj (op V)) (x : M.val.obj (op V)) :
    (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V))
      (((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app
    (tens Y pY M)).val.app
        (op V) (Scheme.purScalarSection RY SY pY M V a x)) =
    Scheme.purScalarSection RX SX pX N ((Scheme.proEtaleBaseChange f).obj V)
      ((Scheme.proEtaleRingDirectImageMap f SY SX cS).hom.app (op V) a)
      (c.val.app (op ((Scheme.proEtaleBaseChange f).obj V))
        (((Scheme.proEtaleRingModuleAdjunction f RY RX cR).unit.app M).val.app
          (op V) x)) := by
  rw [purScalarSection_smul]
  erw [(((Scheme.proEtaleRingModuleAdjunction f SY SX cS).unit.app
    (tens Y pY M)).val.app (op V)).hom.map_smul]
  erw [((tensorMap' f RY SY RX SX cR cS pY pX hsq M N c).val.app _).hom.map_smul]
  have he := tensorPullbackHomEquiv'_apply f RY SY RX SX cR cS pY pX hsq M
    (tens X pX N) (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c) V x
  have hm : tensorPullbackHomEquiv' f RY SY RX SX cR cS pY pX hsq M
      (tens X pX N) (tensorMap' f RY SY RX SX cR cS pY pX hsq M N c) =
      c ≫ tensorUnit' X pX N :=
      tensorMap'_homEquiv f RY SY RX SX cR cS pY pX hsq M N c
  rw [hm] at he
  rw [← he]
  change (Scheme.proEtaleRingDirectImageMap f SY SX cS).hom.app (op V) a •
    (show (tens X pX N).val.obj (op ((Scheme.proEtaleBaseChange f).obj V)) from
      (tensorUnit' X pX N).val.app _ _) = _
  rw [tensorUnit'_apply]
  exact (purScalarSection_smul X pX N _ _ _).symm

end

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
private def rootModuleDirect (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    Scheme.purTwistRootsModule Y ℓ r ⟶
      (Scheme.proEtaleRingModuleDirectImage f
        (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
        (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)).obj
          (Scheme.purTwistRootsModule X ℓ r) :=
  finiteRingModuleHom Y (ℓ ^ (r + 1)) (pow_pos (Fact.out : ℓ.Prime).pos _)
    (Scheme.purTwistRing Y (Scheme.purTwistFiniteRing Y ℓ r))
    (Scheme.purTwistFiniteRingIso Y ℓ r) _ _
    (Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1)))

private def rootModuleComparison (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    (Scheme.proEtaleRingModulePullback f
      (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
      (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)).obj
        (Scheme.purTwistRootsModule Y ℓ r) ⟶ Scheme.purTwistRootsModule X ℓ r :=
  ((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _).symm
    (rootModuleDirect f ℓ r)

private theorem rootModuleComparison_underlying (ℓ : ℕ) [Fact ℓ.Prime] (r : ℕ) :
    (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
      ((SheafOfModules.toSheaf _).map
        ((Scheme.proEtaleRingModuleAdjunction f
          (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
          (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)).unit.app
            (Scheme.purTwistRootsModule Y ℓ r)))) ≫
      (SheafOfModules.toSheaf _).map (rootModuleComparison f ℓ r) =
        Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (r + 1)) := by
  rw [Scheme.proEtaleRootsOfUnityInverseImageMap]
  apply ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_right, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  have h := ((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _).apply_symm_apply
    (rootModuleDirect f ℓ r)
  rw [Adjunction.homEquiv_unit] at h
  change (SheafOfModules.toSheaf _).map
    (((Scheme.proEtaleRingModuleAdjunction f _ _ _).unit.app
      (Scheme.purTwistRootsModule Y ℓ r)) ≫
        (Scheme.proEtaleRingModuleDirectImage f _ _ _).map
          (rootModuleComparison f ℓ r)) = _
  exact congrArg (fun k ↦ (SheafOfModules.toSheaf _).map k) h

private theorem rootModuleComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] (r : ℕ) :
    IsIso (rootModuleComparison f ℓ r) := by
  have := spRoots_cartesian f ℓ (r + 1)
  have hu := pullback_unit_mate_isIso f
    (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
    (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)
    (Scheme.purTwistRootsModule Y ℓ r)
  let unitMate := (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _).symm
    ((SheafOfModules.toSheaf _).map
      ((Scheme.proEtaleRingModuleAdjunction f
        (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
        (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)).unit.app
          (Scheme.purTwistRootsModule Y ℓ r))))
  have : IsIso unitMate := hu
  have : IsIso (unitMate ≫ (SheafOfModules.toSheaf _).map (rootModuleComparison f ℓ r)) := by
    rw [show unitMate ≫ (SheafOfModules.toSheaf _).map (rootModuleComparison f ℓ r) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (r + 1)) from
        rootModuleComparison_underlying f ℓ r]
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf _).map (rootModuleComparison f ℓ r)) :=
    IsIso.of_isIso_comp_left unitMate _
  exact isIso_of_reflects_iso (rootModuleComparison f ℓ r) (SheafOfModules.toSheaf _)

private theorem constantStructural_direct (A : Type (u + 1)) [CommRing A] :
    Scheme.proEtaleRingDirectImageMap f
      (Scheme.tateFiniteCoefficient Y A) (Scheme.tateFiniteCoefficient X A)
      (StrictTower.constantRingIso A f) =
      Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1} (CommRingCat.of A) := by
  change ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _)
    (((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).symm _) = _
  exact Equiv.apply_symm_apply _ _

private theorem finiteScalarSquare (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    Scheme.tateFiniteScalar Y ℓ A r a ≫
      Scheme.proEtaleRingDirectImageMap f
        (Scheme.tateFiniteCoefficient Y A) (Scheme.tateFiniteCoefficient X A)
        (StrictTower.constantRingIso A f) =
    Scheme.proEtaleRingDirectImageMap f
      (Scheme.purTwistFiniteRing Y ℓ r) (Scheme.purTwistFiniteRing X ℓ r)
      (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f) ≫
        (Scheme.proEtaleSheafDirectImage f CommRingCat.{u + 1}).map
          (Scheme.tateFiniteScalar X ℓ A r a) := by
  rw [constantStructural_direct f A,
    constantStructural_direct f (ULift.{u + 1} (ZMod (ℓ ^ (r + 1))))]
  let φ : CommRingCat.of (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (a.comp ULift.ringEquiv.toRingHom)
  simpa only [Scheme.tateFiniteScalar] using Scheme.constantDirect_naturality f φ

private def finiteFirstComparison (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    (Scheme.proEtaleRingModulePullback f
      (Scheme.tateFiniteCoefficient Y A) (Scheme.tateFiniteCoefficient X A)
      (StrictTower.constantRingIso A f)).obj (Scheme.tateFiniteLine Y ℓ A r a) ⟶
        Scheme.tateFiniteLine X ℓ A r a :=
  tensorMap' f _ _ _ _
    (StrictTower.constantRingIso (ULift.{u + 1} (ZMod (ℓ ^ (r + 1)))) f)
    (StrictTower.constantRingIso A f) _ _ (finiteScalarSquare f ℓ A r a)
    (Scheme.purTwistRootsModule Y ℓ r) (Scheme.purTwistRootsModule X ℓ r)
    (rootModuleComparison f ℓ r)

private theorem finiteFirstComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    IsIso (finiteFirstComparison f ℓ A r a) := by
  have := rootModuleComparison_isIso f ℓ r
  exact tensorMap'_isIso f _ _ _ _ _ _ _ _ (finiteScalarSquare f ℓ A r a) _ _ _

private theorem finiteFirstComparison_apply (ℓ : ℕ) [Fact ℓ.Prime]
    (A : Type (u + 1)) [CommRing A] (r : ℕ)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) (V : Y.ProEt)
    (b : (Scheme.tateFiniteCoefficient Y A).obj.obj (op V))
    (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)) :
    (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
      (finiteFirstComparison f ℓ A r a)).val.app (op V)
        (Scheme.tateFiniteTensor Y ℓ A r a V b z) =
      Scheme.tateFiniteTensor X ℓ A r a ((Scheme.proEtaleBaseChange f).obj V)
        ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
          (CommRingCat.of A)).hom.app (op V) b)
        ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app (op V) z) := by
  rw [Adjunction.homEquiv_unit]
  have h := tensorMap'_apply f _ _ _ _ _ _ _ _ (finiteScalarSquare f ℓ A r a)
    _ _ (rootModuleComparison f ℓ r) V b z
  have hr := ((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _).apply_symm_apply
    (rootModuleDirect f ℓ r)
  rw [Adjunction.homEquiv_unit] at hr
  have hv := congrArg (fun k ↦ k.val.app (op V) z) hr
  change (rootModuleComparison f ℓ r).val.app _
    (((Scheme.proEtaleRingModuleAdjunction f _ _ _).unit.app
      (Scheme.purTwistRootsModule Y ℓ r)).val.app (op V) z) = _ at hv
  erw [hv, constantStructural_direct] at h
  exact h

private theorem finiteFirstComparison_kummer (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (A : Type (u + 1)) [CommRing A] [Finite A] (r n : ℕ) (hrn : r ≤ n)
    (a : ZMod (ℓ ^ (r + 1)) →+* A) :
    (Scheme.proEtaleRingModulePullback f _ _ _).map (spFiniteKummer Y ℓ A r n hrn a) ≫
      finiteFirstComparison f ℓ A r a =
    finiteFirstComparison f ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
        (ZMod (ℓ ^ (r + 1))))) ≫ spFiniteKummer X ℓ A r n hrn a := by
  apply ((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  apply (Scheme.tensorHomEquiv Y
    (Scheme.tateFiniteScalar Y ℓ A n
      (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ hrn))
        (ZMod (ℓ ^ (r + 1)))))) (Scheme.purTwistRootsModule Y ℓ n) _).injective
  ext V x
  simp only [Scheme.tensorHomEquiv_apply]
  have hY := (spFiniteKummer_existsUnique Y ℓ A r n hrn a).exists.choose_spec.2 V.unop 1 x
  change (spFiniteKummer Y ℓ A r n hrn a).val.app V _ = _ at hY
  have hX := (spFiniteKummer_existsUnique X ℓ A r n hrn a).exists.choose_spec.2
    ((Scheme.proEtaleBaseChange f).obj V.unop)
    ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
      (CommRingCat.of A)).hom.app V 1)
    ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (n + 1))).hom.app V x)
  change (spFiniteKummer X ℓ A r n hrn a).val.app _ _ = _ at hX
  change (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
    (finiteFirstComparison f ℓ A r a)).val.app V
      ((spFiniteKummer Y ℓ A r n hrn a).val.app V _) =
    (spFiniteKummer X ℓ A r n hrn a).val.app _
      ((((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
        (finiteFirstComparison f ℓ A n _)).val.app V _)
  erw [hY, finiteFirstComparison_apply, finiteFirstComparison_apply, hX]
  congr 1
  exact congrArg (fun k ↦ k.hom.app V x)
    (Scheme.roots_direct_transition f (ℓ ^ (r + 1)) (ℓ ^ (n + 1))
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ (Nat.succ_le_succ hrn)))

attribute [local irreducible] finiteFirstComparison rootModuleComparison
  rootModuleDirect tensorMap' directScalarIso' tensorPullbackHomEquiv'

/-- The finite signed comparison is normalized on root tensors, and commutes with
all annihilating-exponent Kummer identifications. Source: blueprint Finite coefficients
and Powers and duals paragraphs
(blueprint: lemma-inverse-image-coefficient-sheaves--2).
Proof: tensor the root comparison with the constant coefficient comparison. The
map sends u tensor a to the pulled-back u tensor the pulled-back a. Pure tensors
locally generate, so this determines it uniquely. The Kummer square is the root
power square. Tensor this comparison for positive powers and use alpha in degree
zero. For negative powers pull back evaluation; finite local freeness makes the
dual comparison invertible. Apply the unbounded derived tensor comparison with
one factor the signed line in degree zero. This gives the natural derived
isomorphism for every K, without any boundedness or constructibility restriction. -/
theorem spFiniteTwists_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (A : Type (u + 1)) [CommRing A] [Finite A] :
    ∃ β : ∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A),
      SpSignedComparison f (Scheme.tateFiniteCoefficient Y A)
        (Scheme.tateFiniteCoefficient X A)
        (StrictTower.constantRingIso A f)
        (Scheme.tateFiniteLine Y ℓ A r a) (Scheme.tateFiniteLine X ℓ A r a),
      (∀ (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A) (V : Y.ProEt)
        (b : (Scheme.tateFiniteCoefficient Y A).obj.obj (op V))
        (z : (Scheme.proEtaleRootsOfUnitySheaf Y (ℓ ^ (r + 1))).obj.obj (op V)),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          ((β r a).signed 1).hom).val.app (op V)
            (Scheme.tateFiniteTensor Y ℓ A r a V b z) =
          Scheme.tateFiniteTensor X ℓ A r a ((Scheme.proEtaleBaseChange f).obj V)
            ((Scheme.proEtaleConstantDirectImageMap f CommRingCat.{u + 1}
              (CommRingCat.of A)).hom.app (op V) b)
            ((Scheme.proEtaleRootsOfUnityDirectImageMap f (ℓ ^ (r + 1))).hom.app
              (op V) z)) ∧
      (∀ (r n : ℕ) (h : r ≤ n) (a : ZMod (ℓ ^ (r + 1)) →+* A),
        (Scheme.proEtaleRingModulePullback f _ _ _).map
          (spFiniteKummer Y ℓ A r n h a) ≫ ((β r a).signed 1).hom =
        ((β n (a.comp (ZMod.castHom (pow_dvd_pow ℓ (Nat.succ_le_succ h))
          (ZMod (ℓ ^ (r + 1)))))).signed 1).hom ≫ spFiniteKummer X ℓ A r n h a) := by
  classical
  have hb (r : ℕ) (a : ZMod (ℓ ^ (r + 1)) →+* A) :
      ∃ β : SpSignedComparison f (Scheme.tateFiniteCoefficient Y A)
          (Scheme.tateFiniteCoefficient X A) (StrictTower.constantRingIso A f)
          (Scheme.tateFiniteLine Y ℓ A r a) (Scheme.tateFiniteLine X ℓ A r a),
        (β.signed 1).hom = finiteFirstComparison f ℓ A r a := by
    have := finiteFirstComparison_isIso f ℓ A r a
    exact signedComparison_exists f _ _ (StrictTower.constantRingIso A f) _ _
      (asIso (finiteFirstComparison f ℓ A r a))
      (finiteLine_commonCover Y ℓ A r a) (finiteLine_commonCover X ℓ A r a)
  choose β hβ using hb
  refine ⟨β, ?_, ?_⟩
  · intro r a V b z
    rw [hβ]
    exact finiteFirstComparison_apply f ℓ A r a V b z
  · intro r n h a
    rw [hβ, hβ]
    exact finiteFirstComparison_kummer f ℓ A r n h a

/-- A comparison over alpha in the internal and sectionwise module encodings.
The signed first comparison has exactly the given abelian adjunct, which fixes
its linear lift; the module isomorphisms encode semilinearity over alpha at every
signed degree. Source: blueprint compatibility with alpha and module structures
(blueprint: lemma-inverse-image-coefficient-sheaves--2). -/
def SpInternalCartesian
    (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : Mod (Sheaf (Scheme.ProEt.topology Y) AddCommGrpCat.{u + 1}) (condensedRingObj Λ Y))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) AddCommGrpCat.{u + 1}) (condensedRingObj Λ X))
    (τ : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj L.X ⟶ M.X) : Prop :=
  IsIso τ ∧
    ∃ β : SpSignedComparison f
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology Y)
          (condensedRingObj Λ Y))
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u} (Scheme.ProEt.topology X)
          (condensedRingObj Λ X)) (spCoefficientIso f Λ)
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology Y) (condensedRingObj Λ Y)).functor.obj L)
        ((InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) (condensedRingObj Λ X)).functor.obj M),
      ∀ (V : Y.ProEtᵒᵖ) (m : L.X.obj.obj V),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          (β.signed 1).hom).val.app V m =
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _) τ).hom.app
          V m

private theorem integralComparison_π (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (n : ℕ) :
    spIntegralComparison f ℓ E ≫ (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom =
      (upperStar AddCommGrpCat.{u + 1} f).map
          (limit.π (spIntegralTwistSystem Y ℓ E) (op n)).hom ≫
        integralLevelComparison f ℓ E n := by
  unfold spIntegralComparison
  exact (Classical.choose_spec (spIntegralComparison_existsUnique f ℓ E)).1 n

section
private theorem nativeIntegralComparison_isIso (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    IsIso (spIntegralComparison f ℓ E) := by
  let F := upperStar AddCommGrpCat.{u + 1} f
  let UY := Mod.forget (C := AbSheaf Y)
    (D := AbSheaf Y)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) Y)
  let UX := Mod.forget (C := AbSheaf X)
    (D := AbSheaf X)
    (condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) X)
  let a := spIntegralTwistSystem Y ℓ E
  let b := spIntegralTwistSystem X ℓ E
  let α := integralComparisonSystem f ℓ E
  have hi (n : ℕᵒᵖ) : IsIso (α.app n) := by
    rcases n with ⟨n⟩
    have := spRoots_cartesian f ℓ (n + 1)
    change IsIso ((integralComparisonSystem f ℓ E).app (op n))
    rw [integralComparisonSystem_app]
    dsimp only [integralLevelComparison]
    infer_instance
  have : IsIso α := NatIso.isIso_of_isIso_app α
  apply comparisonIntoPreservedLimit_isIso UY UX F a b α
    (spIntegralTwist_inverseImage_isLimit f ℓ E).some (spIntegralComparison f ℓ E)
  rintro ⟨n⟩
  change spIntegralComparison f ℓ E ≫ _ = _ ≫ (integralComparisonSystem f ℓ E).app (op n)
  rw [integralComparisonSystem_app]
  exact integralComparison_π f ℓ E n

end

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] spIntegersMap spEllMap spIntegralTwistMap
  spRationalTwistMap
private theorem integersMap_spec (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    IsMonHom (spIntegersMap T ℓ h) ∧
      spIntegersMap T ℓ h ≫ padicIntegersToPadicSubfield T ℓ F =
        padicIntegersToPadicSubfield T ℓ E ≫
          coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) T := by
  unfold spIntegersMap
  exact (spIntegersMap_existsUnique T ℓ h).exists.choose_spec

private theorem ellMap_spec (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    spEllReduction T ℓ E n ≫ spEllMap T ℓ h n =
      spIntegersMap T ℓ h ≫ spEllReduction T ℓ F n := by
  unfold spEllMap
  exact (spEllMap_existsUnique T ℓ h n).exists.choose_spec

private theorem integralTwistMap_spec (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    spIntegralTwistMap T ℓ h ≫ (limit.π (spIntegralTwistSystem T ℓ F) (op n)).hom =
      (limit.π (spIntegralTwistSystem T ℓ E) (op n)).hom ≫
        (spEllMap T ℓ h n ⊗ₘ
          𝟙 (Scheme.proEtaleRootsOfUnitySheaf T (ℓ ^ (n + 1)))) := by
  unfold spIntegralTwistMap
  exact (spIntegralTwistMap_existsUnique T ℓ h).exists.choose_spec n

private theorem rationalTwistMap_spec (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    Mod.extendπ (padicIntegersToPadicSubfield T ℓ E) (spIntegralTwist T ℓ E) ≫
        spRationalTwistMap T ℓ h =
      (coefficientMap.{u} (Profinite.padicSubfieldRingObjMap ℓ h) T ⊗ₘ
        spIntegralTwistMap T ℓ h) ≫
          Mod.extendπ (padicIntegersToPadicSubfield T ℓ F) (spIntegralTwist T ℓ F) := by
  unfold spRationalTwistMap
  exact (spRationalTwistMap_existsUnique T ℓ h).exists.choose_spec

private theorem integersMap_unique (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F)
    (z : condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ E.1) T ⟶
      condensedRingObj (Profinite.padicIntegersRingObj.{u} ℓ F.1) T)
    (hz : IsMonHom z)
    (hcomm : z ≫ padicIntegersToPadicSubfield T ℓ F =
      padicIntegersToPadicSubfield T ℓ E ≫
        coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ h) T) :
    z = spIntegersMap T ℓ h :=
  (spIntegersMap_existsUnique T ℓ h).unique ⟨hz, hcomm⟩ (integersMap_spec T ℓ h)

private theorem coefficientExtension_natural
    (A B K L : PointAb.{u})
    [MonObj A] [MonObj B]
    (p : A ⟶ K) (q : B ⟶ L) (t : K ⟶ L)
    (sY : condensedRingObj A Y ⟶ condensedRingObj B Y) [IsMonHom sY]
    (sX : condensedRingObj A X ⟶ condensedRingObj B X)
    (hs : sY ≫ coefficientMap q Y = coefficientMap p Y ≫ coefficientMap t Y)
    (hu : ∀ z : condensedRingObj A X ⟶ condensedRingObj B X,
      IsMonHom z → z ≫ coefficientMap q X = coefficientMap p X ≫ coefficientMap t X →
        z = sX) :
    (upperStar Ab.{u + 1} f).map sY ≫ condensedPullbackHom B f =
      condensedPullbackHom A f ≫ sX := by
  exact uniqueMonExtension_natural (upperStar Ab.{u + 1} f)
    (condensedPullbackHom A f) (condensedPullbackHom B f)
    (condensedPullbackHom K f) (condensedPullbackHom L f)
    (coefficientMap p Y) (coefficientMap q Y) (coefficientMap p X) (coefficientMap q X)
    sY sX (coefficientMap t Y) (coefficientMap t X)
    (map_coefficientMap_comp_condensedPullbackHom p f)
    (map_coefficientMap_comp_condensedPullbackHom q f)
    (map_coefficientMap_comp_condensedPullbackHom t f) hs hu

private theorem integralCoefficient_natural (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (upperStar AddCommGrpCat.{u + 1} f).map (spIntegersMap Y ℓ h) ≫
        condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ F.1) f =
      condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ E.1) f ≫ spIntegersMap X ℓ h := by
  have : IsMonHom (spIntegersMap Y ℓ h) := (integersMap_spec Y ℓ h).1
  exact coefficientExtension_natural f
    (Profinite.padicIntegersRingObj.{u} ℓ E.1) (Profinite.padicIntegersRingObj.{u} ℓ F.1)
    (Profinite.continuousMapRingObj.{u} E.1) (Profinite.continuousMapRingObj.{u} F.1)
    (padicIntegersRingObjToContinuousMapRingObj ℓ E)
    (padicIntegersRingObjToContinuousMapRingObj ℓ F)
    (Profinite.padicSubfieldRingObjMap.{u} ℓ h)
    (spIntegersMap Y ℓ h) (spIntegersMap X ℓ h)
    (integersMap_spec Y ℓ h).2 (integersMap_unique X ℓ h)

private theorem finiteCoefficient_natural (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) (n : ℕ) :
    (upperStar AddCommGrpCat.{u + 1} f).map (spEllMap Y ℓ h n) ≫
        condensedPullbackHom (spEllPointRingObj.{u} ℓ F n) f =
      condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f ≫ spEllMap X ℓ h n := by
  let U := upperStar AddCommGrpCat.{u + 1} f
  let a := condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f
  let b := condensedPullbackHom (spEllPointRingObj.{u} ℓ F n) f
  let aI := condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ E.1) f
  let bI := condensedPullbackHom (Profinite.padicIntegersRingObj.{u} ℓ F.1) f
  let ψ := inv a ≫ U.map (spEllMap Y ℓ h n) ≫ b
  have hE : U.map (spEllReduction Y ℓ E n) ≫ a = aI ≫ spEllReduction X ℓ E n :=
    map_coefficientMap_comp_condensedPullbackHom _ _
  have hF : U.map (spEllReduction Y ℓ F n) ≫ b = bI ≫ spEllReduction X ℓ F n :=
    map_coefficientMap_comp_condensedPullbackHom _ _
  have hφ := ellMap_spec Y ℓ h n
  have hψ :
      spEllReduction X ℓ E n ≫ ψ = spIntegersMap X ℓ h ≫ spEllReduction X ℓ F n := by
    exact conjugate_precompose U a b aI bI
      (spEllReduction Y ℓ E n) (spEllReduction Y ℓ F n)
      (spEllReduction X ℓ E n) (spEllReduction X ℓ F n)
      (spEllMap Y ℓ h n) (spIntegersMap Y ℓ h) (spIntegersMap X ℓ h)
      hE hF (integralCoefficient_natural f ℓ h) hφ
  have he : ψ = spEllMap X ℓ h n :=
    (spEllMap_existsUnique X ℓ h n).unique hψ
      (ellMap_spec X ℓ h n)
  have hh : a ≫ ψ = U.map (spEllMap Y ℓ h n) ≫ b := by
    dsimp only [ψ]
    rw [IsIso.hom_inv_id_assoc]
  rw [he] at hh
  exact hh.symm

private theorem integral_maps_ext (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ)
    {P : AbSheaf T}
    {a b : P ⟶ (spIntegralTwist T ℓ E).X}
    (h : ∀ n : ℕ, a ≫ (limit.π (spIntegralTwistSystem T ℓ E) (op n)).hom =
      b ≫ (limit.π (spIntegralTwistSystem T ℓ E) (op n)).hom) : a = b := by
  apply (isLimitOfPreserves (Mod.forget _) (limit.isLimit (spIntegralTwistSystem T ℓ E))).hom_ext
  intro j
  exact h j.unop
private theorem integralComparison_natural (ℓ : ℕ) [Fact ℓ.Prime]
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (upperStar AddCommGrpCat.{u + 1} f).map (spIntegralTwistMap Y ℓ h) ≫
        spIntegralComparison f ℓ F =
      spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h := by
  let U := upperStar AddCommGrpCat.{u + 1} f
  apply integral_maps_ext X ℓ F
  intro n
  have hE := integralComparison_π f ℓ E n
  have hF := integralComparison_π f ℓ F n
  dsimp only [integralLevelComparison] at hE hF
  have hY := integralTwistMap_spec Y ℓ h n
  have hX := integralTwistMap_spec X ℓ h n
  exact tensorProjection_natural U
    (spIntegralTwistMap Y ℓ h) (spIntegralTwistMap X ℓ h)
    (spEllMap Y ℓ h n) (spEllMap X ℓ h n)
    (limit.π (spIntegralTwistSystem Y ℓ E) (op n)).hom
    (limit.π (spIntegralTwistSystem Y ℓ F) (op n)).hom
    (limit.π (spIntegralTwistSystem X ℓ E) (op n)).hom
    (limit.π (spIntegralTwistSystem X ℓ F) (op n)).hom
    (spIntegralComparison f ℓ E) (spIntegralComparison f ℓ F)
    (condensedPullbackHom (spEllPointRingObj.{u} ℓ E n) f)
    (condensedPullbackHom (spEllPointRingObj.{u} ℓ F n) f)
    (Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ (n + 1)))
    hE hF hY hX (finiteCoefficient_natural f ℓ h n)
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem rationalComparison_natural (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).obj (spRationalTwist Y ℓ E).X ⟶
        (spRationalTwist X ℓ E).X)
    (hρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).map
        (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫ ρ E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
        (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
          spIntegralComparison f ℓ E) ≫
        Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E))
    {E F : PadicAlgCl.FiniteIntermediateField ℓ} (h : E ≤ F) :
    (upperStar AddCommGrpCat.{u + 1} f).map (spRationalTwistMap Y ℓ h) ≫ ρ F =
      ρ E ≫ spRationalTwistMap X ℓ h := by
  let U := upperStar AddCommGrpCat.{u + 1} f
  let π := Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)
  have : Epi π := inferInstance
  have : Epi (U.map π) := U.map_epi π
  exact tensorQuotient_natural U
    (spIntegralTwistMap Y ℓ h) (spIntegralTwistMap X ℓ h)
    (coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ h) Y)
    (coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ h) X)
    (spRationalTwistMap Y ℓ h) (spRationalTwistMap X ℓ h)
    (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E))
    (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ F) (spIntegralTwist Y ℓ F))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E))
    (Mod.extendπ (padicIntegersToPadicSubfield X ℓ F) (spIntegralTwist X ℓ F))
    (spIntegralComparison f ℓ E) (spIntegralComparison f ℓ F)
    (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f)
    (condensedPullbackHom (Profinite.continuousMapRingObj.{u} F.1) f)
    (ρ E) (ρ F) (hρ E) (hρ F)
    (rationalTwistMap_spec Y ℓ h) (rationalTwistMap_spec X ℓ h)
    (map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjMap.{u} ℓ h) f)
    (integralComparison_natural f ℓ h)

end

private theorem laxAction_stage
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type uJ} [Category.{vJ} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {A R S M N P : C} {A' R' S' M' N' P' : D}
    (b : A ⟶ S) (c : A ⟶ R) (s : M ⟶ N) (j : M ⟶ P) (k : N ⟶ P)
    (b' : A' ⟶ S') (c' : A' ⟶ R') (s' : M' ⟶ N')
    (j' : M' ⟶ P') (k' : N' ⟶ P')
    (act : R ⊗ N ⟶ N) (act' : R' ⊗ N' ⟶ N')
    (big : S ⊗ P ⟶ P) (big' : S' ⊗ P' ⟶ P')
    (a : F.obj A ⟶ A') (r : F.obj R ⟶ R') (z : F.obj S ⟶ S')
    (ρ : F.obj M ⟶ M') (σ : F.obj N ⟶ N') (κ : F.obj P ⟶ P')
    (hY : (b ⊗ₘ j) ≫ big = (c ⊗ₘ s) ≫ act ≫ k)
    (hX : (b' ⊗ₘ j') ≫ big' = (c' ⊗ₘ s') ≫ act' ≫ k')
    (hb : F.map b ≫ z = a ≫ b') (hc : F.map c ≫ r = a ≫ c')
    (hs : F.map s ≫ σ = ρ ≫ s') (hj : F.map j ≫ κ = ρ ≫ j')
    (hk : F.map k ≫ κ = σ ≫ k')
    (hlin : Functor.LaxMonoidal.μ F R N ≫ F.map act ≫ σ = (r ⊗ₘ σ) ≫ act') :
    (F.map b ⊗ₘ F.map j) ≫ (Functor.LaxMonoidal.μ F S P ≫ F.map big ≫ κ) =
      (F.map b ⊗ₘ F.map j) ≫ (z ⊗ₘ κ) ≫ big' := by
  calc
    _ = Functor.LaxMonoidal.μ F A M ≫ F.map ((b ⊗ₘ j) ≫ big) ≫ κ := by
      rw [Functor.LaxMonoidal.μ_natural_assoc, Functor.map_comp, Category.assoc]
    _ = Functor.LaxMonoidal.μ F A M ≫ F.map (c ⊗ₘ s) ≫ F.map act ≫ F.map k ≫ κ := by
      rw [hY]
      simp only [Functor.map_comp, Category.assoc]
    _ = (F.map c ⊗ₘ F.map s) ≫
        (Functor.LaxMonoidal.μ F R N ≫ F.map act ≫ σ) ≫ k' := by
      rw [hk, ← Functor.LaxMonoidal.μ_natural_assoc]
      simp only [Category.assoc]
    _ = (F.map c ⊗ₘ F.map s) ≫ (r ⊗ₘ σ) ≫ act' ≫ k' := by
      rw [hlin]
      simp only [Category.assoc]
    _ = (a ⊗ₘ ρ) ≫ (c' ⊗ₘ s') ≫ act' ≫ k' := by
      simp only [tensorHom_comp_tensorHom_assoc]
      rw [hc, hs]
    _ = (a ⊗ₘ ρ) ≫ (b' ⊗ₘ j') ≫ big' := by rw [hX]
    _ = _ := by
      simp only [tensorHom_comp_tensorHom_assoc]
      rw [hb, hj]

private def semilinearOfEquation
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {D : Type uJ} [Category.{vJ} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.LaxMonoidal]
    {R : C} [MonObj R] {S : D} [MonObj S]
    (a : F.obj R ⟶ S) [IsMonHom a] (M : Mod C R) (N : Mod D S)
    (κ : F.obj M.X ⟶ N.X)
    (h : Functor.LaxMonoidal.μ F R M.X ≫ F.map (Mod.act M.X) ≫ κ =
      (a ⊗ₘ κ) ≫ Mod.act N.X) :
    (F.mapMod R).obj M ⟶ (Mod.comap a).obj N := by
  refine Mod.homMk κ ?_
  change (Functor.LaxMonoidal.μ F R M.X ≫ F.map (Mod.act M.X)) ≫ κ =
    F.obj R ◁ κ ≫ a ▷ N.X ≫ Mod.act N.X
  simpa only [tensorHom_def', Category.assoc] using h

private theorem tensorColimit_ext
    {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
    {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
    {D : I ⥤ C} {E : J ⥤ C} (c : Cocone D) (d : Cocone E)
    (hc : IsColimit c) (hd : IsColimit d)
    [PreservesColimit D (tensorRight d.pt)]
    [∀ i : I, PreservesColimit E (tensorLeft (D.obj i))]
    {Z : C} {a b : c.pt ⊗ d.pt ⟶ Z}
    (h : ∀ (i : I) (j : J), (c.ι.app i ⊗ₘ d.ι.app j) ≫ a =
      (c.ι.app i ⊗ₘ d.ι.app j) ≫ b) : a = b := by
  apply (isColimitOfPreserves (tensorRight d.pt) hc).hom_ext
  intro i
  apply (isColimitOfPreserves (tensorLeft (D.obj i)) hd).hom_ext
  intro j
  change D.obj i ◁ d.ι.app j ≫ (c.ι.app i ▷ d.pt ≫ a) =
    D.obj i ◁ d.ι.app j ≫ (c.ι.app i ▷ d.pt ≫ b)
  simpa only [tensorHom_def', Category.assoc, Functor.const_obj_obj] using h i j
private theorem colimitComparison_exists
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {I : Type uI} [Category.{vI} I] (F : C ⥤ D) (A : I ⥤ C) (B : I ⥤ D)
    [HasColimit A] [HasColimit B] [PreservesColimit A F]
    (α : A ⋙ F ≅ B) :
    ∃ c : F.obj (colimit A) ≅ colimit B, ∀ i : I,
      F.map (colimit.ι A i) ≫ c.hom = α.hom.app i ≫ colimit.ι B i := by
  let c := preservesColimitIso F A ≪≫ HasColimit.isoOfNatIso α
  refine ⟨c, ?_⟩
  intro i
  dsimp only [c]
  rw [Iso.trans_hom, ← Category.assoc, ι_preservesColimitIso_hom,
    HasColimit.ι_isoOfNatIso_hom]

private def ordinaryToSemilinear
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (M : Mod C R) (N : Mod C S)
    (c : (Mod.comap (inv a)).obj M ⟶ N) : M ⟶ (Mod.comap a).obj N :=
  (Mod.comapId R).inv.app M ≫
    (Mod.comapCongr (IsIso.hom_inv_id a)).inv.app M ≫
    (Mod.comapComp a (inv a)).hom.app M ≫ (Mod.comap a).map c

private theorem ordinaryToSemilinear_hom
    {C : Type*} [Category C] [MonoidalCategory C]
    {R S : C} [MonObj R] [MonObj S]
    (a : R ⟶ S) [IsMonHom a] [IsIso a]
    (M : Mod C R) (N : Mod C S)
    (c : (Mod.comap (inv a)).obj M ⟶ N) :
    (ordinaryToSemilinear a M N c).hom = c.hom := by
  change 𝟙 M.X ≫ 𝟙 M.X ≫ 𝟙 M.X ≫ c.hom = c.hom
  simp only [Category.id_comp]

private def internalComparisonSemilinear
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) :
    ((upperStar AddCommGrpCat.{u + 1} f).mapMod (condensedRingObj Λ Y)).obj L ⟶
      (Mod.comap (condensedPullbackHom Λ f)).obj M :=
  ordinaryToSemilinear (condensedPullbackHom Λ f) _ M
    ((Mod.extendScalarsIsoComapInv (condensedPullbackHom Λ f)).inv.app _ ≫ g)

private theorem internalComparisonSemilinear_hom
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) :
    (internalComparisonSemilinear f Λ L M g).hom =
      (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom := by
  rw [internalComparisonSemilinear, ordinaryToSemilinear_hom]
  unfold profinitePointModuleForgetPullbackIso
  rfl

private theorem internalComparison_smul
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) :
    Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act L.X) ≫
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom) =
      (condensedPullbackHom Λ f ⊗ₘ
        ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom)) ≫ Mod.act M.X := by
  have h := Mod.act_hom (internalComparisonSemilinear f Λ L M g)
  change (Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
      (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act L.X)) ≫
        (internalComparisonSemilinear f Λ L M g).hom =
    _ ◁ (internalComparisonSemilinear f Λ L M g).hom ≫
      condensedPullbackHom Λ f ▷ M.X ≫ Mod.act M.X at h
  rw [internalComparisonSemilinear_hom] at h
  simpa only [tensorHom_def', Category.assoc] using h

private theorem internalComparison_smul_normalized
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M)
    (τ₀ : (upperStar Ab.{u + 1} f).obj L.X ⟶ M.X)
    (hτ₀ : (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom = τ₀) :
    Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act L.X) ≫
          τ₀ =
      (condensedPullbackHom Λ f ⊗ₘ
        τ₀) ≫ Mod.act M.X := by
  subst τ₀
  exact internalComparison_smul f Λ L M g

attribute [local irreducible] spRationalTwistMap spIntegralTwistMap spEllMap
  spIntegersMap
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem qbarTwist_smul (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    (E G H : PadicAlgCl.FiniteIntermediateField ℓ) (hE : E ≤ H) (hG : G ≤ H) :
    (coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) T ⊗ₘ
      colimit.ι (spRationalTwistDiagram T ℓ) G) ≫ Mod.act (spQbarTwist T ℓ).X =
    (coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ hE) T ⊗ₘ
      spRationalTwistMap T ℓ hG) ≫ Mod.act (spRationalTwist T ℓ H).X ≫
        colimit.ι (spRationalTwistDiagram T ℓ) H :=
  (spQbarTwistAction_existsUnique T ℓ).exists.choose_spec E G H hE hG

private theorem qbarAction_natural (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).obj (spRationalTwist Y ℓ E).X ⟶
        (spRationalTwist X ℓ E).X)
    (κ : (upperStar AddCommGrpCat.{u + 1} f).obj (spQbarTwist Y ℓ).X ⟶
      (spQbarTwist X ℓ).X)
    (hκ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).map
        (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ κ =
      ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E)
    (hρ : ∀ (E G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ G),
      (upperStar AddCommGrpCat.{u + 1} f).map (spRationalTwistMap Y ℓ h) ≫ ρ G =
        ρ E ≫ spRationalTwistMap X ℓ h)
    (hlin : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act (spRationalTwist Y ℓ E).X) ≫ ρ E =
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ ρ E) ≫
        Mod.act (spRationalTwist X ℓ E).X) :
    Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
      (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act (spQbarTwist Y ℓ).X) ≫ κ =
    (condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) f ⊗ₘ κ) ≫
      Mod.act (spQbarTwist X ℓ).X := by
  have : HasColimit (spRationalTwistDiagram Y ℓ) := inferInstance
  have : HasColimit (spRationalTwistDiagram X ℓ) := inferInstance
  let F := upperStar AddCommGrpCat.{u + 1} f
  let a := condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) f
  apply tensorColimit_ext
    (F.mapCocone (padicAlgClRingObjCocone Y ℓ))
    (F.mapCocone (colimit.cocone (spRationalTwistDiagram Y ℓ)))
    (isColimitOfPreserves F (isColimitPadicAlgClRingObjCocone Y ℓ))
    (isColimitOfPreserves F (colimit.isColimit (spRationalTwistDiagram Y ℓ)))
  intro E G
  obtain ⟨H, hE, hG⟩ := exists_ge_ge E G
  let bY := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) Y
  let bX := coefficientMap (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) X
  let cY := coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ hE) Y
  let cX := coefficientMap (Profinite.padicSubfieldRingObjMap.{u} ℓ hE) X
  let iY (L : PadicAlgCl.FiniteIntermediateField ℓ) :
      (spRationalTwist Y ℓ L).X ⟶ (spQbarTwist Y ℓ).X :=
    colimit.ι (spRationalTwistDiagram Y ℓ) L
  let iX (L : PadicAlgCl.FiniteIntermediateField ℓ) :
      (spRationalTwist X ℓ L).X ⟶ (spQbarTwist X ℓ).X :=
    colimit.ι (spRationalTwistDiagram X ℓ) L
  have hY := qbarTwist_smul Y ℓ E G H hE hG
  have hX := qbarTwist_smul X ℓ E G H hE hG
  change (bY ⊗ₘ iY G) ≫ Mod.act (spQbarTwist Y ℓ).X =
    (cY ⊗ₘ spRationalTwistMap Y ℓ hG) ≫
      Mod.act (spRationalTwist Y ℓ H).X ≫ iY H at hY
  change (bX ⊗ₘ iX G) ≫ Mod.act (spQbarTwist X ℓ).X =
    (cX ⊗ₘ spRationalTwistMap X ℓ hG) ≫
      Mod.act (spRationalTwist X ℓ H).X ≫ iX H at hX
  change (F.map bY ⊗ₘ F.map (iY G)) ≫
      (Functor.LaxMonoidal.μ F _ _ ≫ F.map (Mod.act (spQbarTwist Y ℓ).X) ≫ κ) =
    (F.map bY ⊗ₘ F.map (iY G)) ≫ ((a ⊗ₘ κ) ≫ Mod.act (spQbarTwist X ℓ).X)
  exact laxAction_stage F bY cY (spRationalTwistMap Y ℓ hG) (iY G) (iY H)
    bX cX (spRationalTwistMap X ℓ hG) (iX G) (iX H)
    (Mod.act (spRationalTwist Y ℓ H).X) (Mod.act (spRationalTwist X ℓ H).X)
    (Mod.act (spQbarTwist Y ℓ).X) (Mod.act (spQbarTwist X ℓ).X)
    (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f)
    (condensedPullbackHom (Profinite.continuousMapRingObj.{u} H.1) f)
    a (ρ G) (ρ H) κ hY hX
    (map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjToPadicAlgCl.{u} ℓ E) f)
    (map_coefficientMap_comp_condensedPullbackHom
      (Profinite.padicSubfieldRingObjMap.{u} ℓ hE) f)
    (hρ G H hG) (hκ G) (hκ H) (hlin H)

private theorem qbarComparisonSemilinear_exists (ℓ : ℕ) [Fact ℓ.Prime]
    (ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).obj (spRationalTwist Y ℓ E).X ⟶
        (spRationalTwist X ℓ E).X)
    (κ : (upperStar AddCommGrpCat.{u + 1} f).obj (spQbarTwist Y ℓ).X ⟶
      (spQbarTwist X ℓ).X)
    (hκ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (upperStar AddCommGrpCat.{u + 1} f).map
        (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ κ =
      ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E)
    (hρ : ∀ (E G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ G),
      (upperStar AddCommGrpCat.{u + 1} f).map (spRationalTwistMap Y ℓ h) ≫ ρ G =
        ρ E ≫ spRationalTwistMap X ℓ h)
    (hlin : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      Functor.LaxMonoidal.μ (upperStar AddCommGrpCat.{u + 1} f) _ _ ≫
        (upperStar AddCommGrpCat.{u + 1} f).map (Mod.act (spRationalTwist Y ℓ E).X) ≫ ρ E =
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ ρ E) ≫
        Mod.act (spRationalTwist X ℓ E).X) :
    ∃ c : ((upperStar AddCommGrpCat.{u + 1} f).mapMod
      (condensedRingObj (Profinite.padicAlgClRingObj.{u} ℓ) Y)).obj (spQbarTwist Y ℓ) ⟶
      (Mod.comap (condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) f)).obj
        (spQbarTwist X ℓ), c.hom = κ := by
  refine ⟨semilinearOfEquation (upperStar AddCommGrpCat.{u + 1} f)
    (condensedPullbackHom (Profinite.padicAlgClRingObj.{u} ℓ) f)
    (spQbarTwist Y ℓ) (spQbarTwist X ℓ) κ
    (qbarAction_natural f ℓ ρ κ hκ hρ hlin), rfl⟩

section
variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
private abbrev sectionRing' (T : Scheme.{u}) :=
  InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
    (Scheme.ProEt.topology T) (condensedRingObj Λ T)
private abbrev actualPush := Scheme.proEtaleRingModuleDirectImage f
  (sectionRing' Λ Y) (sectionRing' Λ X) (spCoefficientIso f Λ)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CondensedRing.upperStarLowerStarAdjunction
  InternalModuleOperations.lowerComparison InternalModuleOperations.coefficientMap
private theorem coefficientRingMap_eq :
    InternalModuleOperations.coefficientMap Λ f =
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
          (Scheme.proEtaleRingDirectImageMap f _ _ (spCoefficientIso f Λ)) := by
  ext V r
  have h₁ : ((InternalModuleOperations.coefficientMap Λ f).hom.app V).hom r =
      ((condensedPushforwardHom Λ f).hom.app V).hom r := by
    unfold InternalModuleOperations.coefficientMap
    exact (InternalModuleOperations.coefficientMap_existsUnique Λ f).exists.choose_spec V r
  exact h₁.trans (coefficientIso_adjunct f Λ V r).symm

private def pushBridge :
    (InternalModuleOperations.equivalence Λ X).functor ⋙
      InternalModuleOperations.lowerStar Λ f ≅
    (InternalModuleOperations.equivalence Λ X).functor ⋙ actualPush f Λ :=
  Functor.isoWhiskerLeft _ (SheafOfModules.pushforwardCongr (coefficientRingMap_eq f Λ))

private theorem pushBridge_apply
    (M : ModSheaf X
      (condensedRingObj Λ X)) (V : Y.ProEtᵒᵖ)
    (x : M.X.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V)) :
    ((pushBridge f Λ).hom.app M).val.app V x = x := by
  simp only [pushBridge, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app]
  rfl

private theorem lowerComparison_apply
    (M : ModSheaf X
      (condensedRingObj Λ X)) (V : Y.ProEtᵒᵖ)
    (x : M.X.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V)) :
    ((InternalModuleOperations.lowerComparison Λ f).hom.app M).val.app V x = x := by
  unfold InternalModuleOperations.lowerComparison
  exact (InternalModuleOperations.lowerComparison_existsUnique Λ f).exists.choose_spec M V x

private theorem internalIso_lift
    (L : ModSheaf Y
      (condensedRingObj Λ Y))
    (M : ModSheaf X
      (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) [IsIso g] :
    ∃ c : (Scheme.proEtaleRingModulePullback f
        (sectionRing' Λ Y) (sectionRing' Λ X) (spCoefficientIso f Λ)).obj
          ((InternalModuleOperations.equivalence Λ Y).functor.obj L) ≅
        (InternalModuleOperations.equivalence Λ X).functor.obj M,
      ∀ (V : Y.ProEtᵒᵖ) (m : L.X.obj.obj V),
        (((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _)
          c.hom).val.app V m =
        (((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _)
          ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom)).hom.app V m := by
  let lc := InternalModuleOperations.lowerComparison Λ f ≪≫ pushBridge f Λ
  have hlc (N : ModSheaf X
      (condensedRingObj Λ X)) (V : Y.ProEtᵒᵖ)
      (x : N.X.obj.obj ((Scheme.proEtaleBaseChange f).op.obj V)) :
      (lc.hom.app N).val.app V x = x := by
    simp only [lc, Iso.trans_hom, NatTrans.comp_app, SheafOfModules.comp_val,
      PresheafOfModules.comp_app, ModuleCat.comp_apply, lowerComparison_apply]
    exact pushBridge_apply f Λ N V _
  -- Only its identity formula on sections is needed below.
  clear_value lc
  obtain ⟨j, _, _, hj, _, _⟩ := exists_equivalenceAdjunctionComparison
    (InternalModuleOperations.equivalence Λ Y) (InternalModuleOperations.equivalence Λ X)
    (CondensedRing.upperStarLowerStarAdjunction Λ f)
    (Scheme.proEtaleRingModuleAdjunction f (sectionRing' Λ Y) (sectionRing' Λ X)
      (spCoefficientIso f Λ)) lc
  let c := (j.app L).symm ≪≫
    (InternalModuleOperations.equivalence Λ X).functor.mapIso (asIso g)
  have hh := hj L M g
  change ((Scheme.proEtaleRingModuleAdjunction f _ _ _).homEquiv _ _) c.hom = _ at hh
  clear_value c
  refine ⟨c, ?_⟩
  intro V m
  have h₁ := congrArg (fun k ↦ k.val.app V m) hh
  have h₂ : (lc.hom.app M).val.app V
      (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv L M g).hom.hom.app V m) =
        (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv L M g).hom.hom.app V m) := by
    exact hlc M V _
  change _ = (lc.hom.app M).val.app V
    (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv L M g).hom.hom.app V m) at h₁
  rw [h₂] at h₁
  refine h₁.trans ?_
  have hu := moduleUnit_forget_inv Λ f L
  have he : (((CondensedRing.upperStarLowerStarAdjunction Λ f).homEquiv L M g).hom) =
      ((Scheme.proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv _ _)
        ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom) := by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    change (((CondensedRing.upperStarLowerStarAdjunction Λ f).unit.app L).hom ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map g.hom) = _
    rw [Functor.map_comp, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ (lowerStar AddCommGrpCat.{u + 1} f).map g.hom) hu.symm
  exact congrArg (fun k ↦ k.hom.app V m) he

end

private theorem ordinaryComparison_isIso
    (Λ : PointAb.{u}) [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ≅ M)
    (τ₀ : (upperStar Ab.{u + 1} f).obj L.X ⟶ M.X)
    (hτ₀ : (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom.hom = τ₀) :
    IsIso τ₀ := by
  subst τ₀
  have hp : IsIso ((profinitePointModuleForgetPullbackIso Λ f).inv.app L) :=
    ((profinitePointModuleForgetPullbackIso Λ f).app L).isIso_inv
  have hg : IsIso g.hom.hom := by
    change IsIso ((Mod.forget (condensedRingObj Λ X)).map g.hom)
    infer_instance
  exact IsIso.comp_isIso' hp hg

private theorem internalCartesian_of_iso
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) [IsIso g]
    (hL : ∃ (I : Type (u + 1)) (V : I → Y.ProEt),
      (Scheme.ProEt.topology Y).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence Λ Y).functor.obj L).over
        (V i) ≅ SheafOfModules.unit ((Scheme.purTwistRing Y (sectionRing' Λ Y)).over
          (V i))))
    (hM : ∃ (I : Type (u + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence Λ X).functor.obj M).over
        (V i) ≅ SheafOfModules.unit ((Scheme.purTwistRing X (sectionRing' Λ X)).over
          (V i)))) :
    SpInternalCartesian f Λ L M
      ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom) := by
  obtain ⟨c, hc⟩ := internalIso_lift f Λ L M g
  obtain ⟨β, hβ⟩ := signedComparison_exists f (sectionRing' Λ Y) (sectionRing' Λ X)
    (spCoefficientIso f Λ) _ _ c hL hM
  refine ⟨?_, β, ?_⟩
  · exact ordinaryComparison_isIso f Λ L M (asIso g)
      ((profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom) rfl
  · intro V m
    rw [hβ]
    exact hc V m

private theorem internalCartesian_of_iso_normalized
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf Y (condensedRingObj Λ Y))
    (M : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj L ⟶ M) [IsIso g]
    (τ₀ : (upperStar Ab.{u + 1} f).obj L.X ⟶ M.X)
    (hτ₀ : (profinitePointModuleForgetPullbackIso Λ f).inv.app L ≫ g.hom = τ₀)
    (hL : ∃ (I : Type (u + 1)) (V : I → Y.ProEt),
      (Scheme.ProEt.topology Y).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence Λ Y).functor.obj L).over
        (V i) ≅ SheafOfModules.unit ((Scheme.purTwistRing Y (sectionRing' Λ Y)).over
          (V i))))
    (hM : ∃ (I : Type (u + 1)) (V : I → X.ProEt),
      (Scheme.ProEt.topology X).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence Λ X).functor.obj M).over
        (V i) ≅ SheafOfModules.unit ((Scheme.purTwistRing X (sectionRing' Λ X)).over
          (V i)))) :
    SpInternalCartesian f Λ L M τ₀ := by
  subst τ₀
  exact internalCartesian_of_iso f Λ L M g hL hM

private theorem extendedComparison_iso_exists_normalized
    (Λ A : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ] [MonObj A] [IsCommMonObj A]
    (φ : Λ ⟶ A) [IsMonHom φ]
    (M : ModSheaf Y (condensedRingObj Λ Y))
    (N : ModSheaf X (condensedRingObj Λ X))
    (g : (CondensedRing.upperStar Λ f).obj M ⟶ N) [IsIso g]
    (τ₀ : (upperStar Ab.{u + 1} f).obj M.X ⟶ N.X)
    (hτ₀ : (profinitePointModuleForgetPullbackIso Λ f).inv.app M ≫ g.hom = τ₀) :
    ∃ e : (CondensedRing.upperStar A f).obj
        ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≅
      (Mod.extendScalars (coefficientMap φ X)).obj N,
      (upperStar Ab.{u + 1} f).map (Mod.extendπ (coefficientMap φ Y) M) ≫
        ((profinitePointModuleForgetPullbackIso A f).inv.app
          ((Mod.extendScalars (coefficientMap φ Y)).obj M) ≫ e.hom.hom) =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f) (condensedRingObj A Y) M.X ≫
        (condensedPullbackHom A f ⊗ₘ τ₀) ≫
        Mod.extendπ (coefficientMap φ X) N := by
  subst τ₀
  exact extendedComparison_iso_exists f Λ A φ M N g

attribute [local irreducible] SpInternalCartesian

private theorem signedCover_to_lineCover (T : Scheme.{u})
    (Λ : PointAb.{u})
    [MonObj Λ] [IsCommMonObj Λ]
    (L : ModSheaf T (condensedRingObj Λ T))
    (h : ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty ((spSignedTwist T _ L 1).over (V i) ≅
        (spSignedTwist T _ L 0).over (V i))) :
    ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence Λ T).functor.obj L).over
        (V i) ≅ SheafOfModules.unit ((Scheme.purTwistRing T (sectionRing' Λ T)).over
          (V i))) := by
  exact h

private theorem integralLine_commonCover (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence
        (Profinite.padicIntegersRingObj.{u} ℓ E.1) T).functor.obj
          (spIntegralTwist T ℓ E)).over (V i) ≅
          SheafOfModules.unit ((Scheme.purTwistRing T
            (sectionRing' (Profinite.padicIntegersRingObj.{u} ℓ E.1) T)).over (V i))) := by
  apply signedCover_to_lineCover T (Profinite.padicIntegersRingObj.{u} ℓ E.1)
    (spIntegralTwist T ℓ E)
  obtain ⟨I, V, v, ζ, e, hc, _, _, _, hi, _⟩ := spTwists_commonCover T ℓ
  exact ⟨I, V, commonCover_coversTop T V v hc, fun i ↦ (hi E i).1⟩

private theorem rationalLine_commonCover (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence
        (Profinite.continuousMapRingObj.{u} E.1) T).functor.obj
          (spRationalTwist T ℓ E)).over (V i) ≅
          SheafOfModules.unit ((Scheme.purTwistRing T
            (sectionRing' (Profinite.continuousMapRingObj.{u} E.1) T)).over (V i))) := by
  apply signedCover_to_lineCover T (Profinite.continuousMapRingObj.{u} E.1) (spRationalTwist T ℓ E)
  obtain ⟨I, V, v, ζ, e, hc, _, _, _, hi, _⟩ := spTwists_commonCover T ℓ
  exact ⟨I, V, commonCover_coversTop T V v hc, fun i ↦ (hi E i).2⟩

private theorem qbarLine_commonCover (T : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : T, Invertible (ℓ : T.residueField x)] :
    ∃ (I : Type (u + 1)) (V : I → T.ProEt),
      (Scheme.ProEt.topology T).CoversTop V ∧
      ∀ i, Nonempty (((InternalModuleOperations.equivalence
        (Profinite.padicAlgClRingObj.{u} ℓ) T).functor.obj (spQbarTwist T ℓ)).over (V i) ≅
          SheafOfModules.unit ((Scheme.purTwistRing T
            (sectionRing' (Profinite.padicAlgClRingObj.{u} ℓ) T)).over (V i))) := by
  apply signedCover_to_lineCover T (Profinite.padicAlgClRingObj.{u} ℓ) (spQbarTwist T ℓ)
  obtain ⟨I, V, v, ζ, e, hc, _, _, _, _, hi⟩ := spTwists_commonCover T ℓ
  exact ⟨I, V, commonCover_coversTop T V v hc, hi⟩

-- Keep the native inverse-limit construction abstract when applying scalar extension.
attribute [local irreducible] spIntegralTwist
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem nativeRationalComparison_iso_exists
    (ℓ : ℕ) [Fact ℓ.Prime] (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (gI : (CondensedRing.upperStar (Profinite.padicIntegersRingObj.{u} ℓ E.1) f).obj
      (spIntegralTwist Y ℓ E) ≅ spIntegralTwist X ℓ E)
    (hgI : (profinitePointModuleForgetPullbackIso
      (Profinite.padicIntegersRingObj.{u} ℓ E.1) f).inv.app (spIntegralTwist Y ℓ E) ≫
        gI.hom.hom = spIntegralComparison f ℓ E) :
      ∃ g : (CondensedRing.upperStar (Profinite.continuousMapRingObj.{u} E.1) f).obj
          (spRationalTwist Y ℓ E) ≅ spRationalTwist X ℓ E,
        (upperStar AddCommGrpCat.{u + 1} f).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫
          ((profinitePointModuleForgetPullbackIso
            (Profinite.continuousMapRingObj.{u} E.1) f).inv.app
              (spRationalTwist Y ℓ E) ≫ g.hom.hom) =
          Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
            (spIntegralTwist Y ℓ E).X ≫
            (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
              spIntegralComparison f ℓ E) ≫
            Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) := by
  exact extendedComparison_iso_exists_normalized f
      (Profinite.padicIntegersRingObj.{u} ℓ E.1)
      (Profinite.continuousMapRingObj.{u} E.1)
      (padicIntegersRingObjToContinuousMapRingObj ℓ E)
      (spIntegralTwist Y ℓ E) (spIntegralTwist X ℓ E)
      gI.hom (spIntegralComparison f ℓ E) hgI

-- Use only the comparison APIs for these module objects below.
set_option backward.defeqAttrib.useBackward false

attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence
  InternalAbelianSheafModule.sectionRingSheaf
  Scheme.proEtaleRingModulePullback Scheme.proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

/-- Inverse image of all non-finite coefficient twists, including integral and rational
Q_ell as the bottom finite subextension, and the algebraic-closure sheafified colimit.
Together with spRoots_cartesian and spFiniteTwists_cartesian this states every
coefficient case in the source. Source: blueprint Inverse image of Tate twists,
Integral twist, Rational and algebraically closed coefficients, Powers and duals,
and Derived consequence paragraphs
(blueprint: lemma-inverse-image-coefficient-sheaves--2).
Proof:
1. The separate native integral tower lemma says that inverse image preserves its
   displayed limiting cone. The finite component comparisons are isomorphisms by
   the root comparison and alpha. Uniqueness of maps between limiting cones makes
   the projection-normalized integral comparison invertible.
2. The integral residue tensor square lifts that abelian comparison to the ordinary
   coefficient-module pullback. Scalar extension to E preserves its invertibility.
   Its quotient-map normalization is the required rational normalization.
3. Conjugate each coefficient inclusion by alpha. Its normalized composite into the
   field coefficients determines it uniquely, giving integral coefficient naturality.
   The quotient normalizations then give finite coefficient naturality. Projection
   extensionality and the scalar-extension quotient give integral and rational twist
   naturality, respectively.
4. Inverse image preserves the filtered colimit over finite subextensions. The
   preceding rational naturality supplies its comparison isomorphism and fixes every
   coprojection. To check semilinearity, test on a coefficient coprojection and a
   module coprojection, choose a common upper finite field, and use the specified
   finite-stage action there. This uses the finite-subextension condensed Qbar ring.
5. Transport each ordinary internal-module isomorphism to sectionwise modules. The
   coefficient and adjunction-unit normalizations identify its abelian adjunct
   exactly, so the prescribed first comparison is retained.
6. The common root cover makes each finite, integral, rational and Qbar line locally
   free of rank one. The signed-line derived base-change theorem then gives all
   signed degrees with their unit, tensor and evaluation normalizations. Uniqueness
   of left adjoints transports its unit formulas to the actual pullback, and the
   induced natural isomorphism on unbounded derived categories gives the derived
   comparison. No boundedness or finite-Tor condition is needed.
7. Naturality of the root inverse-image map gives the last transition formula. -/
theorem spTwists_cartesian (ℓ : ℕ) [Fact ℓ.Prime]
    [∀ x : X, Invertible (ℓ : X.residueField x)]
    [∀ y : Y, Invertible (ℓ : Y.residueField y)] :
    ∃ (ρ : ∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
        (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spRationalTwist.{u} Y ℓ E).X ⟶ (spRationalTwist.{u} X ℓ E).X)
      (κ : (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).obj
          (spQbarTwist.{u} Y ℓ).X ⟶ (spQbarTwist.{u} X ℓ).X),
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist.{u} Y ℓ E)) ≫
        ρ E =
      Functor.OplaxMonoidal.δ (upperStar AddCommGrpCat.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist.{u} Y ℓ E).X ≫
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
        spIntegralComparison f ℓ E) ≫
      Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist.{u} X ℓ E)) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫ κ =
        ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E) ∧
    (∀ E : PadicAlgCl.FiniteIntermediateField ℓ,
      SpInternalCartesian f (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist.{u} Y ℓ E) (spIntegralTwist.{u} X ℓ E) (spIntegralComparison f ℓ E) ∧
      SpInternalCartesian f (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist.{u} Y ℓ E) (spRationalTwist.{u} X ℓ E) (ρ E)) ∧
    SpInternalCartesian f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist.{u} Y ℓ) (spQbarTwist.{u} X ℓ) κ ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spIntegralTwistMap Y ℓ h) ≫ spIntegralComparison f ℓ F =
        spIntegralComparison f ℓ E ≫ spIntegralTwistMap X ℓ h) ∧
    (∀ (E F : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ F),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
          (spRationalTwistMap Y ℓ h) ≫ ρ F =
        ρ E ≫ spRationalTwistMap X ℓ h) ∧
    (∀ (n m : ℕ) (h : n ≤ m),
      (Scheme.proEtaleSheafInverseImage f AddCommGrpCat.{u + 1}).map
        (Scheme.proEtaleRootsOfUnityTransition Y (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) ≫ Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ n) =
      Scheme.proEtaleRootsOfUnityInverseImageMap f (ℓ ^ m) ≫
        Scheme.proEtaleRootsOfUnityTransition X (ℓ ^ n) (ℓ ^ m)
          (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
          (pow_dvd_pow ℓ h)) := by
  classical
  have hI (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      IsIso (spIntegralComparison f ℓ E) := by
    exact nativeIntegralComparison_isIso f ℓ E
  have hiE (E : PadicAlgCl.FiniteIntermediateField ℓ) := by
    have := hI E
    exact ordinaryIntegralComparison_iso_exists f ℓ E
  choose gI hgI using hiE
  have hrE (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    nativeRationalComparison_iso_exists f ℓ E (gI E) (hgI E)
  choose gR hgR using hrE
  let ρ (E : PadicAlgCl.FiniteIntermediateField ℓ) :=
    (profinitePointModuleForgetPullbackIso
      (Profinite.continuousMapRingObj.{u} E.1) f).inv.app (spRationalTwist Y ℓ E) ≫
        (gR E).hom.hom
  have hρdef (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (profinitePointModuleForgetPullbackIso
        (Profinite.continuousMapRingObj.{u} E.1) f).inv.app (spRationalTwist Y ℓ E) ≫
          (gR E).hom.hom = ρ E := rfl
  -- Retain the equation without repeatedly unfolding the scalar-extension object.
  clear_value ρ
  have hρ (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStar Ab.{u + 1} f).map
          (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫
        ρ E =
      Functor.OplaxMonoidal.δ (upperStar Ab.{u + 1} f)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} E.1) Y)
        (spIntegralTwist Y ℓ E).X ≫
        (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ
          spIntegralComparison f ℓ E) ≫
        Mod.extendπ (padicIntegersToPadicSubfield X ℓ E) (spIntegralTwist X ℓ E) := by
    exact (congrArg (fun k ↦ (upperStar Ab.{u + 1} f).map
      (Mod.extendπ (padicIntegersToPadicSubfield Y ℓ E) (spIntegralTwist Y ℓ E)) ≫ k)
      (hρdef E).symm).trans (hgR E)
  have hnρ (E G : PadicAlgCl.FiniteIntermediateField ℓ) (h : E ≤ G) :
      (upperStar AddCommGrpCat.{u + 1} f).map (spRationalTwistMap Y ℓ h) ≫ ρ G =
        ρ E ≫ spRationalTwistMap X ℓ h :=
    rationalComparison_natural f ℓ ρ hρ h
  have hρiso (E : PadicAlgCl.FiniteIntermediateField ℓ) : IsIso (ρ E) :=
    ordinaryComparison_isIso f (Profinite.continuousMapRingObj.{u} E.1)
      (spRationalTwist Y ℓ E) (spRationalTwist X ℓ E) (gR E) (ρ E) (hρdef E)
  let aρ : spRationalTwistDiagram Y ℓ ⋙ upperStar AddCommGrpCat.{u + 1} f ≅
      spRationalTwistDiagram X ℓ :=
    NatIso.ofComponents (fun E ↦ @asIso _ _ _ _ (ρ E) (hρiso E))
        (fun g ↦ hnρ _ _ (leOfHom g))
  have haρ (E : PadicAlgCl.FiniteIntermediateField ℓ) : (aρ.hom.app E) = ρ E := rfl
  clear_value aρ
  obtain ⟨κ, hκ'⟩ := colimitComparison_exists
    (upperStar AddCommGrpCat.{u + 1} f)
    (spRationalTwistDiagram Y ℓ) (spRationalTwistDiagram X ℓ) aρ
  have hκ (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      (upperStar Ab.{u + 1} f).map (colimit.ι (spRationalTwistDiagram Y ℓ) E) ≫
        κ.hom = ρ E ≫ colimit.ι (spRationalTwistDiagram X ℓ) E := by
    rw [← haρ E]
    exact hκ' E
  have hlin (E : PadicAlgCl.FiniteIntermediateField ℓ) :
      Functor.LaxMonoidal.μ (upperStar Ab.{u + 1} f) _ _ ≫
        (upperStar Ab.{u + 1} f).map (Mod.act (spRationalTwist Y ℓ E).X) ≫ ρ E =
      (condensedPullbackHom (Profinite.continuousMapRingObj.{u} E.1) f ⊗ₘ ρ E) ≫
        Mod.act (spRationalTwist X ℓ E).X := by
    exact internalComparison_smul_normalized f (Profinite.continuousMapRingObj.{u} E.1)
      (spRationalTwist Y ℓ E) (spRationalTwist X ℓ E) (gR E).hom (ρ E) (hρdef E)
  obtain ⟨cκ, hcκ⟩ := qbarComparisonSemilinear_exists f ℓ ρ κ.hom hκ hnρ hlin
  have : IsIso cκ.hom := by
    rw [hcκ]
    exact κ.isIso_hom
  obtain ⟨gκ, hgκ'⟩ := ordinaryLift_iso f (Profinite.padicAlgClRingObj.{u} ℓ)
    (spQbarTwist Y ℓ) (spQbarTwist X ℓ) cκ
  have hgκ : (profinitePointModuleForgetPullbackIso
      (Profinite.padicAlgClRingObj.{u} ℓ) f).inv.app (spQbarTwist Y ℓ) ≫
        gκ.hom.hom = κ.hom := hgκ'.trans hcκ
  refine ⟨ρ, κ.hom, hρ, hκ, ?_, ?_, ?_, hnρ, ?_⟩
  · intro E
    have := hI E
    constructor
    · exact internalCartesian_of_iso_normalized f
        (Profinite.padicIntegersRingObj.{u} ℓ E.1)
        (spIntegralTwist Y ℓ E) (spIntegralTwist X ℓ E) (gI E).hom
        (spIntegralComparison f ℓ E) (hgI E)
        (integralLine_commonCover Y ℓ E) (integralLine_commonCover X ℓ E)
    · exact internalCartesian_of_iso_normalized f
        (Profinite.continuousMapRingObj.{u} E.1)
        (spRationalTwist Y ℓ E) (spRationalTwist X ℓ E) (gR E).hom (ρ E) (hρdef E)
        (rationalLine_commonCover Y ℓ E) (rationalLine_commonCover X ℓ E)
  · exact internalCartesian_of_iso_normalized f (Profinite.padicAlgClRingObj.{u} ℓ)
      (spQbarTwist Y ℓ) (spQbarTwist X ℓ) gκ.hom κ.hom hgκ
      (qbarLine_commonCover Y ℓ) (qbarLine_commonCover X ℓ)
  · intro E G h
    exact integralComparison_natural f ℓ h
  · intro n m h
    exact Scheme.roots_inverse_transition f (ℓ ^ n) (ℓ ^ m)
      (pow_pos (Fact.out : ℓ.Prime).pos _) (pow_pos (Fact.out : ℓ.Prime).pos _)
      (pow_dvd_pow ℓ h)

end AlgebraicGeometry.ProEtale

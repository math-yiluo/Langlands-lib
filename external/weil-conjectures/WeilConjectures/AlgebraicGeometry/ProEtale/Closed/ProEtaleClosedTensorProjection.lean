/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import all WeilConjectures.SixFunctors.CoefficientClosedStructure.ClosedTensorDualAdjunction
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalTensorPullback
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedDetection
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.Algebra.Homology.RingedDerivedTensorHomAdjunction
import WeilConjectures.Algebra.Homology.Ringed.RingedDerivedTensorNativeSupplement
import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
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
import WeilConjectures.Algebra.Homology.HomComplex
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseIso
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.SecSmoothPurity.CochainTensoratorExistence
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainInverseComparison
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import WeilConjectures.Algebra.Homology.InternalHom
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.Algebra.Homology.HomotopyCategory.InternalHom
import WeilConjectures.SecSmoothPurity.ModuleTensorGenerators
import WeilConjectures.SecSmoothPurity.CochainCoefficientArrowsSupplement
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

/-! # The closed-support projection formula

## References

* Stacks Tags 03EL, 07A4 and 09BM
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits WeilConjectures
namespace AlgebraicGeometry.Scheme

private def nativeModel (X : Scheme.{u})
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) : ProEtaleTensorModel X R where
  tensor := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology X) R)
  representative := NatIso.ofComponents
    (fun P ↦ RingedDerivedNative.tensorIso.{u + 1, u, 0, u + 2}
      (ProEt.topology X) R P.1.obj P.2.obj (Or.inl P.1.property.1))
    (fun f ↦ RingedDerivedNative.tensorIso_naturality.{u + 1, u, 0, u + 2}
      (ProEt.topology X) R _ _ _ _ _ _ f.1.hom f.2.hom)

private theorem nativePullTensor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    let S := (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R
    let p := proEtaleRingDerivedPullback f R S (Iso.refl _)
    Nonempty ((nativeModel Y R).tensor ⋙ p ≅ p.prod p ⋙ (nativeModel X S).tensor) := by
  dsimp only
  obtain ⟨a, _ha, _uniq⟩ := (proEtaleCanonicalTensorPullback f R _ (Iso.refl _)
    (nativeModel Y R) (nativeModel X _)).2
  exact ⟨a⟩

private theorem push_eq {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModuleDirectImage f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) =
      proEtaleRingedDirectImage f R := by
  have hm : proEtaleRingDirectImageMap f R
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) =
        (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R := by
    unfold proEtaleRingDirectImageMap
    change _ ≫ (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map (𝟙 _) = _
    rw [(proEtaleSheafDirectImage f CommRingCat.{u + 1}).map_id, Category.comp_id]
  simp only [proEtaleRingModuleDirectImage, hm, proEtaleRingedDirectImage,
    proEtaleModuleCoefficients]

private def inverseIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1}) :
    proEtaleRingModulePullback f R
        ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R) (Iso.refl _) ≅
      proEtaleModuleInverseImage f R := by
  let a := (proEtaleRingModuleOperations_properties f R _ (Iso.refl _)).2.2.2.2.some
  exact a.leftAdjointUniq ((ringedInverseImageAdjunction f R).ofNatIsoRight
    (eqToIso (push_eq f R)).symm)

private theorem openClosedModuleData
    {X Z U : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (h : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) :
    let Ri := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
    let Rj := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
    let pi := proEtaleRingModulePullback i R Ri (Iso.refl _)
    let qi := proEtaleRingModuleDirectImage i R Ri (Iso.refl _)
    let pj := proEtaleRingModulePullback j R Rj (Iso.refl _)
    PreservesFiniteLimits qi ∧ PreservesFiniteColimits qi ∧
      (∃ a : pi ⊣ qi, IsIso a.counit) ∧
      (∀ N, IsZero (pj.obj (qi.obj N))) ∧
      JointlyReflectIsomorphisms (pairFunctor pi pj) := by
  dsimp only
  let V := ProEt.mk j
  have : IsOpenImmersion V.hom := ‹IsOpenImmersion j›
  have : QuasiCompact V.hom := ‹QuasiCompact j›
  obtain ⟨q, ⟨e⟩, ai, aj, hc, _, hz, _, _, _, hl, hr, _, _⟩ :=
    proEtale_ringed_open_closed i V h R
  have : IsIso ai.counit := NatIso.isIso_of_isIso_app _
  have := ai.fullyFaithfulROfIsIsoCounit.full
  have := ai.fullyFaithfulROfIsIsoCounit.faithful
  have hli : PreservesFiniteLimits (proEtaleRingModuleDirectImage i R _ (Iso.refl _)) := by
    rw [push_eq]; exact hl
  have hri : PreservesFiniteColimits (proEtaleRingModuleDirectImage i R _ (Iso.refl _)) := by
    rw [push_eq]; exact hr
  obtain ⟨a⟩ := (proEtaleRingModuleOperations_properties i R _ (Iso.refl _)).2.2.2.2
  have ha : IsIso a.counit := by
    have : (proEtaleRingModuleDirectImage i R _ (Iso.refl _)).Full := by
      rw [push_eq]; infer_instance
    have : (proEtaleRingModuleDirectImage i R _ (Iso.refl _)).Faithful := by
      rw [push_eq]; infer_instance
    infer_instance
  refine ⟨hli, hri, ⟨a, ha⟩, ?_, ?_⟩
  · intro N
    have h0 : IsZero ((proEtaleModuleInverseImage j R).obj
        ((proEtaleRingedDirectImage i R).obj N)) :=
      IsZero.of_full_of_faithful_of_isZero q.functor _
        ((hz N).of_iso (e.app _))
    exact h0.of_iso
      ((inverseIso j R).app ((proEtaleRingModuleDirectImage i R _ (Iso.refl _)).obj N) ≪≫
        (proEtaleModuleInverseImage j R).mapIso (eqToIso (congrArg (fun F ↦ F.obj N)
          (push_eq i R))))
  · refine jointlyReflectIsomorphisms_pairFunctor _ _ ?_
    intro M N f hi hj
    have hk : IsZero (kernel f) := proEtaleRingModule_isZero_of_open_closed
      i j h R _ _ (Iso.refl _) (Iso.refl _) _
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ f))
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ f))
    have hco : IsZero (cokernel f) := proEtaleRingModule_isZero_of_open_closed
      i j h R _ _ (Iso.refl _) (Iso.refl _) _
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ f))
      ((isZero_cokernel_of_epi _).of_iso (PreservesCokernel.iso _ f))
    have : Mono f := Preadditive.mono_of_isZero_kernel _ hk
    have : Epi f := Preadditive.epi_of_isZero_cokernel _ hco
    exact isIso_of_mono_of_epi f

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

/-- Closed direct image commutes with derived tensor against ambient complexes.
No exceptional functor or dualizing object occurs in this assertion. -/
theorem proEtaleClosedTensorProjection
    {T Z U : Scheme.{u}} (i : Z ⟶ T) [IsClosedImmersion i]
    (j : U ⟶ T) [IsOpenImmersion j] [QuasiCompact j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    (R : Sheaf (ProEt.topology T) CommRingCat.{u + 1}) :
    let RZ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
    let tT := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
    let tZ := @MonoidalCategory.tensor _ _
      (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ)
    Nonempty ((proEtaleRingDerivedDirectImage i R RZ (Iso.refl _)).prod (𝟭 _) ⋙ tT ≅
      (𝟭 _).prod (proEtaleRingDerivedPullback i R RZ (Iso.refl _)) ⋙ tZ ⋙
        proEtaleRingDerivedDirectImage i R RZ (Iso.refl _)) := by
  dsimp only
  let RZ := (proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R
  let RU := (proEtaleSheafInverseImage j CommRingCat.{u + 1}).obj R
  let pi := proEtaleRingModulePullback i R RZ (Iso.refl _)
  let qi := proEtaleRingModuleDirectImage i R RZ (Iso.refl _)
  let pj := proEtaleRingModulePullback j R RU (Iso.refl _)
  obtain ⟨hli, hri, ⟨a, ha⟩, hz, hdet⟩ := openClosedModuleData i j hij R
  have : PreservesFiniteLimits qi := hli
  have : PreservesFiniteColimits qi := hri
  have : IsIso a.counit := ha
  let ad := exactDerivedAdjunction a
  have : ∀ N, IsIso (ad.counit.app N) :=
    fun N ↦ exactDerivedAdjunction_counit_isIso a N
  have : IsIso ad.counit := NatIso.isIso_of_isIso_app _
  have hd := Functor.jointlyReflectIsomorphisms_pairFunctor_mapDerivedCategory pi pj hdet
  have hzd (N : DerivedCategory (proEtaleRingModules Z RZ)) :
      IsZero (pj.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N)) := by
    apply Functor.isZero_mapDerivedCategory_obj
    intro n
    exact (hz ((DerivedCategory.homologyFunctor _ n).obj N)).of_iso
      (pj.mapIso ((qi.mapDerivedCategoryHomologyFunctorIso n).app N)).symm
  obtain ⟨ei⟩ := nativePullTensor i R
  obtain ⟨ej⟩ := nativePullTensor j R
  let tT := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology T) R)
  let tZ := @MonoidalCategory.tensor _ _
    (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology Z) RZ)
  have hu (N : DerivedCategory (proEtaleRingModules Z RZ))
      (K : DerivedCategory (proEtaleRingModules T R)) :
      IsIso (ad.unit.app (tT.obj (qi.mapDerivedCategory.obj N, K))) := by
    apply CategoryTheory.supportedUnit pi.mapDerivedCategory qi.mapDerivedCategory
      pj.mapDerivedCategory ad
      (fun f hi hj ↦ hd.isIso_of_pairFunctor f hi hj) hzd
    let := RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology U) RU
    obtain ⟨⟨m, ac, ev⟩, hm, _, _⟩ :=
      RingedDerivedNative.closedAdjunction.{u + 1, u, 0, u + 2} (ProEt.topology U) RU
    dsimp only [CoefficientClosedStructure.monoidal] at hm
    subst m
    have := (ac (pj.mapDerivedCategory.obj K)).isLeftAdjoint
    have h0 : IsZero
        ((@MonoidalCategory.tensor _ _
          (RingedDerivedNative.monoidal.{u + 1, u, 0, u + 2} (ProEt.topology U) RU)).obj
            (pj.mapDerivedCategory.obj (qi.mapDerivedCategory.obj N),
              pj.mapDerivedCategory.obj K)) :=
      (MonoidalCategory.tensorRight (pj.mapDerivedCategory.obj K)).map_isZero (hzd N)
    exact h0.of_iso (ej.app (qi.mapDerivedCategory.obj N, K))
  obtain ⟨e⟩ := CategoryTheory.projectionOfSupportedUnit
    pi.mapDerivedCategory qi.mapDerivedCategory ad tT tZ ei hu
  let eQ := qi.rightDerivedFunctorIsoMapDerivedCategory
  exact ⟨Functor.isoWhiskerRight (NatIso.prod eQ (Iso.refl (𝟭 _))) tT ≪≫ e ≪≫
    Functor.isoWhiskerLeft ((𝟭 _).prod pi.mapDerivedCategory ⋙ tZ) eQ.symm⟩

end AlgebraicGeometry.Scheme

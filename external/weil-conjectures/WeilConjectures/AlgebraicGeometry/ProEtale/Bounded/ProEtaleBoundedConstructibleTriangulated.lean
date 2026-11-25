/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleExactClosure
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Bounded constructible pro-etale complexes form a triangulated subcategory

## References

* Stacks Project, Tags 09AL, 09B5 and 06UQ
* Stacks Project, Tag 0H7J, uniqueness of the constant-sheaf adjunction
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The canonical constant-coefficient inverse-image comparison is invertible. -/
theorem constantComparison_isIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] : IsIso (proEtaleCoefficientInverseImageMap f A) :=
  proEtaleConstantRingComparison_isIso.{u} f A

private noncomputable def constantModulePullbackFunctor {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A] :
    proEtaleRingModules Y (proEtaleConstantRing Y A) ⥤
      proEtaleRingModules X (proEtaleConstantRing X A) := by
  have := constantComparison_isIso f A
  exact proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))

private theorem pullback_isZero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsZero (proEtaleConstantModulePullback f A F) := by
  have := constantComparison_isIso f A
  exact (proEtaleRingModulePullback f (proEtaleConstantRing Y A) (proEtaleConstantRing X A)
    (asIso (proEtaleCoefficientInverseImageMap f A))).map_isZero hF

private theorem constantPresheaf_zero (C : Type (u + 1)) [Category* C]
    (A : Type u) [CommRing A] :
    IsZero (proEtaleConstantModulePresheaf C A
      ((HasZeroObject.zero
        (C := ModuleCat.{u + 1} (ULift.{u + 1, u} A))).choose)) := by
  rw [IsZero.iff_id_eq_zero]
  apply PresheafOfModules.hom_ext
  intro U
  exact (isZero_zero _).eq_of_src _ _

theorem locallyConstant_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsLocallyConstantProEtaleModuleSheaf Y A F := by
  let : Zero (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) := HasZeroObject.zero' _
  let U : PUnit.{u + 2} → Y.ProEt := fun _ ↦ ProEt.mk (𝟙 Y)
  let a : ∀ i : PUnit.{u + 2}, U i ⟶ ProEt.mk (𝟙 Y) := fun _ ↦ 𝟙 _
  refine ⟨PUnit.{u + 2}, U, a, ?_, fun i ↦ ?_⟩
  · rw [Presieve.ofArrows_of_unique]
    exact Precoverage.mem_coverings_of_isIso (𝟙 (ProEt.mk (𝟙 Y)))
  · refine ⟨0, ⟨?_⟩⟩
    have hz : IsZero (proEtaleConstantModuleSheafOver Y A (U i) 0) := by
      have := (proEtaleConstantRingUnit_over_locallyBijective Y A (U i)).1
      have := (proEtaleConstantRingUnit_over_locallyBijective Y A (U i)).2
      unfold proEtaleConstantModuleSheafOver
      exact (PresheafOfModules.sheafification _).map_isZero (constantPresheaf_zero _ A)
    let E := SheafOfModules.overFunctor
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (proEtaleConstantRing Y A)) (U i)
    have : E.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
    exact (E.map_isZero hF).iso hz

private theorem locallyConstant_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsLocallyConstantProEtaleModuleSheaf Y A F) :
    IsLocallyConstantProEtaleModuleSheaf Y A G := by
  obtain ⟨I, U, f, hc, ht⟩ := hF
  refine ⟨I, U, f, hc, fun i ↦ ?_⟩
  obtain ⟨M, ⟨hM⟩⟩ := ht i
  exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U i)).mapIso e.symm ≪≫ hM⟩⟩

theorem finite_stalk_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y)
    [Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)] :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) G) := by
  let E := geometricRingModuleStalkFunctor y (proEtaleConstantRing Y A)
  have : Finite (E.obj F) :=
    ‹Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F)›
  change Finite (E.obj G)
  exact Finite.of_injective (E.mapIso e.symm).toLinearEquiv
    (E.mapIso e.symm).toLinearEquiv.injective

theorem finite_stalk_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ Y) :
    Finite (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) := by
  have hz := (geometricRingModuleStalkFunctor y (proEtaleConstantRing Y A)).map_isZero hF
  have : Subsingleton (proEtaleGeometricModuleStalk y (proEtaleConstantRing Y A) F) :=
    ModuleCat.subsingleton_of_isZero hz
  infer_instance

/-- The single stratum equal to the whole scheme witnesses constructibility of zero. -/
private theorem constructibleProEtale_of_isZero (Y : Scheme.{u}) (A : Type u)
    [CommRing A] [Finite A] (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsZero F) : IsConstructibleProEtaleModuleSheaf Y A F := by
  let S : Stratification Y :=
    { n := 1
      stratum := fun _ ↦ Set.univ
      isLocallyClosed_stratum := fun _ ↦ IsOpen.isLocallyClosed isOpen_univ
      isConstructible_stratum := fun _ ↦ Topology.IsConstructible.univ
      iUnion_stratum_eq_univ := by
        ext x
        exact ⟨fun _ ↦ Set.mem_univ _, fun _ ↦ Set.mem_iUnion.mpr ⟨0, Set.mem_univ _⟩⟩
      pairwise_disjoint_stratum := fun i j h ↦ (h (Subsingleton.elim i j)).elim
      domain := fun _ ↦ Y
      immersion := fun _ ↦ 𝟙 Y
      range_immersion := fun _ ↦ Set.range_id }
  refine ⟨S, by change 0 < (1 : ℕ); exact Nat.zero_lt_succ 0, fun i ↦ ?_⟩
  have hz := pullback_isZero (S.immersion i) A F hF
  exact ⟨locallyConstant_of_isZero _ A _ hz, fun Ω _ _ y ↦
    finite_stalk_of_isZero _ A _ hz y⟩

/-- Transport a constructibility witness through a module-sheaf isomorphism. -/
private theorem constructibleProEtale_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' : proEtaleConstantModulePullback (S.immersion i) A F ≅
      proEtaleConstantModulePullback (S.immersion i) A G :=
    (constantModulePullbackFunctor (S.immersion i) A).mapIso e
  refine ⟨locallyConstant_of_iso _ A e' (hS i).1, ?_⟩
  intro Ω _ _ y
  have := (hS i).2 Ω y
  exact finite_stalk_of_iso _ A e' y

private theorem finite_homology_support_iff_bounded
    (Y : Scheme.{u}) (A : Type u) [CommRing A] (K : proEtaleDerivedCategory Y A) :
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ↔
      DerivedCategory.TStructure.t.bounded K := by
  rw [Set.finite_iff_bddBelow_bddAbove]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, (DerivedCategory.isGE_iff K a).2 fun i hi ↦ by
      by_contra h
      exact (not_le_of_gt hi) (ha h)⟩,
      ⟨b, (DerivedCategory.isLE_iff K b).2 fun i hi ↦ by
        by_contra h
        exact (not_le_of_gt hi) (hb h)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, fun i hi ↦ le_of_not_gt fun h ↦ hi ((DerivedCategory.isGE_iff K a).1 ha i h)⟩,
      ⟨b, fun i hi ↦ le_of_not_gt fun h ↦ hi ((DerivedCategory.isLE_iff K b).1 hb i h)⟩⟩

/-- Bounded globally constructible cohomology is invariant under isomorphisms and
cuts out a full triangulated subcategory. -/
theorem proEtale_bounded_constructible_isTriangulated
    (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A] :
    ObjectProperty.IsClosedUnderIsomorphisms (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) ∧
    ObjectProperty.IsTriangulated (fun K : proEtaleDerivedCategory Y A ↦
      Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
        ((DerivedCategory.homologyFunctor
          (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)) := by
  let P : ObjectProperty (proEtaleRingModules Y (proEtaleConstantRing Y A)) :=
    IsConstructibleProEtaleModuleSheaf Y A
  let : Zero (proEtaleRingModules Y (proEtaleConstantRing Y A)) := HasZeroObject.zero' _
  obtain ⟨hkc, hext⟩ := constructibleProEtale_exactClosure Y A
  have : P.IsClosedUnderIsomorphisms :=
    ⟨fun e h ↦ constructibleProEtale_of_iso Y A e h⟩
  have : P.ContainsZero :=
    ⟨0, isZero_zero _, constructibleProEtale_of_isZero Y A _ (isZero_zero _)⟩
  have : P.IsClosedUnderKernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((kernelIsKernel f).conePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).1⟩
  have : P.IsClosedUnderCokernels := ⟨by
    rintro _ ⟨f, k, hk, hFG⟩
    exact P.prop_of_iso ((cokernelIsCokernel f).coconePointUniqueUpToIso hk)
      (hkc _ _ f hFG.1 hFG.2).2⟩
  have : P.IsClosedUnderExtensions := ⟨fun hS h1 h3 ↦ hext _ hS h1 h3⟩
  have htri := (cohomology_in_weak_serre_subcategory P).2.2
  let Q : ObjectProperty (proEtaleDerivedCategory Y A) := fun K ↦
    Set.Finite {i : ℤ | ¬ IsZero ((DerivedCategory.homologyFunctor
      (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)} ∧
      ∀ i : ℤ, P ((DerivedCategory.homologyFunctor
        (proEtaleRingModules Y (proEtaleConstantRing Y A)) i).obj K)
  have hQ : Q = DerivedCategory.homologyProperty P ⊓ DerivedCategory.TStructure.t.bounded := by
    funext K
    apply propext
    change (_ ∧ _) ↔ (_ ∧ DerivedCategory.TStructure.t.bounded K)
    rw [finite_homology_support_iff_bounded]
    exact and_comm
  change ObjectProperty.IsClosedUnderIsomorphisms Q ∧ ObjectProperty.IsTriangulated Q
  rw [hQ]
  exact ⟨inferInstance, htri⟩

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Module.ProEtaleModuleStalkFunctor
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Constructible sheaves placed in degree zero

Source: coefficient-twist blueprint, order 1505, proof step 10; Stacks Tag 03RZ.
(blueprint: lem-pur-constructible-single-support)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme

private theorem pullback_isZero {X Y : Scheme.{u}} (f : X ⟶ Y)
    (A : Type u) [CommRing A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A)) (hF : IsZero F) :
    IsZero (proEtaleConstantModulePullback f A F) := by
  have := proEtaleConstantRingComparison_isIso f A
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

private theorem locallyConstant_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
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

private theorem finite_stalk_of_isZero (Y : Scheme.{u}) (A : Type u) [CommRing A]
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

private theorem constructible_of_iso (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    {F G : proEtaleRingModules Y (proEtaleConstantRing Y A)} (e : F ≅ G)
    (hF : IsConstructibleProEtaleModuleSheaf Y A F) :
    IsConstructibleProEtaleModuleSheaf Y A G := by
  obtain ⟨S, hn, hS⟩ := hF
  refine ⟨S, hn, fun i ↦ ?_⟩
  let e' := (proEtaleConstantRingPullback A (S.immersion i)).mapIso e
  obtain ⟨I, U, f, hc, ht⟩ := (hS i).1
  refine ⟨⟨I, U, f, hc, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨M, ⟨hM⟩⟩ := ht j
    exact ⟨M, ⟨(SheafOfModules.overFunctor _ (U j)).mapIso e'.symm ≪≫ hM⟩⟩
  · intro Ω _ _ y
    let E := geometricRingModuleStalkFunctor y (proEtaleConstantRing (S.domain i) A)
    have : Finite (E.obj ((proEtaleConstantRingPullback A
        (S.immersion i)).obj F)) := (hS i).2 Ω y
    exact Finite.of_injective (E.mapIso e'.symm).toLinearEquiv
      (E.mapIso e'.symm).toLinearEquiv.injective

/-- A constructible sheaf in degree zero has finite constructible cohomology, supported
only in zero. Its support is exactly `{0}` when the sheaf is not a zero object.
Source: coefficient-twist blueprint, order 1505, step 10; Stacks Tag 03RZ
(blueprint: lem-pur-constructible-single-support).

Proof: the single complex has vanishing homology in every degree other than zero,
and its zeroth homology is the original sheaf. Constructibility transports across
isomorphisms by keeping the stratification, composing the restricted trivializations,
and transporting finiteness through the stalk functor. The zero sheaf is constructible
using the single stratum equal to the whole
scheme and the constant zero module on the identity cover. Its geometric stalks
are zero because the stalk functor is additive. The kernel of an identity supplies
this zero object. It is isomorphic to every vanishing homology object. Thus all homology is
constructible and the support is a subset of the finite set `{0}`. The zeroth
homology comparison shows that zero belongs to the support precisely when the
original sheaf is not zero. No nonemptiness of the scheme or of a stalk is assumed. -/
theorem constructible_single_support (Y : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (F : proEtaleRingModules Y (proEtaleConstantRing Y A))
    (hF : IsConstructibleProEtaleModuleSheaf Y A F)
    (K : proEtaleDerivedCategory Y A)
    (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj F) :
    Set.Finite (proEtaleCohomologicalSupport K) ∧
    (∀ i : ℤ, IsConstructibleProEtaleModuleSheaf Y A
      ((DerivedCategory.homologyFunctor _ i).obj
        K)) ∧
    proEtaleCohomologicalSupport K ⊆ {0} ∧
    (¬ IsZero F →
      proEtaleCohomologicalSupport K = {0}) := by
  classical
  have hz (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor _ i).obj K) := by
    apply IsZero.of_iso (Y := (DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ 0).obj F))
    · rcases lt_or_gt_of_ne hi with hi | hi
      · exact DerivedCategory.isZero_of_isGE _ 0 i hi
      · exact DerivedCategory.isZero_of_isLE _ 0 i hi
    · exact (DerivedCategory.homologyFunctor _ i).mapIso e
  have hs : proEtaleCohomologicalSupport K ⊆ {0} := by
    intro i hi
    by_contra h
    exact hi (hz i (by simpa using h))
  have h0 := (DerivedCategory.homologyFunctor _ 0).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app F
  have hzero := constructibleProEtale_of_isZero Y A _ (isZero_kernel_of_mono (𝟙 F))
  refine ⟨(Set.finite_singleton 0).subset hs, ?_, hs, ?_⟩
  · intro i
    by_cases hi : i = 0
    · subst i
      exact constructible_of_iso Y A h0.symm hF
    · exact constructible_of_iso Y A
        ((isZero_kernel_of_mono (𝟙 F)).iso (hz i hi)) hzero
  · intro hF0
    apply Set.Subset.antisymm hs
    intro i hi
    have hi0 : i = 0 := by simpa using hi
    subst i
    exact fun h ↦ hF0 (h.of_iso h0.symm)

end AlgebraicGeometry.Scheme

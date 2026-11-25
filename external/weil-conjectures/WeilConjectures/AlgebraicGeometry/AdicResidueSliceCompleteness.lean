/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.CategoryTheory.NativeRingedRestrictionDerivedHom
import WeilConjectures.CategoryTheory.NativeRingedRestrictionEquivalence
import WeilConjectures.CategoryTheory.NativeRingedRestrictionLocalization

/-! # Completeness on slices of completed coefficients

Source: Stacks Project, proetale.tex, Tag 09C6, first half of the proof.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace AlgebraicGeometry.Scheme

private noncomputable def sliceTest
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (M : CategoryTheory.ConstantCompletion.D O)
    (U : C) (f : O.obj.obj (op U)) : CategoryTheory.ConstantCompletion.D (O.over U) :=
  letI := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (O.over U))
  (derivedInternalHom (T.over U) (O.over U)).obj
    (op ((DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization (O.over U) (ringedSliceSection O U f))),
      (adicResidueRestriction O U).obj M)

private theorem isComplete_iff
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    {O S : Sheaf T CommRingCat.{w}} (q : O ⟶ S)
    (M : CategoryTheory.ConstantCompletion.D O) :
    CategoryTheory.ConstantCompletion.IsComplete q M ↔
      ∀ (U : C) (f : O.obj.obj (op U)), q.hom.app (op U) f = 0 →
        IsZero (sliceTest O M U f) := by
  have hk (U : C) : (CategoryTheory.ConstantCompletion.kernelIdeal q).sections U =
      RingHom.ker (q.hom.app (op U)).hom :=
    (CategoryTheory.ConstantCompletion.kernelIdeal_existsUnique q).exists.choose_spec U
  constructor
  · intro h U f hf
    apply h U f
    refine ⟨⟨f, ?_⟩, rfl⟩
    rw [hk]
    exact hf
  · intro h U f hf
    apply h U f
    change ∃ y : (CategoryTheory.ConstantCompletion.kernelIdeal q).sections U,
      y.val = f at hf
    obtain ⟨y, rfl⟩ := hf
    exact (le_of_eq (hk U)) y.property

private theorem sliceTest_isZero
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    (O : Sheaf T CommRingCat.{w}) (M : CategoryTheory.ConstantCompletion.D O)
    (U : C) (V : Over U) (f : O.obj.obj (op V.left))
    (hz : IsZero (sliceTest O M V.left f)) :
    IsZero (sliceTest (O.over U) ((adicResidueRestriction O U).obj M) V f) := by
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod O)
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (O.over U))
  let := HasDerivedCategory.standard (CategoryTheory.ConstantCompletion.Mod (O.over V.left))
  let := HasDerivedCategory.standard
    (CategoryTheory.ConstantCompletion.Mod ((O.over U).over V))
  let := HasDerivedCategory.standard
    (CategoryTheory.NativeRestriction.NativeModules.{w}
      (CategoryTheory.NativeRestriction.restrictedCommRing.{w, w, w, w, 0}
        (K := (T.over U).over V) V.iteratedSliceForward (O.over V.left)))
  have : V.iteratedSliceEquiv.inverse.IsDenseSubsite
      (T.over V.left) ((T.over U).over V) := inferInstance
  have : V.iteratedSliceEquiv.functor.IsDenseSubsite
      ((T.over U).over V) (T.over V.left) := inferInstance
  have : V.iteratedSliceForward.IsEquivalence :=
    inferInstanceAs V.iteratedSliceEquiv.functor.IsEquivalence
  have : V.iteratedSliceEquiv.symm.inverse.IsDenseSubsite
      ((T.over U).over V) (T.over V.left) :=
    inferInstanceAs (V.iteratedSliceEquiv.functor.IsDenseSubsite
      ((T.over U).over V) (T.over V.left))
  let F := CategoryTheory.NativeRestriction.restrictModules.{w, w, w, w, 0}
    (K := (T.over U).over V) V.iteratedSliceForward (O.over V.left)
  have : F.IsEquivalence :=
    CategoryTheory.NativeRestriction.restrictModules_isEquivalence.{w, w, w, w, 0}
      V.iteratedSliceEquiv.symm (O.over V.left)
  have : F.Additive :=
    CategoryTheory.NativeRestriction.restrictModules_additive.{w, w, w, w, 0}
      (K := (T.over U).over V) V.iteratedSliceForward (O.over V.left)
  have : PreservesFiniteLimits F := inferInstance
  have : PreservesFiniteColimits F := inferInstance
  let L := (DerivedCategory.singleFunctor _ 0).obj
    (ringedSectionLocalization (O.over V.left) (ringedSliceSection O V.left f))
  let N := (adicResidueRestriction O V.left).obj M
  -- Transport internal Hom along the equivalence of the two slice sites.
  obtain ⟨e⟩ := CategoryTheory.NativeRestriction.derivedHomRestriction.{w, w, w, w, 0}
    (K := (T.over U).over V) V.iteratedSliceForward (O.over V.left)
    (fun _ ↦ inferInstance) L N
  obtain ⟨eL₀⟩ := CategoryTheory.NativeRestriction.localizationRestriction.{w, w, w, w, 0}
    (K := (T.over U).over V) V.iteratedSliceForward (O.over V.left)
    (ringedSliceSection O V.left f)
  let eL : F.mapDerivedCategory.obj L ≅ (DerivedCategory.singleFunctor _ 0).obj
      (ringedSectionLocalization ((O.over U).over V)
        (ringedSliceSection (O.over U) V f)) :=
    (F.mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso eL₀
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((CategoryTheory.siteModuleRings O).over V.left))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((CategoryTheory.siteModuleRings O).over U))
  let := HasDerivedCategory.standard
    (SheafOfModules.{w} ((CategoryTheory.siteModuleRings (O.over U)).over V))
  let A := SheafOfModules.overFunctor (CategoryTheory.siteModuleRings O)
    V.left
  let B := SheafOfModules.overFunctor (CategoryTheory.siteModuleRings O) U
  let D := SheafOfModules.overFunctor
    (CategoryTheory.siteModuleRings (O.over U)) V
  have : A.Additive := ringedOverFunctor_additive O V.left
  have : B.Additive := ringedOverFunctor_additive O U
  have : D.Additive := ringedOverFunctor_additive (O.over U) V
  have : PreservesFiniteLimits A := ringedOverFunctor_preservesFiniteLimits O V.left
  have : PreservesFiniteColimits A := ringedOverFunctor_preservesFiniteColimits O V.left
  have : PreservesFiniteLimits B := ringedOverFunctor_preservesFiniteLimits O U
  have : PreservesFiniteColimits B := ringedOverFunctor_preservesFiniteColimits O U
  have : PreservesFiniteLimits D := ringedOverFunctor_preservesFiniteLimits (O.over U) V
  have : PreservesFiniteColimits D := ringedOverFunctor_preservesFiniteColimits (O.over U) V
  -- Compare sections individually to avoid unfolding the composite functors.
  let c : A ⋙ F ≅ B ⋙ D :=
    NatIso.ofComponents (fun P ↦ (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _) (by intros; ext x; rfl)))
      (by intros; ext W x; rfl)
  -- Descend the sectionwise identity to the derived categories.
  let eN : F.mapDerivedCategory.obj N ≅
      (adicResidueRestriction (O.over U) V).obj ((adicResidueRestriction O U).obj M) :=
    (Functor.mapDerivedCategoryCompIso A F).app M ≪≫
      (Functor.mapDerivedCategoryNatIso c).app M ≪≫
        (Functor.mapDerivedCategoryCompIso B D).symm.app M
  let e' := e ≪≫ (derivedInternalHom ((T.over U).over V) ((O.over U).over V)).mapIso
    (eL.symm.op.prod eN)
  exact (F.mapDerivedCategory.map_isZero hz).of_iso e'.symm

/-- Restriction to an arbitrary slice preserves local derived completeness.
Source: Stacks Project, algebraization.tex, Tag 0999; Modules on Sites, Section 03DH;
Cohomology on Sites, Tag 08JB; proetale.tex, Tag 09C6, the connected-local reduction.
(auxiliary; not a blueprint node).

Proof: The slice ring and first projection are sectionwise restrictions of the
original ones. Thus the kernel ideal over an arrow V -> U has exactly the same
sections as the original kernel on V. The iterated slice (C/U)/(V -> U) is canonically
equivalent to C/V, by forgetting the intermediate arrow and by composition in the
inverse direction. This equivalence preserves coverings and the coefficient ring.
Its exact module equivalence identifies the localized module for each kernel section
with the original localization on C/V. The composite restriction of M identifies
with direct restriction to V. Compute derived internal Hom by a K-injective
representative: exact equivalences preserve K-injectives and identify the Hom
complexes sectionwise. Therefore the internal Hom in the local completeness test
on the iterated slice is the image under an equivalence of the zero internal Hom
supplied by completeness of M at V. It is zero. This applies to every U, every arrow
V -> U and every kernel section, and proves the stated local completeness. No
boundedness, affine hypothesis or weak contractibility is used. The zero ring,
zero ideal and empty slices use the same equivalence and vanishing argument. -/
theorem adicResidue_slice_completeness
    (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] [IsNoetherianRing A]
    (J : Ideal A) :
    (∀ (M : CategoryTheory.ConstantCompletion.D
        (CategoryTheory.ConstantCompletion.completed
          (coefficientProEtaleModelTopology.{u, v} X) A J)),
      CategoryTheory.ConstantCompletion.IsComplete
        (CategoryTheory.ConstantCompletion.projection
          (coefficientProEtaleModelTopology.{u, v} X) A J 0) M →
      ∀ U : coefficientProEtaleSiteModel.{u, v} X,
        CategoryTheory.ConstantCompletion.IsComplete
          (adicResidueLocalProjection.{u, v} X J U 0)
          ((adicResidueRestriction
            (CategoryTheory.ConstantCompletion.completed
              (coefficientProEtaleModelTopology.{u, v} X) A J) U).obj M)) := by
  intro M hM U
  let O := CategoryTheory.ConstantCompletion.completed
    (coefficientProEtaleModelTopology.{u, v} X) A J
  let q := CategoryTheory.ConstantCompletion.projection
    (coefficientProEtaleModelTopology.{u, v} X) A J 0
  apply (isComplete_iff (adicResidueLocalProjection X J U 0) _).mpr
  intro V f hf
  have hz : IsZero (sliceTest O M V.left f) :=
    (isComplete_iff q M).mp hM V.left f hf
  exact sliceTest_isZero O M U V f hz

end AlgebraicGeometry.Scheme

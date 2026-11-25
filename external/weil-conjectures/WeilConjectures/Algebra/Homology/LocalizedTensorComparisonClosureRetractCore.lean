/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonProperty
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Flat.Basic
import WeilConjectures.Algebra.Homology.LocalizedTensorComparisonDerivedArrow
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

@[expose] public section
universe u
open CategoryTheory MonoidalCategory
open scoped TensorProduct
set_option autoImplicit false
namespace ModuleCat

private theorem exists_kFlat_representative
    {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat.{u} A)]
    (Y : DerivedCategory (ModuleCat.{u} A)) :
    ∃ V : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (DerivedCategory.Q.obj V ≅ Y) ∧
      ∀ W : CochainComplex (ModuleCat.{u} A) ℤ, W.Acyclic →
        (CochainComplex.mapBifunctor W V (curriedTensor _)).Acyclic := by
  classical
  have (M : ModuleCat.{u} A) : CategoryTheory.Limits.PreservesColimitsOfShape ℤ
      ((curriedTensor (ModuleCat.{u} A)).flip.obj M) :=
    inferInstanceAs (CategoryTheory.Limits.PreservesColimitsOfShape ℤ (tensorRight M))
  have : CategoryTheory.HasExactColimitsOfShape ℤ (ModuleCat.{u} A) :=
    CategoryTheory.HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
      (AsSmall.equiv (C := ℤ)).symm
  let L := DerivedCategory.Q.objPreimage Y
  let Λ := (Classical.choice (inferInstance :
    Abelian.HasFunctorialFlatResolution (ModuleCat.{u} A))).reduced
  let V := Λ.resolutionFunctor.obj L
  let s := Λ.resolutionNatTrans.app L
  have hs : QuasiIso s := inferInstance
  have : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ s).2 hs
  have hk := Λ.kFlat_resolutionFunctor_obj ObjectProperty.flat.essImage_ι_le L
  refine ⟨V, ⟨asIso (DerivedCategory.Q.map s) ≪≫
    DerivedCategory.Q.objObjPreimageIso Y⟩, ?_⟩
  rw [← HomotopyCategory.kFlat_quotient_obj_iff,
    HomotopyCategory.kFlat_iff_preserves_acyclic] at hk
  intro W hW
  have hW' := (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic W).2 hW
  exact (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic
    (CochainComplex.mapBifunctor W V (curriedTensor _))).1 (hk _ hW').2

variable (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra (A ⊗[R] B) C]
  [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} A)]
  [HasDerivedCategory (ModuleCat.{u} B)]
  (Q : CochainComplex (ModuleCat.{u} A) ℤ)
  (N : CochainComplex (ModuleCat.{u} C) ℤ)
  (t : (((extendScalars.{u, u, u}
    ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
      (.up ℤ)).obj Q) ⟶ N)

/-- Core component of retract closure, with the representative and model quantifiers exposed.
Source: Stacks Project, Tag 0DJA(1), retract part.
(blueprint: lem-pc-localized-tensor-comparison-closure-retracts-core) -/
theorem localizedTensorComparisonProperty_retract_core
    (hQ : ∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V Q (curriedTensor _)).Acyclic)
    {X Y : DerivedCategory (ModuleCat.{u} A)} (hXY : Retract X Y)
    (hY : localizedTensorComparisonProperty R A B C Q N t Y) :
    ∀ (U : CochainComplex (ModuleCat.{u} A) ℤ),
    Nonempty (DerivedCategory.Q.obj U ≅ X) →
    (∀ V : CochainComplex (ModuleCat.{u} A) ℤ, V.Acyclic →
      (CochainComplex.mapBifunctor V U (curriedTensor _)).Acyclic) →
    ∀ (mU : BaseDerivedTensorCohomologyModel R A B (U ⊗ Q) C) (i : ℤ),
    let F := (extendScalars.{u, u, u}
      ((algebraMap (A ⊗[R] B) C).comp (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex
        (.up ℤ)
    IsIso (mU.localizedComparison i ≫ HomologicalComplex.homologyMap
      ((Functor.Monoidal.μIso F U Q).inv ≫ (F.obj U ◁ t)) i) := by
  classical
  intro U hUX hU mU i
  obtain ⟨eUX⟩ := hUX
  obtain ⟨V, ⟨eVY⟩, hV⟩ := exists_kFlat_representative Y
  obtain ⟨mV⟩ := nonempty_baseDerivedTensorCohomologyModel R A B (V ⊗ Q) C
  obtain ⟨H, hH⟩ := exists_localizedTensorComparison_derived_arrow R A B C Q N t hQ i
  obtain ⟨eU⟩ := hH U hU mU
  obtain ⟨eV⟩ := hH V hV mV
  have hr : Retract (DerivedCategory.Q.obj U) (DerivedCategory.Q.obj V) :=
    ((Retract.ofIso eUX).trans hXY).trans (Retract.ofIso eVY.symm)
  let ha := ((Retract.ofIso eU).trans (hr.map H)).trans (Retract.ofIso eV.symm)
  exact MorphismProperty.of_retract (P := MorphismProperty.isomorphisms _) ha
    (hY V ⟨eVY⟩ hV mV i)
end ModuleCat

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Braided
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization

/-! # K-flatness after restricting a localized base

Source: Stacks Project, Tags 06Y6 and 00CS.
(blueprint: lem-pc-localization-restriction-kflat).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory MonoidalCategory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace ModuleCat

/-- Restriction along a localization preserves K-flat complexes.
Source: Stacks Project, Tag 06Y6, computation of derived base change; Tag 00CS.
(blueprint: lem-pc-localization-restriction-kflat).

Proof: let F be any acyclic R-complex. Flatness of the localization makes
Rp tensor_R F acyclic. Tensor associativity identifies the restriction of
(Rp tensor_R F) tensor_Rp P with F tensor_R (restriction P), term by term
and on differentials, and commutes with the direct sums in totalization.
K-flatness of P makes the former tensor acyclic. Exact restriction preserves
acyclicity, so the latter tensor is acyclic. Braiding gives the other tensor
order, hence the K-flat predicate. This also works for identity localizations,
unbounded complexes and the zero localization: no nonzero assumption is used. -/
theorem kFlat_restrictScalars_of_isLocalization
    {R Rp : Type u} [CommRing R] [CommRing Rp] [Algebra R Rp]
    (S : Submonoid R) [IsLocalization S Rp]
    (P : CochainComplex (ModuleCat.{u} Rp) ℤ)
    (hP : (HomologicalComplex.quasiIso (ModuleCat.{u} Rp) (.up ℤ)).kFlat P) :
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (.up ℤ)).kFlat
      (((restrictScalars (algebraMap R Rp)).mapHomologicalComplex (.up ℤ)).obj P) := by
  let f := algebraMap R Rp
  let E := (extendScalars f).mapHomologicalComplex (.up ℤ)
  let U := (restrictScalars f).mapHomologicalComplex (.up ℤ)
  let B := (mixedTensor f).flip.map₂CochainComplex
  have : CategoryTheory.Limits.PreservesFiniteLimits (extendScalars f) :=
    preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat Rp S))
  obtain ⟨e⟩ := CochainComplex.exists_mixedTensor_restriction_iso f
  have hright : HomologicalComplex.preservesQuasiIso (tensorRight (U.obj P)) := by
    intro F G a ha
    have : QuasiIso a := ha
    have he : QuasiIso (E.map a) := inferInstance
    have hb : QuasiIso ((B.map a).app P) := by
      change QuasiIso (HomologicalComplex.mapBifunctorMap (E.map a) (𝟙 P)
        (curriedTensor (ModuleCat.{u} Rp)).flip (.up ℤ))
      have ht := hP.whiskerLeft he
      exact (quasiIso_iff_of_arrow_mk_iso _ _
        (Arrow.isoMk
          (HomologicalComplex.mapBifunctorFlipIso P (E.obj F)
            (curriedTensor (ModuleCat.{u} Rp)) (.up ℤ))
          (HomologicalComplex.mapBifunctorFlipIso P (E.obj G)
            (curriedTensor (ModuleCat.{u} Rp)) (.up ℤ))
          (by exact (HomologicalComplex.mapBifunctorFlipIso_hom_naturality
            (𝟙 P) (E.map a) (curriedTensor (ModuleCat.{u} Rp)) (.up ℤ)).symm))).2 ht
    have hu : QuasiIso (U.map ((B.map a).app P)) := inferInstance
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk ((e.app F).app P) ((e.app G).app P)
        (by exact (congrArg (fun t ↦ t.app P) (e.hom.naturality a)).symm))).1 hu
  refine ⟨?_, hright⟩
  intro F G a ha
  have ht := hright a ha
  exact (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (β_ (U.obj P) F) (β_ (U.obj P) G)
      (by exact (BraidedCategory.braiding_naturality_right (U.obj P) a).symm))).2 ht

end ModuleCat

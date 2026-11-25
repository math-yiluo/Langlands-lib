/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import Mathlib.RingTheory.Localization.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Localization.BaseChange

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace RingTensorCohomology

/-- Ordinary complex cohomology has denominator torsion in the localization-unit kernel.
Source: Stacks Project, Tags 00CS and 00DK, exactness of module localization.
(blueprint: new-lem-pc-complex-localization-unit-kernel).

Proof: represent x by a cycle z in degree i. Its localized image is a boundary,
so write a boundary witness as y/t with y in C^(i-1) and t in S. The equation
z/1 = d(y)/t says that some s in S kills t*z-d(y) in C^i, by the equality
criterion for localized modules. Thus (s*t)*z = d(s*y). This is a boundary
already in C, and hence (s*t)*x = 0. The product s*t belongs to S. This uses only
the two adjacent terms of C, so no boundedness is required. If 0 is in S, its
zero multiple works; for S={1} the unit is an isomorphism and x=0. -/
theorem complexLocalizationUnit_kernel (A Aq : Type u) [CommRing A] [CommRing Aq]
    [Algebra A Aq] (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (C : CochainComplex (ModuleCat.{u} A) ℤ) (x : C.homology i)
    (hx : (HomologicalComplex.homologyMap
      (((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).mapHomologicalComplex
        (.up ℤ)).unit.app C) i) x = 0) :
    ∃ s : S, (s : A) • x = 0 := by
  let f := algebraMap A Aq
  let E := ModuleCat.extendScalars f
  let G := ModuleCat.restrictScalars f
  let adj := ModuleCat.extendRestrictScalarsAdj f
  have : Module.Flat A Aq := IsLocalization.flat Aq S
  have : CategoryTheory.Limits.PreservesFiniteLimits E :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat
      (RingHom.flat_algebraMap_iff.mpr ‹Module.Flat A Aq›)
  have : E.IsLeftAdjoint := adj.isLeftAdjoint
  have : CategoryTheory.Limits.PreservesFiniteColimits E := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits G := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteColimits G := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits (E ⋙ G) :=
    CategoryTheory.Limits.comp_preservesFiniteLimits E G
  have : CategoryTheory.Limits.PreservesFiniteColimits (E ⋙ G) :=
    CategoryTheory.Limits.comp_preservesFiniteColimits E G
  have : (E ⋙ G).PreservesHomology := inferInstance
  let T := C.sc i
  let e := T.mapHomologyIso (𝟭 (ModuleCat.{u} A))
  let e' := T.mapHomologyIso (E ⋙ G)
  have hmap : HomologicalComplex.homologyMap
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app C) i =
      e.hom ≫ adj.unit.app T.homology ≫ e'.inv := by
    change ShortComplex.homologyMap (T.mapNatTrans adj.unit) = _
    exact T.homologyMap_mapNatTrans adj.unit
  have hz : adj.unit.app T.homology (e.hom x) = 0 := by
    have h := congrArg (fun y ↦ e'.hom y) hx
    rw [hmap] at h
    change (e.hom ≫ adj.unit.app T.homology ≫ e'.inv ≫ e'.hom) x = e'.hom 0 at h
    simpa only [Iso.inv_hom_id, Category.comp_id, ModuleCat.comp_apply,
      e'.hom.hom.map_zero] using h
  let u : T.homology →ₗ[A] (G.obj (E.obj T.homology)) := (adj.unit.app _).hom
  have hloc : IsLocalization S Aq := inferInstance
  have halg : f.toAlgebra = ‹Algebra A Aq› := Algebra.algebra_ext _ _ fun _ ↦ rfl
  have : IsLocalizedModule S u := by
    let : Algebra A Aq := f.toAlgebra
    have : IsLocalization S Aq := by
      change @IsLocalization A _ S Aq _ f.toAlgebra
      rw [halg]
      exact hloc
    change IsLocalizedModule S (TensorProduct.mk A Aq T.homology 1)
    infer_instance
  have hu : u (e.hom x) = u 0 := by
    rw [u.map_zero]
    exact hz
  obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := u) hu
  refine ⟨s, ?_⟩
  apply (ModuleCat.mono_iff_injective e.hom).1 inferInstance
  rw [e.hom.hom.map_smul, e.hom.hom.map_zero]
  simpa only [Submonoid.smul_def, smul_zero] using hs

end RingTensorCohomology

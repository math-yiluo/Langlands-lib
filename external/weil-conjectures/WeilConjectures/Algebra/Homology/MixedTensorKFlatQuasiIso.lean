/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.MixedTotalTensor
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.MixedTensorRestrictionComparison
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution

/-!
# Quasi-isomorphisms for mixed total tensor

Source: Stacks Project, More on Algebra, Tags 064L and 06Y0.
(blueprint: lem-pc-mixed-tensor-kflat-quasi-iso)
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

/-- Mixed total tensor preserves quasi-isomorphisms in the two K-flat situations.
Source: Stacks Project, Tags 064L and 06Y0.
(blueprint: lem-pc-mixed-tensor-kflat-quasi-iso)

Proof: Restrict the A-complexes to R. The canonical associativity isomorphism
N ⊗_A (A ⊗_R E) ≅ E ⊗_R N, applied in each bidegree of the flipped
mixed tensor, identifies its restriction with the ordinary total tensor.
Restriction of scalars is exact and reflects isomorphisms, so it detects
quasi-isomorphisms. For the first clause choose an R-K-flat resolution K → N
of the restricted complex. In the tensor square for a and this resolution,
the two vertical arrows and the top arrow are quasi-isomorphisms by K-flatness;
two-of-three gives the bottom arrow. For the second clause K-flatness of F
applied to the restricted quasi-isomorphism u gives the result directly.
The termwise identifications commute with the signed differentials and both
variable maps. No flatness of A over R is required. -/
theorem mixedTensor_kFlat_quasiIso {R A : Type u} [CommRing R] [CommRing A]
    (f : R →+* A) :
    let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
    (∀ (N : CochainComplex (ModuleCat.{u} A) ℤ)
      (E E' : CochainComplex (ModuleCat.{u} R) ℤ) (a : E ⟶ E'),
      QuasiIso a → (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E →
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat E' →
      QuasiIso ((B.map a).app N)) ∧
    (∀ (N N' : CochainComplex (ModuleCat.{u} A) ℤ) (u : N ⟶ N'),
      QuasiIso u → ∀ F : CochainComplex (ModuleCat.{u} R) ℤ,
      (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).kFlat F →
      QuasiIso ((B.obj F).map u)) := by
  let S := (ModuleCat.restrictScalars f).mapHomologicalComplex (.up ℤ)
  let B := (ModuleCat.mixedTensor f).flip.map₂CochainComplex
  obtain ⟨e⟩ := exists_mixedTensor_restriction_iso f
  constructor
  · intro N E E' a ha hE hE'
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      ((B.map a).app N) (ModuleCat.restrictScalars f)).1
    have ht := (HomologicalComplex.quasiIso (ModuleCat R) (.up ℤ)).whiskerRight_of_kFlat
      a ha hE hE' (S.obj N)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk ((e.app E).app N) ((e.app E').app N)
        (by exact (congrArg (fun t ↦ t.app N) (e.hom.naturality a)).symm))).2 ht
  · intro N N' a ha F hF
    apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
      ((B.obj F).map a) (ModuleCat.restrictScalars f)).1
    have : QuasiIso a := ha
    have ht := hF.whiskerLeft
      (show QuasiIso (S.map a) from inferInstance)
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoMk ((e.app F).app N) ((e.app F).app N')
        (by exact ((e.app F).hom.naturality a).symm))).2 ht

end CochainComplex

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.RightDerivedFunctorTruncationIso
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB

/-! # The lowest cohomology of truncated derived sections

Source: Stacks Project, Tag 05TC (2), and Tag 06Z0, proof of Lemma 36.3.5.
(blueprint: new-affine-derived-sections-truncated-bottom).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- Left exactness computes the lowest cohomology of truncated derived sections.
This statement applies to every derived sheaf object, without quasi-coherence.
Source: Stacks Project, Tag 05TC (2); Tag 06Z0, cohomology calculation.
(blueprint: new-affine-derived-sections-truncated-bottom).

Proof: Write S for sections followed by scalar transport; it preserves finite
limits. Lift truncGE n into the bounded below derived category. The canonical
map truncLT (n + 1) -> identity becomes invertible on H^n after derived S,
by isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι. On this lifted
functor, truncGE n after truncLT (n + 1) is already invertible, since the
objects have no cohomology below n. The natural isomorphism
DerivedCategory.Plus.eTruncLTCompETruncGEIso identifies this double truncation
with H^n followed by the single functor in degree n. Commutation of single
functors, derived S and homology with shifts reduces its cohomology to the
single functor in degree zero. Compose the single-functor derived comparison
with rightDerivedZeroIsoSelf. Finally use compatibility of bounded below
and unbounded derived S and the canonical H^n truncGE projection isomorphism.
Ordinary S is definitionally moduleSpecΓFunctor. Every map is natural, and no
quasi-coherence, boundedness of the original object, or nonzero-ring hypothesis
is needed. -/
theorem affineDerivedSections_truncated_bottom (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (n : ℤ) :
    Nonempty ((DerivedCategory.TStructure.t.truncGE n) ⋙
      (RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ≅
      DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)) n ⋙
      moduleSpecΓFunctor (R := .of A)) := by
  let C := SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace)
  let S := RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  have : Limits.PreservesFiniteLimits S := by
    dsimp [S, RingedSpace.globalSectionsFunctor]
    infer_instance
  let t := DerivedCategory.TStructure.t (C := C)
  let tp := DerivedCategory.Plus.TStructure.t (C := C)
  let L := t.plus.lift (t.truncGE n) (fun K ↦ ⟨n, inferInstance⟩)
  let H := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) n
  let R := S.rightDerivedFunctorPlus
  let α := Functor.whiskerLeft L
    (Functor.whiskerRight (Functor.whiskerRight (tp.truncLTι (n + 1)) R) H)
  have (K : DerivedCategory C) : IsIso (α.app K) := by
    apply S.isIso_homologyFunctor_rightDerivedFunctorPlus_truncLEι n (L.obj K)
  have : IsIso α := NatIso.isIso_of_isIso_app α
  let β := Functor.whiskerLeft L
    (Functor.whiskerLeft (tp.truncLT (n + 1))
      (Functor.whiskerRight (Functor.whiskerRight (tp.truncGEπ n) R) H))
  have (K : DerivedCategory C) : IsIso (β.app K) := by
    have : tp.IsGE (L.obj K) n := by
      apply (DerivedCategory.Plus.isGE_ι_obj_iff (L.obj K) n).mp
      change t.IsGE ((t.truncGE n).obj K) n
      infer_instance
    have : IsIso ((tp.truncGEπ n).app ((tp.truncLT (n + 1)).obj (L.obj K))) :=
      inferInstance
    change IsIso (H.map (R.map _))
    infer_instance
  have : IsIso β := NatIso.isIso_of_isIso_app β
  let eT := DerivedCategory.Plus.eTruncLTCompETruncGEIso (C := C) n
  let Hn := DerivedCategory.Plus.homologyFunctor C n
  let H₀ := DerivedCategory.Plus.homologyFunctor (ModuleCat.{u} A) 0
  let eS : DerivedCategory.Plus.singleFunctor C n ⋙ R ⋙ H ≅ S :=
    Functor.isoWhiskerRight
      ((DerivedCategory.Plus.singleFunctors C).shiftIso (-n) n 0 (by omega)).symm
      (R ⋙ H) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (Functor.isoWhiskerRight (R.commShiftIso (-n)) H) ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0 ⋙ R)
      (H₀.shiftIso (-n) n 0 (by omega)) ≪≫
    S.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso 0 ≪≫
    S.rightDerivedZeroIsoSelf
  let e := (asIso α).symm ≪≫ asIso β ≪≫
    Functor.isoWhiskerLeft L (Functor.isoWhiskerRight eT (R ⋙ H)) ≪≫
    Functor.isoWhiskerLeft (L ⋙ Hn) eS
  let HC := DerivedCategory.homologyFunctor C n
  let HA := DerivedCategory.homologyFunctor (ModuleCat.{u} A) n
  let γ := Functor.whiskerRight (t.truncGEπ n) HC
  have (K : DerivedCategory C) : IsIso (γ.app K) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n n le_rfl
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  let eP := Functor.isoWhiskerLeft L
    (Functor.isoWhiskerRight S.rightDerivedFunctorPlusCompatibility.symm HA)
  change Nonempty ((t.truncGE n) ⋙ S.rightDerivedFunctor ⋙ HA ≅
    HC ⋙ moduleSpecΓFunctor (R := .of A))
  exact ⟨eP ≪≫ e ≪≫ Functor.isoWhiskerRight (asIso γ).symm S⟩

end AlgebraicGeometry

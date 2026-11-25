/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

/-! # Bottom cohomology of a left exact derived functor

Source: Stacks Project, Tag 05TC (2).
(blueprint: new-qcoh-sections-left-exact-bottom).
-/

@[expose] public section

universe uC vC uD vD wC wD
open CategoryTheory
namespace CategoryTheory.Functor

/-- A left exact functor computes bottom cohomology after lower truncation.
Source: Stacks Project, Tag 05TC (2).
(blueprint: new-qcoh-sections-left-exact-bottom).

Proof: Lift the lower truncation to the bounded below category. Upper truncation
at n has invertible H^n after deriving a left exact functor. Double truncation
is the single cohomology object in degree n. Shift to degree zero, apply the
single-object comparison and rightDerivedZeroIsoSelf. Compatibility of bounded
below and unbounded derived functors and the homology truncation projection
give the displayed natural isomorphism. No quasi-coherence is needed. -/
theorem rightDerivedFunctor_truncated_bottom
    {C : Type uC} [Category.{vC} C] [Abelian C]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    [HasDerivedCategory.{wC} C]
    {D : Type uD} [Category.{vD} D] [Abelian D]
    [HasDerivedCategory.{wD} D]
    (S : C ⥤ D) [S.Additive] [Limits.PreservesFiniteLimits S] (n : ℤ) :
    Nonempty ((DerivedCategory.TStructure.t.truncGE n) ⋙ S.rightDerivedFunctor ⋙
      DerivedCategory.homologyFunctor D n ≅
      DerivedCategory.homologyFunctor C n ⋙ S) := by
  let t := DerivedCategory.TStructure.t (C := C)
  let tp := DerivedCategory.Plus.TStructure.t (C := C)
  let L := t.plus.lift (t.truncGE n) (fun K ↦ ⟨n, inferInstance⟩)
  let H := DerivedCategory.Plus.homologyFunctor D n
  let R := S.rightDerivedFunctorPlus
  let α := Functor.whiskerLeft L
    (Functor.whiskerRight (Functor.whiskerRight (tp.truncLTι (n + 1)) R) H)
  have (K : DerivedCategory C) : IsIso (α.app K) := by
    let M := L.obj K
    let T := (R ⋙ DerivedCategory.Plus.ι).mapTriangle.obj
      ((tp.triangleLTGE (n + 1)).obj M)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      (R ⋙ DerivedCategory.Plus.ι).map_distinguished _
        (tp.triangleLTGE_distinguished (n + 1) M)
    have hz (j : ℤ) (hj : j < n + 1) :
        Limits.IsZero ((DerivedCategory.homologyFunctor D j).obj T.obj₃) := by
      exact S.isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
        ((tp.truncGE (n + 1)).obj M) (n + 1) hj
    exact DerivedCategory.isIso_homologyMap_mor₁ T hT (n - 1) n (by omega)
      (hz (n - 1) (by omega)) (hz n (by omega))
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
  let H₀ := DerivedCategory.Plus.homologyFunctor D 0
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
  let HA := DerivedCategory.homologyFunctor D n
  let γ := Functor.whiskerRight (t.truncGEπ n) HC
  have (K : DerivedCategory C) : IsIso (γ.app K) :=
    DerivedCategory.isIso_homologyFunctor_map_truncGEπ_app K n n le_rfl
  have : IsIso γ := NatIso.isIso_of_isIso_app γ
  let eP := Functor.isoWhiskerLeft L
    (Functor.isoWhiskerRight S.rightDerivedFunctorPlusCompatibility.symm HA)
  change Nonempty ((t.truncGE n) ⋙ S.rightDerivedFunctor ⋙ HA ≅
    HC ⋙ S)
  exact ⟨eP ≪≫ e ≪≫ Functor.isoWhiskerRight (asIso γ).symm S⟩

end CategoryTheory.Functor

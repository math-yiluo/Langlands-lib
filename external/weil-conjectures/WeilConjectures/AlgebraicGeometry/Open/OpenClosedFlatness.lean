/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.OpenClosed.Exact
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic

import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicTensorComparison
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Flatness on an open--closed decomposition

The two declarations below spell out the ordinary module-sheaf assertion on the
small étale and small pro-étale sites. Étale flatness is detected on geometric
fibers. On the pro-étale site, the intrinsic constant-ring realization transfers
flatness to fixed-scalar sheaves, where complementary pullbacks detect the kernel
of each tensored monomorphism. The open unit, closed counit and disjoint-range
vanishing prove preservation by extension by zero and closed direct image.

## References

* Stacks Tags 095L, 03ER and 05VD
* Stacks Tags 09AH, 03DI and 05VD
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Flatness is detected on the two members of a complementary pair on the
small étale site; extension by zero and closed direct image preserve flatness.
-/
theorem openClosedFlatness_etale
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (CategoryTheory.ObjectProperty.flat H ↔
      (CategoryTheory.ObjectProperty.flat ((Etale.upperStar (ModuleCat.{u + 1} A) j).obj H) ∧
        CategoryTheory.ObjectProperty.flat ((Etale.upperStar (ModuleCat.{u + 1} A) i).obj H))) ∧
      (∀ L : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A),
        CategoryTheory.ObjectProperty.flat L →
          CategoryTheory.ObjectProperty.flat
            ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).obj L)) ∧
      (∀ M : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A),
        CategoryTheory.ObjectProperty.flat M →
          CategoryTheory.ObjectProperty.flat
            ((Etale.lowerStar (ModuleCat.{u + 1} A) i).obj M)) := by
  let B := ModuleCat.{u + 1} A
  have detect (F : Sheaf X.smallEtaleTopology B)
      (hj : ObjectProperty.flat ((Etale.upperStar B j).obj F))
      (hi : ObjectProperty.flat ((Etale.upperStar B i).obj F)) : ObjectProperty.flat F := by
    apply (Etale.flat_iff_forall_flat_sheafFiber_obj F).2
    intro Ω _ _ s
    obtain ⟨t, ht, -⟩ | ⟨t, ht, -⟩ :=
      existsUnique_fac_or_fac_of_range_eq_compl j i hij s
    · subst ht
      exact ObjectProperty.prop_of_iso ObjectProperty.flat
        ((Etale.upperStarCompUliftSheafFiberIso B j t).app F)
          ((Etale.flat_iff_forall_flat_sheafFiber_obj _).1 hj t)
    · subst ht
      exact ObjectProperty.prop_of_iso ObjectProperty.flat
        ((Etale.upperStarCompUliftSheafFiberIso B i t).app F)
          ((Etale.flat_iff_forall_flat_sheafFiber_obj _).1 hi t)
  refine ⟨⟨fun h ↦ ⟨Functor.PreservesFlat.flat_obj h,
    Functor.PreservesFlat.flat_obj h⟩, fun h ↦ detect H h.1 h.2⟩, ?_, ?_⟩
  · intro L hL
    apply detect
    · exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (asIso ((Etale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app L)) hL
    · exact ObjectProperty.flat_of_isZero
        (Etale.isZero_upperStar_openImmersionLowerShriek_of_disjoint_range B j i
          (disjoint_range_of_range_eq_compl j i hij) L)
  · intro M hM
    apply detect
    · exact ObjectProperty.flat_of_isZero
        (Etale.isZero_upperStar_lowerStar_of_disjoint_range B j i
          (disjoint_range_of_range_eq_compl j i hij) M)
    · exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (asIso ((Etale.upperStarLowerStarAdjunction B i).counit.app M)).symm hM

private theorem site_flat_of_iso {T : Scheme.{u}} (A : Type u) [CommRing A]
    {M N : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)}
    (e : M ≅ N)
    (hN : SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := Scheme.proEtaleConstantRing T A) N) :
    SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
      (R := Scheme.proEtaleConstantRing T A) M := by
  let R := Scheme.proEtaleConstantRing T A
  apply (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1} R M).mpr
  intro U n a s h
  let s' (i : Fin n) := e.hom.val.app (Opposite.op U) (s i)
  have hs : (∑ i, a i • s' i) = 0 := by
    change (∑ i, a i • (e.hom.val.app (Opposite.op U)) (s i)) = 0
    simpa only [map_sum, map_smul, map_zero] using
      congrArg (fun z ↦ e.hom.val.app (Opposite.op U) z) h
  obtain ⟨S, hS, hlocal⟩ :=
    (SheafOfModules.isFlatOnSite_iff_local_equationalCriterion.{u + 1, u, u + 1, u + 1}
      R N).mp hN U n a s' hs
  refine ⟨S, hS, ?_⟩
  intro V f hf
  obtain ⟨l, b, t, ht, hb⟩ := hlocal V f hf
  refine ⟨l, b, fun q ↦ e.inv.val.app (Opposite.op V) (t q), ?_, hb⟩
  intro p
  have hp := congrArg (fun z ↦ e.inv.val.app (Opposite.op V) z) (ht p)
  simp only [map_sum, map_smul] at hp
  rw [← PresheafOfModules.naturality_apply] at hp
  have hinv : e.inv.val.app (Opposite.op V)
      (e.hom.val.app (Opposite.op V) (M.val.map f.op (s p))) =
      M.val.map f.op (s p) :=
    congrArg (fun z ↦ z.val.app (Opposite.op V) (M.val.map f.op (s p))) e.hom_inv_id
  exact hinv.symm.trans hp

private theorem intrinsic_flat_iff (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (N : Sheaf (ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    ObjectProperty.flat N ↔
      SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
        (R := Scheme.proEtaleConstantRing T A)
        ((Scheme.sfIntrinsicModuleEquivalence T A).functor.obj N) := by
  let e := Scheme.sfIntrinsicModuleEquivalence T A
  let F := SheafOfModules.siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (J := ProEt.topology T)
    (A := Scheme.proEtaleConstantRing T A) (e.functor.obj N)
  obtain ⟨t⟩ := proEtale_intrinsic_tensorRight_comparison T A N
  have equiv : exactFunctor _ _ (tensorRight N) ↔ exactFunctor _ _ F := by
    constructor
    · intro h
      have : PreservesFiniteLimits (tensorRight N) := h.1
      have : PreservesFiniteColimits (tensorRight N) := h.2
      let q : F ≅ e.inverse ⋙ tensorRight N ⋙ e.functor :=
        (Functor.leftUnitor F).symm ≪≫
          Functor.isoWhiskerRight e.counitIso.symm F ≪≫
          Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft e.inverse t
      have : PreservesFiniteLimits (e.inverse ⋙ tensorRight N ⋙ e.functor) :=
        comp_preservesFiniteLimits _ _
      have : PreservesFiniteColimits (e.inverse ⋙ tensorRight N ⋙ e.functor) :=
        comp_preservesFiniteColimits _ _
      exact ⟨preservesFiniteLimits_of_natIso q.symm,
        preservesFiniteColimits_of_natIso q.symm⟩
    · intro h
      have : PreservesFiniteLimits F := h.1
      have : PreservesFiniteColimits F := h.2
      have : PreservesFiniteLimits (e.functor ⋙ F) := comp_preservesFiniteLimits _ _
      have : PreservesFiniteColimits (e.functor ⋙ F) := comp_preservesFiniteColimits _ _
      have : PreservesFiniteLimits (tensorRight N ⋙ e.functor) :=
        preservesFiniteLimits_of_natIso t
      have : PreservesFiniteColimits (tensorRight N ⋙ e.functor) :=
        preservesFiniteColimits_of_natIso t
      exact ⟨preservesFiniteLimits_of_reflects_of_preserves _ e.functor,
        preservesFiniteColimits_of_reflects_of_preserves _ e.functor⟩
  constructor
  · intro h
    exact equiv.mp h.2
  · intro h
    have ht := equiv.mpr h
    exact ⟨(exactFunctor _ _).prop_of_iso
      (BraidedCategory.tensorLeftIsoTensorRight N).symm ht, ht⟩

private theorem fixed_flat_detect
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : IsCompl (Set.range i.base) (Set.range j.base))
    (H : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} A))
    (hj : ObjectProperty.flat ((ProEtale.upperStar (ModuleCat A) j).obj H))
    (hi : ObjectProperty.flat ((ProEtale.upperStar (ModuleCat A) i).obj H)) :
    ObjectProperty.flat H := by
  rw [ObjectProperty.flat_iff_preservesFiniteLimits,
    Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono]
  intro S hS
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨hS.exact.map_of_epi_of_preservesCokernel _ hS.epi_g inferInstance, ?_⟩
  have hm {Y : Scheme.{u}} (f : Y ⟶ X)
      (hf : ObjectProperty.flat ((ProEtale.upperStar (ModuleCat A) f).obj H)) :
      Mono ((ProEtale.upperStar (ModuleCat A) f).map
        ((MonoidalCategory.tensorLeft H).map S.f)) := by
    let F := ProEtale.upperStar (ModuleCat A) f
    have : PreservesFiniteLimits (MonoidalCategory.tensorLeft (F.obj H)) := hf.1.1
    have : Mono (F.map S.f) := F.map_mono S.f
    have : Mono (F.obj H ◁ F.map S.f) := (tensorLeft (F.obj H)).map_mono _
    change Mono (F.map (H ◁ S.f))
    rw [Functor.Monoidal.map_whiskerLeft]
    infer_instance
  have := hm i hi
  have := hm j hj
  exact Preadditive.mono_of_isZero_kernel _
    (ProEtale.isZero_of_isZero_upperStar_of_isCompl i j hij _
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ _))
      ((isZero_kernel_of_mono _).of_iso (PreservesKernel.iso _ _)))

/-- Flatness of module sheaves over the constant finite ring sheaf on the small pro-étale site
is detected on the two members of a complementary pair; extension by zero and closed direct
image preserve flatness. -/
theorem openClosedFlatness_proEtale
    (A : Type u) [CommRing A] [Finite A]
    {X U Z : Scheme.{u}} (j : U ⟶ X) (i : Z ⟶ X)
    [IsOpenImmersion j] [IsClosedImmersion i] [QuasiCompact j]
    (hij : Set.range i.base = (Set.range j.base)ᶜ)
    (H : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :
    (SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
        (R := Scheme.proEtaleConstantRing X A) H ↔
      (SheafOfModules.IsFlatOnSite (J := ProEt.topology U)
          (R := Scheme.proEtaleConstantRing U A)
          ((Scheme.proEtaleConstantRingPullback A j).obj H) ∧
        SheafOfModules.IsFlatOnSite (J := ProEt.topology Z)
          (R := Scheme.proEtaleConstantRing Z A)
          ((Scheme.proEtaleConstantRingPullback A i).obj H))) ∧
      (∀ L : Scheme.proEtaleRingModules U (Scheme.proEtaleConstantRing U A),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology U)
          (R := Scheme.proEtaleConstantRing U A) L →
        SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
          (R := Scheme.proEtaleConstantRing X A)
          ((Scheme.sfIntrinsicExtensionByZero j A).obj L)) ∧
      (∀ M : Scheme.proEtaleRingModules Z (Scheme.proEtaleConstantRing Z A),
        SheafOfModules.IsFlatOnSite (J := ProEt.topology Z)
          (R := Scheme.proEtaleConstantRing Z A) M →
        SheafOfModules.IsFlatOnSite (J := ProEt.topology X)
          (R := Scheme.proEtaleConstantRing X A)
          ((Scheme.proEtaleConstantRingPushforward A i).obj M)) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let e (T : Scheme.{u}) := Scheme.sfIntrinsicModuleEquivalence T A
  have flat_iff (T : Scheme.{u})
      (M : Scheme.proEtaleRingModules T (Scheme.proEtaleConstantRing T A)) :
      SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
          (R := Scheme.proEtaleConstantRing T A) M ↔
        ObjectProperty.flat ((e T).inverse.obj M) := by
    constructor
    · intro hM
      apply (intrinsic_flat_iff T A _).mpr
      exact site_flat_of_iso A ((e T).counitIso.app M) hM
    · intro hM
      exact site_flat_of_iso A ((e T).counitIso.app M).symm
        ((intrinsic_flat_iff T A _).mp hM)
  have pull_flat_iff {T : Scheme.{u}} (f : T ⟶ X)
      (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :
      SheafOfModules.IsFlatOnSite (J := ProEt.topology T)
          (R := Scheme.proEtaleConstantRing T A)
          ((Scheme.proEtaleConstantRingPullback A f).obj M) ↔
        ObjectProperty.flat ((ProEtale.upperStar B f).obj ((e X).inverse.obj M)) := by
    let q := (Scheme.openSquarePullbackModel A f).app M
    constructor
    · intro hM
      apply (intrinsic_flat_iff T A _).mpr
      exact site_flat_of_iso A q.symm hM
    · intro hM
      exact site_flat_of_iso A q ((intrinsic_flat_iff T A _).mp hM)
  have hc : IsCompl (Set.range i.base) (Set.range j.base) := by
    rw [hij]
    exact (isCompl_compl : IsCompl (Set.range j.base) _).symm
  have detect (M : Sheaf (ProEt.topology X) B)
      (hj : ObjectProperty.flat ((ProEtale.upperStar B j).obj M))
      (hi : ObjectProperty.flat ((ProEtale.upperStar B i).obj M)) :
      ObjectProperty.flat M := fixed_flat_detect _ j i hc M hj hi
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro hH
      have hf := (flat_iff X H).mp hH
      exact ⟨(pull_flat_iff j H).mpr (Functor.PreservesFlat.flat_obj hf),
        (pull_flat_iff i H).mpr (Functor.PreservesFlat.flat_obj hf)⟩
    · rintro ⟨hj, hi⟩
      exact (flat_iff X H).mpr
        (detect _ ((pull_flat_iff j H).mp hj) ((pull_flat_iff i H).mp hi))
  · intro L hL
    apply (intrinsic_flat_iff X A _).mp
    apply detect
    · exact ObjectProperty.prop_of_iso ObjectProperty.flat
        (asIso ((ProEtale.openImmersionLowerShriekUpperStarAdjunction B j).unit.app
          ((e U).inverse.obj L))) ((flat_iff U L).mp hL)
    · exact ObjectProperty.flat_of_isZero
        (ProEtale.isZero_upperStar_openImmersionLowerShriek B j i
          (Set.disjoint_iff_inter_eq_empty.mp hc.disjoint.symm) _)
  · intro M hM
    have hm : ObjectProperty.flat
        ((ProEtale.lowerStar B i).obj ((e Z).inverse.obj M)) := by
      apply detect
      · exact ObjectProperty.flat_of_isZero
          (ProEtale.isZero_upperStar_lowerStar_of_disjoint B i j hc.disjoint _)
      · exact ObjectProperty.prop_of_iso ObjectProperty.flat
          (asIso ((ProEtale.upperStarLowerStarAdjunction B i).counit.app
            ((e Z).inverse.obj M))).symm ((flat_iff Z M).mp hM)
    have heq : Scheme.proEtaleRingDirectImageMap i (Scheme.proEtaleConstantRing X A)
        (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRingComparison i A) =
          Scheme.proEtaleCoefficientDirectImageMap i A :=
      ((Scheme.proEtaleSheafAdjunction i CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
    let d : Scheme.proEtaleConstantRingPushforward A i ≅
        Scheme.proEtaleConstantModuleDirectImage i A :=
      SheafOfModules.pushforwardCongr (by rw [heq])
    let q := (Scheme.proEtaleConstantRingPushforward A i).mapIso
        ((e Z).counitIso.app M).symm ≪≫
      d.app ((e Z).functor.obj ((e Z).inverse.obj M)) ≪≫
      (Scheme.sfIntrinsicDirectImageComparison i A).app ((e Z).inverse.obj M)
    exact site_flat_of_iso A q ((intrinsic_flat_iff X A _).mp hm)

end AlgebraicGeometry

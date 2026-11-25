/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
import WeilConjectures.AlgebraicGeometry.DerivedLowerTruncationCycleFormula
import WeilConjectures.AlgebraicGeometry.DerivedSectionsLeftExactBottom

/-! # Identifying section cohomology with the quotient of section cycles

Source: Stacks Project, Tags 0AVW and 08D4, canonical comparison calculation.
(blueprint: lem-sc-kinjective-section-cycle-comparison).
-/

@[expose] public section
universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem section_cycles_cokernel_iso
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    ∃ a : cokernel (F.map (I.sc n).homologyData.left.f') ≅ J.homology n,
      cokernel.π (F.map (I.sc n).homologyData.left.f') ≫ a.hom =
        (J.sc n).liftCycles (F.map (I.sc n).homologyData.left.i) (by
          change F.map (I.sc n).homologyData.left.i ≫ F.map (I.sc n).g = 0
          rw [← F.map_comp, (I.sc n).homologyData.left.wi, F.map_zero]) ≫
          (J.sc n).homologyπ := by
  intro J
  let h := (I.sc n).homologyData.left
  have wi : F.map h.i ≫ F.map (I.sc n).g = 0 := by
    rw [← F.map_comp, h.wi, F.map_zero]
  let hi : IsLimit (KernelFork.ofι (F.map h.i) wi) :=
    KernelFork.mapIsLimit _ h.hi F
  have hf : hi.lift (KernelFork.ofι (F.map (I.sc n).f) (by
      rw [← F.map_comp, (I.sc n).zero, F.map_zero])) = F.map h.f' := by
    apply Fork.IsLimit.hom_ext hi
    calc
      _ = F.map (I.sc n).f := hi.fac _ WalkingParallelPair.zero
      _ = _ := by simp only [KernelFork.ι_ofι, ← F.map_comp, h.f'_i]
  let k : (J.sc n).LeftHomologyData :=
    { K := F.obj h.K
      H := cokernel (F.map h.f')
      i := F.map h.i
      π := cokernel.π (F.map h.f')
      wi := wi
      hi := hi
      wπ := by
        change hi.lift (KernelFork.ofι (F.map (I.sc n).f) _) ≫ _ = 0
        rw [hf]
        exact cokernel.condition _
      hπ := by
        have hff : hi.lift (KernelFork.ofι (J.sc n).f (J.sc n).zero) =
            F.map h.f' := hf
        exact CokernelCofork.isColimitOfIsColimitOfIff'
          (cokernelIsCokernel (F.map h.f')) _ (fun A g ↦ by rw [hff]) }
  refine ⟨k.homologyIso.symm, ?_⟩
  change k.π ≫ k.homologyIso.inv = _
  rw [k.π_comp_homologyIso_inv]
  congr 1
  apply (cancel_mono (J.sc n).iCycles).mp
  rw [k.cyclesIso_inv_comp_iCycles, ShortComplex.liftCycles_i]

/-- The canonical quotient of section cycles computes the homology sheaf sections
when the derived lower truncation projection is invertible in degree n.
Source: Stacks Project, Tag 0AVW, omitted cohomology calculation, and Tag 08D4(1).
(blueprint: lem-sc-kinjective-section-cycle-comparison).

Proof: Put A = truncLE n I and B = truncGE n A. Since F preserves kernels,
H^n(F(A)) maps isomorphically to H^n(F(I)). The natural comparison F(I) to
RF(Q(I)) is invertible because I is K-injective: a comparison to a K-injective
resolution is a homotopy equivalence, which an additive functor preserves.
The upper-truncation map RF(Q(A)) to RF(Q(I)) is invertible on H^n by left
exactness. Naturality therefore makes the comparison for A invertible on H^n.
The hypothesis and naturality of lower truncation give invertibility on H^n
of RF(Q(A)) to RF(Q(B)): upper truncation leaves H^n of RF unchanged. The complex
B has just H^n(I) in degree n; left exactness identifies bottom derived
cohomology with F(H^n(I)), and this is the natural comparison for B.
In the naturality square for A to B, the degree-n map is the projection of
cycles to their homology class. Uniqueness of kernels identifies the cycles
of F(I) with F of the chosen cycles of I. Their boundaries are exactly the
image of F(h.f'). Thus their homology is the displayed cokernel, and uniqueness
of cokernel descent identifies the composite isomorphism with the displayed
map, since its composite with cokernel.pi is F(h.pi). This is an identity of
canonical maps, not a choice of an unrelated isomorphism. This works for the
zero complex, every integer degree, and any left exact additive F. -/
theorem kInjective_section_cycle_comparison
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) [I.IsKInjective] (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor D n).map
      (F.rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))))) :
    IsIso (cokernel.desc (F.map (I.sc n).homologyData.left.f')
      (F.map (I.sc n).homologyData.left.π) (by
        rw [← F.map_comp, (I.sc n).homologyData.left.f'_π, F.map_zero])) := by
  let J := (F.mapHomologicalComplex (.up ℤ)).obj I
  let H := DerivedCategory.homologyFunctor D n
  let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
    ((DerivedCategory.homologyFunctorFactorsh D n).app
      ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
  let U := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  let q := F.rightDerivedFunctor.map
    ((DerivedCategory.quotientCompQhIso C).hom.app I ≫
      (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))
  obtain ⟨a, ha⟩ := section_cycles_cokernel_iso F I n
  obtain ⟨b, hb⟩ := derived_lower_truncation_cycle_formula F I n
  have : IsIso U := by dsimp [U]; infer_instance
  have : IsIso (H.map q) := by
    dsimp only [q]
    rw [F.rightDerivedFunctor.map_comp, H.map_comp]
    exact inferInstance
  have heq : cokernel.desc (F.map (I.sc n).homologyData.left.f')
      (F.map (I.sc n).homologyData.left.π) (by
        rw [← F.map_comp, (I.sc n).homologyData.left.f'_π, F.map_zero]) =
      a.hom ≫ e.hom ≫ H.map U ≫ H.map q ≫ b.hom := by
    apply (cancel_epi (cokernel.π (F.map (I.sc n).homologyData.left.f'))).mp
    rw [cokernel.π_desc]
    simp only [← Category.assoc]
    rw [ha]
    simp only [Category.assoc]
    simpa only [Category.assoc] using hb.symm
  rw [heq]
  infer_instance

end AlgebraicGeometry

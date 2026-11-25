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

import WeilConjectures.AlgebraicGeometry.LeftExactTruncationCycleFormula
import WeilConjectures.AlgebraicGeometry.DerivedLowerTruncationUnitBridge

/-! # The cycle formula for the bottom derived comparison

Source: Stacks Project, Tags 05TC (2), 0AVW and 08D4 (1).
(blueprint: lem-sc-derived-lower-truncation-cycle-formula).
-/

@[expose] public section

universe u v u' v' w w'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Bottom derived cohomology identifies the derived edge map on each cycle
with its image under the original functor. The complex need not be K-injective,
and no invertibility of the derived truncation map is assumed.

Source: Stacks Project, Tag 05TC (2), lemma-negative-vanishing; Tag 0AVW,
canonical cohomology calculation; Tag 08D4 (1).
(blueprint: lem-sc-derived-lower-truncation-cycle-formula).

Proof: Put A = truncLE n I and B = truncGE n A. The maps A to I and A to B
induce the usual maps on degree-n homology. Preservation of kernels identifies
the cycles of F(A) with F of the cycles of I. The boundary map into these
cycles is F of the induced boundary map. B is quasi-isomorphic to H^n(I)
placed in degree n. For a left exact functor, negative derived cohomology
vanishes; hence the upper-truncation inclusion into truncGE n I induces an
isomorphism in bottom derived degree n. Shift the single complex to degree
zero, where the derived unit identifies R^0 F with F. This constructs the
bottom comparison b. Naturality of the derived unit for A to I and A to B
identifies the map on a cycle with F of its homology class. Kernel uniqueness
identifies the lift in the displayed formula with F of the cycle inclusion;
the cokernel universal property identifies its class with F(h.pi). The
quotient and homotopy homology factor isomorphisms account for localization.
All steps use canonical comparisons, not an arbitrary bottom isomorphism.
Zero complexes and negative cutoff degrees obey the same kernel and shift
calculations. No boundedness of I and no exactness of F beyond kernels is used. -/
theorem derived_lower_truncation_cycle_formula
    {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v'} D]
    [Abelian C] [Abelian D] [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D]
    [EnoughInjectives C] [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    (I : CochainComplex C ℤ) (n : ℤ) :
    let J := (F.mapHomologicalComplex (.up ℤ)).obj I
    let H := DerivedCategory.homologyFunctor D n
    let e := ((HomotopyCategory.homologyFunctorFactors D (.up ℤ) n).app J).symm ≪≫
      ((DerivedCategory.homologyFunctorFactorsh D n).app
        ((HomotopyCategory.quotient D (.up ℤ)).obj J)).symm
    let c := (J.sc n).liftCycles (F.map (I.sc n).homologyData.left.i) (by
      change F.map (I.sc n).homologyData.left.i ≫ F.map (I.sc n).g = 0
      rw [← F.map_comp, (I.sc n).homologyData.left.wi, F.map_zero]) ≫
      (J.sc n).homologyπ
    let U := F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient C (.up ℤ)).obj I)
    let q := F.rightDerivedFunctor.map
      ((DerivedCategory.quotientCompQhIso C).hom.app I ≫
        (DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I))
    ∃ b : H.obj (F.rightDerivedFunctor.obj
        ((DerivedCategory.TStructure.t.truncGE n).obj (DerivedCategory.Q.obj I))) ≅
        F.obj (I.sc n).homologyData.left.H,
      c ≫ e.hom ≫ H.map U ≫ H.map q ≫ b.hom =
        F.map (I.sc n).homologyData.left.π := by
  dsimp only
  obtain ⟨a, ha⟩ := leftExact_truncation_cycle_formula F I n
  obtain ⟨d, hd⟩ := derived_lower_truncation_unit_bridge F I n
  refine ⟨d.symm ≪≫ a, ?_⟩
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc] at hd
  erw [reassoc_of% hd]
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using ha

end AlgebraicGeometry

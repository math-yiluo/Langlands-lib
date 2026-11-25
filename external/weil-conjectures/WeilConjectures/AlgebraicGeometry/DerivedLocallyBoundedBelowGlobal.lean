/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Topology.Sheaves.Sheaf

/-! # Uniform lower bounds on a quasi-compact scheme

Source: Stacks Project, Tag 0A6H, proof of clause (1).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/-- A locally bounded-below derived object on a Noetherian scheme is bounded below.
Source: Stacks Project, Tag 0A6H, proof of clause (1).
(blueprint: lem-sc-derived-locally-bounded-below-global).

Proof: Choose, at each point, the given open neighbourhood and its lower bound.
Quasi-compactness of the Noetherian scheme gives a finite subcover. Choose an integer
no larger than every bound in this finite cover (zero if the cover is empty). For each
smaller degree, the cohomology sheaf restricts to zero on every member of the cover.
Sheaf separatedness implies that all its sections are zero, hence it is a zero object.
The cohomological characterization of the canonical t-structure gives the assertion.
The empty scheme causes no exception: all module sheaves on it are zero. -/
theorem derivedLocallyBoundedBelowGlobal (Y : Scheme.{u}) [IsNoetherian Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory Y)
    (hlocal : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∃ a : ℤ, ∀ n : ℤ, n < a →
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E))) :
    ∃ a : ℤ, E.IsGE a := by
  classical
  choose U hx a hv using hlocal
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun y : Y ↦ (U y : Set Y)) (fun y ↦ (U y).isOpen) (by
      intro y _
      exact Set.mem_iUnion.mpr ⟨y, hx y⟩)
  have hmin : ∃ b : ℤ, ∀ y ∈ s, b ≤ a y := by
    clear hs
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp⟩
    | @insert y s hy ih =>
      obtain ⟨b, hb⟩ := ih
      refine ⟨min (a y) b, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hb z hz)
  obtain ⟨b, hb⟩ := hmin
  refine ⟨b, (DerivedCategory.isGE_iff E b).mpr ?_⟩
  intro n hn
  let M := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj E
  apply (IsZero.iff_id_eq_zero M).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro V
  ext x
  change x = 0
  apply TopCat.Presheaf.IsSheaf.section_ext M.isSheaf
  intro z hz
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ z))
  obtain ⟨hys, hzy⟩ := Set.mem_iUnion.mp hy
  let W := V.unop ⊓ U y
  have hzero := hv y n (hn.trans_le (hb y hys))
  let WO : Over (U y) := Over.mk (homOfLE (show W ≤ U y from inf_le_right))
  have hid := (IsZero.iff_id_eq_zero _).mp hzero
  refine ⟨W, inf_le_left, ⟨hz, hzy⟩, ?_⟩
  have hh := congrArg
    (fun f ↦ (f.val.app (Opposite.op WO)).hom
      (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op x)) hid
  change (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom x = 0 at hh
  change (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom x =
    (M.val.map (homOfLE (show W ≤ V.unop from inf_le_left)).op).hom 0
  simpa only [map_zero] using hh

end AlgebraicGeometry

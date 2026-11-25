/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-! # The homology edge of a left exact functor

Source: Stacks Project, cohomology.tex, Tag 0BKJ: the map from cycles to their
cohomology classes, applied after a functor preserving kernels.
-/

@[expose] public section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.ShortComplex

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

/-- Kernel preservation identifies the mapped cycle object with the cycles after mapping.
Source: Stacks, Tag 0BKJ (blueprint: def-weil-pbc-left-exact-homology-edge). -/
noncomputable def leftExactCyclesIso (S : ShortComplex C) :
    F.obj S.cycles ≅ (S.map F).cycles :=
  (S.map F).isoCyclesOfIsLimit (KernelFork.mapIsLimit _ S.cyclesIsKernel F)

@[reassoc]
theorem leftExactCyclesIso_inv_i (S : ShortComplex C) :
    (leftExactCyclesIso F S).inv ≫ F.map S.iCycles = (S.map F).iCycles :=
  (S.map F).isoCyclesOfIsLimit_inv_ι _

@[reassoc]
theorem toCycles_leftExactCyclesIso_inv (S : ShortComplex C) :
    (S.map F).toCycles ≫ (leftExactCyclesIso F S).inv = F.map S.toCycles := by
  apply (cancel_mono (F.map S.iCycles)).1
  rw [Category.assoc, leftExactCyclesIso_inv_i, toCycles_i, ← F.map_comp, toCycles_i]
  rfl

/-- The canonical homology edge of a left exact additive functor. Only kernels are
preserved: the map out of homology is supplied by its cokernel universal property.
Source: Stacks, Tag 0BKJ (blueprint: def-weil-pbc-left-exact-homology-edge). -/
noncomputable def leftExactHomologyEdge (S : ShortComplex C) :
    (S.map F).homology ⟶ F.obj S.homology :=
  (S.map F).descHomology
    ((leftExactCyclesIso F S).inv ≫ F.map S.homologyπ) (by
      rw [← Category.assoc, toCycles_leftExactCyclesIso_inv, ← F.map_comp,
        toCycles_comp_homologyπ, F.map_zero])

@[reassoc]
theorem homologyπ_leftExactHomologyEdge (S : ShortComplex C) :
    (S.map F).homologyπ ≫ leftExactHomologyEdge F S =
      (leftExactCyclesIso F S).inv ≫ F.map S.homologyπ :=
  (S.map F).π_descHomology _ _

@[reassoc]
theorem leftExactCyclesIso_inv_naturality {S S' : ShortComplex C} (a : S ⟶ S') :
    cyclesMap (F.mapShortComplex.map a) ≫ (leftExactCyclesIso F S').inv =
      (leftExactCyclesIso F S).inv ≫ F.map (cyclesMap a) := by
  dsimp only [Functor.mapShortComplex] at *
  apply (cancel_mono (F.map S'.iCycles)).1
  rw [Category.assoc, leftExactCyclesIso_inv_i, cyclesMap_i,
    Category.assoc, ← F.map_comp, cyclesMap_i, F.map_comp,
    ← Category.assoc, leftExactCyclesIso_inv_i]

/-- Naturality of the edge, without assuming that F preserves cokernels.
Source: Stacks, Tag 0BKJ (blueprint: def-weil-pbc-left-exact-homology-edge). -/
@[reassoc]
theorem leftExactHomologyEdge_naturality {S S' : ShortComplex C} (a : S ⟶ S') :
    homologyMap (F.mapShortComplex.map a) ≫ leftExactHomologyEdge F S' =
      leftExactHomologyEdge F S ≫ F.map (homologyMap a) := by
  have hn := leftExactCyclesIso_inv_naturality F a
  dsimp only [Functor.mapShortComplex] at *
  apply (cancel_epi (S.map F).homologyπ).1
  rw [← Category.assoc, homologyπ_naturality, Category.assoc,
    homologyπ_leftExactHomologyEdge, ← Category.assoc,
    hn, Category.assoc,
    ← F.map_comp, ← homologyπ_naturality, F.map_comp]
  simp only [homologyπ_leftExactHomologyEdge_assoc]

end CategoryTheory.ShortComplex

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.AbelianCechComparisonConstruction
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Ext cocycles give section cycles

Source: Stacks Project, Tags 01EQ and 01FD.
(blueprint: lem-pc-ext-section-cycle)
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] cohomologyHasSheafify cohomologyHasExt

/-- An Ext cocycle determines a section cycle by the constant-sheaf adjunction.
Source: Stacks Project, Tag 01EQ, resolution sections; Mathlib's adjunction
and the universal property of cycles. (blueprint: lem-pc-ext-section-cycle)

Proof: Apply the adjunction to a. Naturality takes its composite with the
resolution differential to the composite with the section differential, which
is zero since a is a cocycle. Factor the resulting morphism through cycles
and evaluate on the generator 1 of the lifted integers. -/
theorem abelianCech_ext_section_cycle
    {X : Scheme.{u}} {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}}
    (I : InjectiveResolution F) (q : ℕ)
    (a : (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    ∃ z : (abelianCechSections I).cycles q,
      ((constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
        isTerminalTop).homEquiv _ _ a) (ULift.up 1) =
          (abelianCechSections I).iCycles q z := by
  let adj := constantSheafAdj (Opens.grothendieckTopology X) AddCommGrpCat.{u}
    isTerminalTop
  let t := adj.homEquiv _ _ a
  have ht : t ≫ (abelianCechSections I).d q (q + 1) = 0 := by
    change adj.homEquiv _ _ a ≫
      ((sheafSections (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (op ⊤)).map
        (I.cocomplex.d q (q + 1)) = 0
    rw [← adj.homEquiv_naturality_right]
    rw [ha]
    exact adj.homAddEquiv_zero _ _
  refine ⟨(abelianCechSections I).liftCycles t (q + 1) (by simp) ht (ULift.up 1), ?_⟩
  symm
  exact ConcreteCategory.congr_hom
    ((abelianCechSections I).liftCycles_i t (q + 1) (by simp) ht) (ULift.up 1)

end AlgebraicGeometry.Scheme.Modules

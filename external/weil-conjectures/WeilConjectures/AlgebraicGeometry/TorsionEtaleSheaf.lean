/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import WeilConjectures.Data.PNat.DvdOrder

/-!
# Torsion abelian sheaves on the small étale site

Source: the blueprint of the Weil conjectures, chapter `chap-Proper-base-change`, unit
`sec-Torsion-sheaves-and-acyclicity` (blueprint: definition-torsion-sheaves); Stacks Project, Etale
cohomology, Section 0DDB.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The kernel inclusion for positive integers ordered by divisibility. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: definition-torsion-sheaves). -/
theorem torsionKernelTransition_condition {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n m : PNat.DvdOrder) (hnm : n.val ∣ m.val) :
    kernel.ι (n.val • 𝟙 F) ≫ (m.val • 𝟙 F) = 0 := by
  obtain ⟨r, hr⟩ := hnm
  rw [hr, mul_nsmul, Preadditive.comp_nsmul, kernel.condition,
    nsmul_zero]

/-- The canonical kernel inclusions satisfy the identity law. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: definition-torsion-sheaves). -/
theorem torsionKernelTransition_id {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (n : PNat.DvdOrder) :
    kernel.lift (n.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n n (dvd_refl n.val)) = 𝟙 _ := by
  apply (cancel_mono (kernel.ι (n.val • 𝟙 F))).1
  simp only [kernel.lift_ι, Category.id_comp]

/-- The canonical kernel inclusions satisfy the composition law. Source: blueprint
`sec-proper-base-change/sk-def-pbc`, statement (blueprint: definition-torsion-sheaves). -/
theorem torsionKernelTransition_comp {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})
    (n m k : PNat.DvdOrder) (hnm : n.val ∣ m.val) (hmk : m.val ∣ k.val) :
    kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n m hnm) ≫
      kernel.lift (k.val • 𝟙 F) (kernel.ι (m.val • 𝟙 F))
        (torsionKernelTransition_condition F m k hmk) =
      kernel.lift (k.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n k (dvd_trans hnm hmk)) := by
  apply (cancel_mono (kernel.ι (k.val • 𝟙 F))).1
  simp only [Category.assoc, kernel.lift_ι]

/-- Source: blueprint `sec-proper-base-change/sk-def-pbc`, statement
(blueprint: definition-torsion-sheaves). For a sheaf `F` of abelian groups on the
small étale site of `T`, form the filtered diagram indexed by positive natural numbers ordered
by divisibility, whose value at `n` is `ker (n : F ⟶ F)` and whose transition maps are the
canonical inclusions. The sheaf `F` is torsion when the canonical map from the colimit of this
diagram to `F`, induced by the kernel inclusions, is an isomorphism (Stacks Project, Section
0DDB). The construction follows the node proof step by step: divisibility gives the positive
integer index category; the kernel inclusion condition gives transition maps; the identity and
composition lemmas give a functor `D`; the kernel inclusions give a cocone `c`; and
`colimit.desc D c` is the canonical map whose `IsIso` property defines torsion. -/
noncomputable def IsTorsionAbelianSheaf {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) : Prop :=
  let D : PNat.DvdOrder ⥤ Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1} :=
    { obj := fun n => kernel (n.val • 𝟙 F)
      map := fun {n m} hnm => kernel.lift (m.val • 𝟙 F) (kernel.ι (n.val • 𝟙 F))
        (torsionKernelTransition_condition F n m hnm.down.down)
      map_id := by
        intro n
        exact torsionKernelTransition_id F n
      map_comp := by
        intro n m k hnm hmk
        exact (torsionKernelTransition_comp F n m k hnm.down.down hmk.down.down).symm }
  let c : Cocone D :=
    { pt := F
      ι := { app := fun n => kernel.ι (n.val • 𝟙 F)
             naturality := by
               intro n m hnm
               simp [D] } }
  IsIso (colimit.desc D c)

end AlgebraicGeometry.Scheme

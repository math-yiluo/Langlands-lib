/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-! # Equality of module subsheaves checked on an open cover

Source: Stacks Project, Lemma 087X, reduction to an affine open cover, and the sheaf axiom.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem comp_cokernel_eq_zero_on_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {A B M : X.Modules} (f : A ⟶ M) (g : B ⟶ M)
    (h : ∀ (i : ι) (W : X.Opens), W ≤ U i →
      Set.range (g.app W) ⊆ Set.range (f.app W)) :
    g ≫ cokernel.π f = 0 := by
  apply Scheme.Modules.hom_ext
  intro W
  ext b
  let Q : TopCat.Sheaf AddCommGrpCat.{u} X :=
    ⟨(cokernel f).presheaf, (cokernel f).isSheaf⟩
  apply Q.eq_of_locally_eq' (fun i ↦ W ⊓ U i) W (fun _ ↦ homOfLE inf_le_left)
    (by
      intro x hx
      obtain ⟨i, hi⟩ := hU x
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hx, hi⟩)
  intro i
  have hb : g.app (W ⊓ U i) (B.presheaf.map (homOfLE inf_le_left).op b) ∈
      Set.range (f.app (W ⊓ U i)) :=
    h i (W ⊓ U i) inf_le_right ⟨_, rfl⟩
  obtain ⟨a, ha⟩ := hb
  have hz := congrArg (fun k : A ⟶ cokernel f ↦ k.app (W ⊓ U i) a)
    (cokernel.condition f)
  change (cokernel.π f).app (W ⊓ U i) (f.app (W ⊓ U i) a) = 0 at hz
  change (cokernel f).presheaf.map (homOfLE inf_le_left).op
    ((g ≫ cokernel.π f).mapPresheaf.app (op W) b) =
    (cokernel f).presheaf.map (homOfLE inf_le_left).op 0
  rw [map_zero, ← ConcreteCategory.comp_apply,
    ← (g ≫ cokernel.π f).mapPresheaf.naturality]
  change (cokernel.π f).app (W ⊓ U i)
    (g.app (W ⊓ U i) (B.presheaf.map (homOfLE inf_le_left).op b)) = 0
  rw [← ha]
  exact hz

/-- Equal section ranges locally on a cover identify two module subobjects.

Source: Stacks Project, Lemma 087X, affine-local verification of kernel image equalities.
(blueprint: new-module-subobject-eq-on-cover).

Proof: Range inclusion on W ∩ U_i makes g followed by the cokernel projection of f
zero there: every value of g is a value of f, which the projection kills. Apply the
separatedness part of the sheaf axiom for the cokernel to the cover (W ∩ U_i)_i.
Naturality identifies the restricted composite with the composite on the restriction,
so g followed by that projection is zero globally. A monomorphism in an abelian
category is the kernel of its cokernel; Abelian.monoLift therefore factors g through f.
This gives Subobject.mk g ≤ Subobject.mk f. Interchange f and g for the reverse
inclusion and use antisymmetry. For an empty cover, the covering condition forces X
empty and sheaf separatedness still applies. Neither quasi-coherence nor finiteness
nor Noetherian hypotheses are needed. -/
theorem module_subobject_eq_on_cover {X : Scheme.{u}} {ι : Type v}
    (U : ι → X.Opens) (hU : ∀ x : X, ∃ i, x ∈ U i)
    {A B M : X.Modules} (f : A ⟶ M) (g : B ⟶ M) [Mono f] [Mono g]
    (h : ∀ (i : ι) (W : X.Opens), W ≤ U i →
      Set.range (f.app W) = Set.range (g.app W)) :
    Subobject.mk f = Subobject.mk g := by
  have hfg := comp_cokernel_eq_zero_on_cover U hU g f
    (fun i W hW ↦ (h i W hW).le)
  have hgf := comp_cokernel_eq_zero_on_cover U hU f g
    (fun i W hW ↦ (h i W hW).ge)
  apply le_antisymm
  · exact Subobject.mk_le_mk_of_comm (Abelian.monoLift g f hfg)
      (Abelian.monoLift_comp g f hfg)
  · exact Subobject.mk_le_mk_of_comm (Abelian.monoLift f g hgf)
      (Abelian.monoLift_comp f g hgf)

end AlgebraicGeometry

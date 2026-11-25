/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PicardDerivedModelSections
@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
/-- The global-section map of the residue lift is section evaluation.
Source: Mathlib/AlgebraicGeometry/Stalk.lean,
Opens.fromSpecStalkOfMem_toSpecΓ; Mathlib/AlgebraicGeometry/ResidueField.lean,
the definition of Scheme.evaluation. Used in the degree-zero argument of Stacks 0BF2.
(blueprint: lem-sc-picard-tensor-frame-restriction-evaluation)

Proof: Cancel the open immersion to identify the residue lift with Spec of the
residue quotient followed by the stalk lift. The composite with U.toSpecΓ is
Spec of the germ map followed by residue. Apply global sections, use naturality
of ΓSpecIso, and evaluate the resulting ring-hom equality on ΓSpecIso.inv a.
The inverse/hom cancellation gives germ followed by residue, which is the
definition of evaluation. This applies to every section, including zero and one. -/
theorem picardResidueLift_appTop_eval (W : Scheme.{v}) (w : W)
    (U : W.Opens) (hwU : w ∈ U) (a : Γ(W, U)) :
    (ΓSpecIso (W.residueField w)).hom
      ((picardResidueLift W w U hwU).appTop (U.topIso.inv a)) =
        W.evaluation U w hwU a := by
  have hp : picardResidueLift W w U hwU =
      Spec.map (W.residue w) ≫ U.fromSpecStalkOfMem w hwU := by
    apply (cancel_mono U.ι).mp
    rw [picardResidueLift_comp, Category.assoc, Opens.fromSpecStalkOfMem_ι]
    rfl
  have hc : picardResidueLift W w U hwU ≫ U.toSpecΓ =
      Spec.map (W.presheaf.germ U w hwU ≫ W.residue w) := by
    rw [hp, Category.assoc, Opens.fromSpecStalkOfMem_toSpecΓ, ← Spec.map_comp]
  have h := congrArg (fun g ↦ g.appTop ≫ (ΓSpecIso (W.residueField w)).hom) hc
  simp only [Hom.comp_appTop, Opens.toSpecΓ_appTop, Category.assoc,
    ΓSpecIso_naturality] at h
  have he := ConcreteCategory.congr_hom h ((ΓSpecIso Γ(W, U)).inv a)
  have heval : W.evaluation U w hwU a = W.residue w (W.presheaf.germ U w hwU a) := rfl
  rw [heval]
  simpa only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply] using he

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange

/-! # Reflection of local generation along tensor pullback

Source: Stacks Project, Modules, Tag 01CY, the local coefficient criterion.
-/

@[expose] public section
set_option autoImplicit false
universe v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem generatesAt_iso {X : Scheme.{v}} {A B : X.Modules} (q : A ≅ B)
    (a : Γ(A, ⊤)) (x : X) (h : GeneratesAt a x) :
    GeneratesAt (q.hom.app ⊤ a) x := by
  obtain ⟨U, hx, hU⟩ := h
  refine ⟨U, hx, ?_⟩
  rw [← Hom.app_presheaf_map]
  exact hU.app_hom q


/-- If the pullback of a section, transported by a module isomorphism, generates at y,
the original section generates at its image.

Source: Stacks Project, Modules, Tag 01CY (local coefficient criterion).
(blueprint: lem-sc-tensor-pullback-generator-reflection)

Proof: Trivialize M near j(y), writing σ = a e. Pullback sends this expression to
j^♯(a) times the pulled-back basis, and a module isomorphism preserves free generators.
Generation of the transported section implies that j^♯(a) is a unit in the local ring
at y. The stalk map is local, so a is a unit at j(y). On the basic open of a the
original section is a free generator. This works for any scheme morphism, without
properness, flatness or a fibre hypothesis. -/
theorem tensorPullback_generatesAt_reflects {Y Z : Scheme.{v}} (j : Y ⟶ Z)
    (M : Z.Modules) [M.IsInvertible] (N : Y.Modules)
    (e : (tensorPullback j).obj M ≅ N) (σ : Γ(M, ⊤)) (τ : Γ(N, ⊤))
    (hστ : e.hom.app ⊤
      (((tensorPullback j).obj M).presheaf.map (homOfLE j.preimage_top.ge).op
        (((Classical.choose (exists_tensorPullbackAdjunction j)).unit.app M).val.app
          (op ⊤) σ)) = τ)
    (y : Y) (hτ : GeneratesAt τ y) : GeneratesAt σ (j y) := by
  classical
  let a := Classical.choose (exists_tensorPullbackAdjunction j)
  let q := (a.leftAdjointUniq (pullbackPushforwardAdjunction j)).app M
  let t : Γ((tensorPullback j).obj M, ⊤) :=
    ((tensorPullback j).obj M).presheaf.map (homOfLE j.preimage_top.ge).op
      ((a.unit.app M).val.app (op ⊤) σ)
  have ht : GeneratesAt t y := by
    have h := generatesAt_iso e.symm τ y hτ
    rw [← hστ] at h
    change GeneratesAt (e.inv.app ⊤ (e.hom.app ⊤ t)) y at h
    simpa only [← ConcreteCategory.comp_apply, ← Hom.comp_app, e.hom_inv_id,
      Hom.id_app, ConcreteCategory.id_apply] using h
  have hq : q.hom.app ⊤ t = pullbackTopSection j σ := by
    dsimp only [t, pullbackTopSection]
    erw [Hom.app_presheaf_map]
    have hu := a.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction j) M
    have hs := congrArg (fun z ↦ z.val.app (op (⊤ : Z.Opens)) σ) hu
    exact congrArg
      (fun z ↦ ((pullback j).obj M).presheaf.map
        (homOfLE j.preimage_top.ge).op z) hs
  have hp := generatesAt_iso q t y ht
  rw [hq] at hp
  have : SheafOfModules.IsInvertible.{v, v, v} M :=
    IsInvertible.sheafOfModules_isInvertible M
  have hs : GeneratesAt
      (∑ r ∈ ({()} : Finset Unit), (1 : Γ(Y, ⊤)) • pullbackTopSection j σ) y := by
    simpa using hp
  obtain ⟨r, hr, hgen⟩ := exists_generatesAt_of_generatesAt_sum j
    ({()} : Finset Unit) (fun _ ↦ (1 : Γ(Y, ⊤))) (fun _ ↦ σ) hs
  exact hgen

end AlgebraicGeometry.Scheme.Modules

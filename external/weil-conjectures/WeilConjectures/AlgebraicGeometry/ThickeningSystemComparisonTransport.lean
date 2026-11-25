/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.TensorPullback
import WeilConjectures.AlgebraicGeometry.ClosedImmersionPushforwardFullyFaithful
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

-- Naturality extends to every map between reflected objects, since the counit is invertible.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem reflector_endomorphism_naturality
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (adj : L ⊣ R) (hc : ∀ Z, IsIso (adj.counit.app Z))
    (a : L ⟶ L) {A B : C} (v : L.obj A ⟶ L.obj B) :
    a.app A ≫ v = v ≫ a.app B := by
  have h (X : C) :
      adj.counit.app (L.obj X) ≫ a.app X =
        a.app (R.obj (L.obj X)) ≫ adj.counit.app (L.obj X) := by
    let := hc (L.obj X)
    have hi : IsIso (L.map (adj.unit.app X)) := by
      have he : L.map (adj.unit.app X) = inv (adj.counit.app (L.obj X)) := by
        apply (cancel_mono (adj.counit.app (L.obj X))).1
        rw [adj.left_triangle_components X, IsIso.inv_hom_id]
        rfl
      rw [he]
      infer_instance
    apply (cancel_epi (L.map (adj.unit.app X))).1
    calc
      L.map (adj.unit.app X) ≫ (adj.counit.app (L.obj X) ≫ a.app X) = a.app X := by
        rw [← Category.assoc, adj.left_triangle_components X]
        exact Category.id_comp _
      _ = (a.app X ≫ L.map (adj.unit.app X)) ≫ adj.counit.app (L.obj X) := by
        rw [Category.assoc, adj.left_triangle_components X, Category.comp_id]
      _ = L.map (adj.unit.app X) ≫
          (a.app (R.obj (L.obj X)) ≫ adj.counit.app (L.obj X)) := by
        exact (congrArg (fun f ↦ f ≫ adj.counit.app (L.obj X))
          (a.naturality (adj.unit.app X))).symm.trans (Category.assoc _ _ _)
  let := hc (L.obj A)
  apply (cancel_epi (adj.counit.app (L.obj A))).1
  calc
    adj.counit.app (L.obj A) ≫ (a.app A ≫ v) =
        a.app (R.obj (L.obj A)) ≫ (adj.counit.app (L.obj A) ≫ v) := by
      rw [← Category.assoc, h, Category.assoc]
    _ = a.app (R.obj (L.obj A)) ≫
        (L.map (R.map v) ≫ adj.counit.app (L.obj B)) := by
      rw [← adj.counit_naturality v]
    _ = L.map (R.map v) ≫
        (a.app (R.obj (L.obj B)) ≫ adj.counit.app (L.obj B)) := by
      rw [← Category.assoc, ← a.naturality (R.map v), Category.assoc]
    _ = adj.counit.app (L.obj A) ≫ (v ≫ a.app B) := by
      rw [← h, ← Category.assoc, adj.counit_naturality v, Category.assoc]

/-- Comparison isomorphisms induce the same compatible-family subtype.
Source: Stacks Project, Lemma 087T and Remark 088F.
(blueprint: lem-weil-pbc-thickening-system-comparison-transport).
-/
theorem compatible_family_comparison_equiv
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (hj : ∀ n, IsClosedImmersion (j n))
    (c d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n))
    (F G : CoherentModules X) :
    ∃ e : ({v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (d n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F.obj}) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (c n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F.obj},
      ∀ v, (e v).val = v.val := by
  classical
  have hcompat (v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
      (Scheme.Modules.tensorPullback (j n)).obj F.obj) :
      (∀ n, (d n).hom.app G.obj ≫ v n =
        (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F.obj) ↔
      (∀ n, (c n).hom.app G.obj ≫ v n =
        (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (c n).hom.app F.obj) := by
    apply forall_congr'
    intro n
    let : IsClosedImmersion (j n) := hj n
    let adj := Classical.choice (Scheme.Modules.nonempty_tensorPullbackAdjunction (j n))
    have hc : ∀ Z, IsIso (adj.counit.app Z) :=
      (closedImmersion_pushforward_fullyFaithful (j n)).1
    let a := (c n).symm ≪≫ d n
    have ha := reflector_endomorphism_naturality adj hc a.hom (v n)
    have hd (M : X.Modules) : (d n).hom.app M = (c n).hom.app M ≫ a.hom.app M := by
      simp [a]
    rw [hd G.obj, hd F.obj, Category.assoc, ha, ← Category.assoc,
      ← Category.assoc, cancel_mono]
  refine ⟨Equiv.subtypeEquivRight hcompat, ?_⟩
  intro v
  rfl

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.CoherentThickeningSystem
public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Componentwise conjugation identifies system arrows with families compatible with `d`.
Source: Stacks Project, Remark 088F and Lemma 087T.
(blueprint: lem-weil-pbc-thickening-system-hom-transport-core).
-/
theorem thickeningSystem_hom_transport_d
    {X : Scheme.{u}} {T : ℕ → Scheme.{u}} {i : ∀ n, T n ⟶ T (n + 1)}
    (j : ∀ n, T n ⟶ X) (d : ∀ n, Scheme.Modules.tensorPullback (j (n + 1)) ⋙
      Scheme.Modules.tensorPullback (i n) ≅ Scheme.Modules.tensorPullback (j n))
    (R : CoherentModules X ⥤ CoherentThickeningSystem T i)
    (r : ∀ n, R ⋙ CoherentThickeningSystem.evaluation T i n ≅
      ObjectProperty.ι (RingedSpace.IsCoherent X.toRingedSpace) ⋙
        Scheme.Modules.tensorPullback (j n))
    (hr : ∀ (F : CoherentModules X) (n : ℕ),
      ((R.obj F).comparison n).hom ≫ (r n).hom.app F =
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) ≫
          (d n).hom.app F.obj)
    (F G : CoherentModules X) :
    ∃ e : (R.obj G ⟶ R.obj F) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (d n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫ (d n).hom.app F.obj},
      ∀ w : G ⟶ F, e (R.map w) =
        ⟨fun n ↦ (Scheme.Modules.tensorPullback (j n)).map w.hom,
          fun n ↦ ((d n).hom.naturality w.hom).symm⟩ := by
  let forward (a : R.obj G ⟶ R.obj F) :=
    fun n ↦ (r n).inv.app G ≫ a.app n ≫ (r n).hom.app F
  have hf (a : R.obj G ⟶ R.obj F) (n : ℕ) :
      (d n).hom.app G.obj ≫ forward a n =
        (Scheme.Modules.tensorPullback (i n)).map (forward a (n + 1)) ≫
          (d n).hom.app F.obj := by
    apply (cancel_epi ((Scheme.Modules.tensorPullback (i n)).map
      ((r (n + 1)).hom.app G))).1
    dsimp [forward]
    simp only [Functor.map_comp, ← Category.assoc]
    rw [← hr G n]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.assoc,
      Iso.hom_inv_id_app, cancelIso, CoherentThickeningSystem.evaluation, Category.id_comp]
    rw [← Category.assoc, a.compatibility n, Category.assoc, ← hr F n]
  let backward (v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
      (Scheme.Modules.tensorPullback (j n)).obj F.obj) :=
    fun n ↦ (r n).hom.app G ≫ v n ≫ (r n).inv.app F
  have hb (v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
      (Scheme.Modules.tensorPullback (j n)).obj F.obj)
      (hv : ∀ n, (d n).hom.app G.obj ≫ v n =
        (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫
          (d n).hom.app F.obj) (n : ℕ) :
      ((R.obj G).comparison n).hom ≫ backward v n =
        (Scheme.Modules.tensorPullback (i n)).map (backward v (n + 1)) ≫
          ((R.obj F).comparison n).hom := by
    apply (cancel_mono ((r n).hom.app F)).1
    dsimp [backward]
    simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app]
    simp only [Functor.comp_obj, ObjectProperty.ι_obj, Category.comp_id]
    rw [← Category.assoc, hr G n, Category.assoc]
    rw [hr F n]
    have hc : (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).inv.app F) ≫
        (Scheme.Modules.tensorPullback (i n)).map ((r (n + 1)).hom.app F) =
          𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app]
      exact (Scheme.Modules.tensorPullback (i n)).map_id _
    rw [← Category.assoc ((Scheme.Modules.tensorPullback (i n)).map
      ((r (n + 1)).inv.app F)), hc, Category.id_comp, hv n]
  let e : (R.obj G ⟶ R.obj F) ≃
      {v : ∀ n, (Scheme.Modules.tensorPullback (j n)).obj G.obj ⟶
        (Scheme.Modules.tensorPullback (j n)).obj F.obj |
        ∀ n, (d n).hom.app G.obj ≫ v n =
          (Scheme.Modules.tensorPullback (i n)).map (v (n + 1)) ≫
            (d n).hom.app F.obj} :=
    { toFun := fun a ↦ ⟨forward a, hf a⟩
      invFun := fun v ↦ ⟨backward v.val, hb v.val v.property⟩
      left_inv := by
        intro a
        have h : backward (forward a) = a.app := by
          funext n
          simp [forward, backward, Category.assoc, CoherentThickeningSystem.evaluation]
        cases a
        simp_all
      right_inv := by
        intro v
        apply Subtype.ext
        funext n
        simp [forward, backward, Category.assoc, CoherentThickeningSystem.evaluation] }
  refine ⟨e, ?_⟩
  intro w
  apply Subtype.ext
  funext n
  change (r n).inv.app G ≫ (R.map w).app n ≫ (r n).hom.app F = _
  have h := (r n).hom.naturality w
  change (R.map w).app n ≫ (r n).hom.app F =
    (r n).hom.app G ≫ (Scheme.Modules.tensorPullback (j n)).map w.hom at h
  rw [h]
  simp

end AlgebraicGeometry

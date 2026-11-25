/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.FpqcSingletonFullyFaithful
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver
import Mathlib.CategoryTheory.Sites.LocalProperties
import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# Gluing a representation after effective descent

## References

* Stacks Project, Tags 03RV and 02W5, gluing the represented sheaf
* Stacks Project, Tag 03RV, final identification of the descended representation
* Tag 02W5, descent from a representable sheaf
-/

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
private theorem iso_of_over_compatible
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    (E G : Sheaf J (Type (u + 1))) (U : C)
    (hc : J.CoversTop (fun _ : PUnit.{1} ↦ U))
    (e : (E.over U).obj ≅ (G.over U).obj)
    (he : ∀ (W : C) (a b : W ⟶ U),
      e.hom.app (op (Over.mk a)) = e.hom.app (op (Over.mk b))) :
    Nonempty (E.obj ≅ G.obj) := by
  classical
  let l (W : C) (a : W ⟶ U) : E.obj.obj (op W) ⟶ G.obj.obj (op W) := e.hom.app (op (Over.mk a))
  have hn {V W : C} (r : W ⟶ V) (a : V ⟶ U) (b : W ⟶ U) :
      E.obj.map r.op ≫ l W b = l V a ≫ G.obj.map r.op := by
    change E.obj.map r.op ≫ e.hom.app (op (Over.mk b)) = _
    rw [← he W (r ≫ a) b]
    exact e.hom.naturality (Over.homMk r : Over.mk (r ≫ a) ⟶ Over.mk a).op
  let a {W : C} (I : (hc.cover W).Arrow) : I.Y ⟶ U := I.hf.choose_spec.some
  have hx (W : C) : ∀ ⦃I₁ I₂ : (hc.cover W).Arrow⦄ (r : I₁.Relation I₂),
      (E.obj.map I₁.f.op ≫ l I₁.Y (a I₁)) ≫ G.obj.map r.g₁.op =
        (E.obj.map I₂.f.op ≫ l I₂.Y (a I₂)) ≫ G.obj.map r.g₂.op := by
    intro I₁ I₂ r
    rw [Category.assoc, Category.assoc, ← hn r.g₁ (a I₁) (r.g₁ ≫ a I₁),
      ← hn r.g₂ (a I₂) (r.g₁ ≫ a I₁)]
    simp only [← Category.assoc, ← E.obj.map_comp, ← op_comp, r.w]
  let η (W : C) : E.obj.obj (op W) ⟶ G.obj.obj (op W) :=
    G.property.amalgamate (hc.cover W)
      (fun I ↦ E.obj.map I.f.op ≫ l I.Y (a I)) (hx W)
  have hη (W V : C) (f : V ⟶ W) (b : V ⟶ U) :
      η W ≫ G.obj.map f.op = E.obj.map f.op ≫ l V b := by
    have h := G.property.amalgamate_map (hc.cover W)
      (fun I ↦ E.obj.map I.f.op ≫ l I.Y (a I)) (hx W)
      (⟨V, f, ⟨PUnit.unit, ⟨b⟩⟩⟩ : (hc.cover W).Arrow)
    exact h.trans (congrArg (fun k ↦ E.obj.map f.op ≫ k) (he V _ b))
  have hηlocal (W : C) (b : W ⟶ U) : η W = l W b := by
    simpa using hη W W (𝟙 W) b
  let f : E ⟶ G := ObjectProperty.homMk
    { app := fun W ↦ η W.unop
      naturality := by
        rintro ⟨V⟩ ⟨W⟩ ⟨r : W ⟶ V⟩
        apply G.property.hom_ext (hc.cover W)
        intro I
        change (E.obj.map r.op ≫ η W) ≫ G.obj.map I.f.op =
          (η V ≫ G.obj.map r.op) ≫ G.obj.map I.f.op
        rw [Category.assoc, Category.assoc, hη W I.Y I.f (a I),
          ← G.obj.map_comp, ← op_comp (f := I.f) (g := r), hη V I.Y (I.f ≫ r) (a I)]
        simp only [← Category.assoc, ← E.obj.map_comp, ← op_comp] }
  have : IsIso f := Sheaf.isIso_of_coversTop hc (fun _ ↦ by
    have h : (J.overPullback (Type (u + 1)) U).map f =
        ObjectProperty.homMk e.hom := by
      apply Sheaf.hom_ext
      apply NatTrans.ext
      funext W
      exact hηlocal W.unop.left W.unop.hom
    rw [h]
    have : IsIso e.hom := inferInstance
    exact (ObjectProperty.isIso_hom_iff (ObjectProperty.homMk e.hom)).1 this)
  exact ⟨(sheafToPresheaf J (Type (u + 1))).mapIso (asIso f)⟩

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A local representation respecting transport identifies E with the sheaf of sections
of any effective realization of the datum. Finiteness is not needed in this gluing step. -/
theorem etaleRepresentable_descentGlue
    (T : Scheme.{u}) (E : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : T.Etale) [Surjective U.hom]
    (D : Over.DescentDataCategory U.hom) [Etale D.V.hom]
    (e : (E.over U).obj ≅ (Etale.overToEtale U).op ⋙
      uliftYoneda.{u + 1}.obj (Etale.mk D.V.hom))
    (hcompat : ∀ (W : T.Etale) (a b : W ⟶ U) (s : E.obj.obj (op W)),
      (D.datum.transport a.left b.left
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
        (Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
          (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down))).left =
        ((e.hom.app (op (Over.mk b))) s).down.left)
    (P : Scheme.{u}) (π : P ⟶ T) [Etale π] (q : D.V.left ⟶ P)
    (hp : IsPullback q D.V.hom π U.hom)
    (ht : ∀ {W : Scheme.{u}} (a b : W ⟶ U.left) (h : a ≫ U.hom = b ≫ U.hom)
      (z : Over.mk a ⟶ D.V), (D.datum.transport a b h z).left ≫ q = z.left ≫ q) :
    Nonempty (E.obj ≅ uliftYoneda.{u + 1}.obj (Etale.mk π)) := by
  classical
  let : etaleTopology.Subcanonical :=
    GrothendieckTopology.Subcanonical.of_le etaleTopology_le_proetaleTopology
  let : T.smallEtaleTopology.Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful
      (Etale.forget T) _ (etaleTopology.over T)
  let G := T.smallEtaleTopology.uliftYoneda.{u + 1}.obj (Etale.mk π)
  let R := (Etale.overToEtale U).op ⋙ uliftYoneda.{u + 1}.obj (Etale.mk D.V.hom)
  let m : R ⟶ (G.over U).obj :=
    { app := fun W ↦ ↾fun s ↦ ⟨MorphismProperty.Over.homMk (s.down.left ≫ q) (by
        change (s.down.left ≫ q) ≫ π = W.unop.left.hom
        rw [Category.assoc, hp.w, ← Category.assoc]
        exact (congrArg (fun a ↦ a ≫ U.hom)
          (MorphismProperty.Over.w s.down)).trans (MorphismProperty.Over.w W.unop.hom))⟩
      naturality := by
        intro W V f
        ext s
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        exact Category.assoc _ _ _ }
  let n : (G.over U).obj ⟶ R :=
    { app := fun W ↦ ↾fun s ↦ ⟨MorphismProperty.Over.homMk
        (hp.lift s.down.left W.unop.hom.left (by
          exact (MorphismProperty.Over.w s.down).trans
            (MorphismProperty.Over.w W.unop.hom).symm))
        (hp.lift_snd _ _ _)⟩
      naturality := by
        intro W V f
        ext s
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        change hp.lift _ _ _ = f.unop.left.left ≫ hp.lift _ _ _
        apply hp.hom_ext
        · simp only [Category.assoc, hp.lift_fst]
          rfl
        · simp only [Category.assoc, hp.lift_snd]
          exact (congrArg (fun a ↦ a.left) (Over.w f.unop)).symm }
  let l : R ≅ (G.over U).obj :=
    { hom := m
      inv := n
      hom_inv_id := by
        ext W s
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        apply hp.hom_ext
        · exact hp.lift_fst _ _ _
        · exact (hp.lift_snd _ _ _).trans (MorphismProperty.Over.w s.down).symm
      inv_hom_id := by
        ext W s
        apply ULift.ext
        apply MorphismProperty.Over.Hom.ext
        exact hp.lift_fst _ _ _ }
  have hc : T.smallEtaleTopology.CoversTop (fun _ : PUnit.{1} ↦ U) := by
    intro W
    apply T.smallEtaleTopology.superset_covering ?_
      (Etale.ofArrows_baseChange_mem_smallEtaleTopology W
        (fun _ : PUnit.{1} ↦ U.hom) (by
          rw [Set.iUnion_const]
          apply Set.range_eq_univ.mpr
          intro x
          exact Surjective.surj (f := U.hom) x))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    intro V f hf
    obtain ⟨i⟩ := hf
    exact ⟨PUnit.unit, ⟨MorphismProperty.Over.homMk (Limits.pullback.snd W.hom U.hom)
      (Limits.pullback.condition.symm)⟩⟩
  apply iso_of_over_compatible E G U hc (e ≪≫ l)
  intro W a b
  ext s
  apply ULift.ext
  apply MorphismProperty.Over.Hom.ext
  change ((e.hom.app (op (Over.mk a))) s).down.left ≫ q =
    ((e.hom.app (op (Over.mk b))) s).down.left ≫ q
  let z : Over.mk a.left ⟶ D.V :=
    Over.homMk ((e.hom.app (op (Over.mk a))) s).down.left
      (MorphismProperty.Over.w ((e.hom.app (op (Over.mk a))) s).down)
  have h := ht a.left b.left
    ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm) z
  rw [hcompat] at h
  exact h.symm

end AlgebraicGeometry.Scheme

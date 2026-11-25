/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Data.Finset.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sum

/-! # Simultaneous lifting of a finite Kan arrow diagram

Source: Stacks Project, Sites, Tag 0A35, independence of presentations,
and Categories, Section Tag 04AX, eventual equality in filtered set colimits.
(blueprint: lem-weil-pbc-colimit-site-finite-kan-arrow-lift).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Source: Stacks Project, Sites, Tag 0A35, omitted independence-of-presentation
verification, expanded using Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-colimit-site-finite-kan-arrow-lift).

Proof: A costructured arrow p for the opposite stage functor is an arrow
V_t(U) to V_t(p.left.unop). Represent each of the finitely many such arrows
in the arrow colimit, and move all representatives and t.right to one stage.
Use eventual equality in the object colimit to align every source with the
image of U and every target with the image of p.left.unop. Equalize the
finitely many competing maps from t.right, so all stage objects use one map.
The costructured-arrow triangle for each listed h says that the image of
its proposed lifted triangle commutes in V.pt. Eventual equality in the arrow
colimit makes each triangle commute at a later stage. The same criterion
makes the lift of the distinguished identity arrow an identity. Enforce these
finitely many equations successively; their validity persists under further
refinement. If a is the resulting arrow from t.right, put r = Under.mk
(t.hom followed by a), and let b be the associated Under morphism. The lifted
arrows at this stage are the required g. Empty arrow lists impose no triangles;
the distinguished identity still has its identity lift. Repeated objects and
arrows cause no problem because every prescribed equality is imposed before
choosing g. There is no presheaf or choice of section in this construction. -/
theorem colimit_site_finite_kan_arrow_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F)
    (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t : Under i) (U : F.obj t.right) :
    let L := (V.ι.app t.right).toFunctor.op
    let D := CostructuredArrow L (L.obj (op U))
    ∀ (S : Finset D) (T : Finset (Σ p q : D, p ⟶ q))
      (hunit : CostructuredArrow.mk (𝟙 (L.obj (op U))) ∈ S),
      ∃ (r : Under i) (b : t ⟶ r)
        (g : ∀ p : S, (F.map b.right).toFunctor.obj U ⟶
          (F.map b.right).toFunctor.obj p.val.left.unop),
        (∀ (p q : S) (h : p.val ⟶ q.val),
          ⟨p.val, q.val, h⟩ ∈ T →
          g q ≫ (F.map b.right).toFunctor.map h.left.unop = g p) ∧
        g ⟨CostructuredArrow.mk (𝟙 (L.obj (op U))), hunit⟩ = 𝟙 _ := by
  classical
  intro L D S T hunit
  have finite_stage_eq :
      ∀ {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
        (c : Cocone G) (hc : IsColimit c) {α : Type u} [Finite α]
        (j : J) (x y : α → G.obj j),
        (∀ a, c.ι.app j (x a) = c.ι.app j (y a)) →
          ∃ (k : J) (f : j ⟶ k), ∀ a, G.map f (x a) = G.map f (y a) := by
    intro J _ _ G c hc α _ j x y h
    classical
    choose k f hf using fun a ↦
      (Types.FilteredColimit.isColimit_eq_iff' hc _ _).mp (h a)
    obtain ⟨l, g, r, hr⟩ := IsFiltered.wideSpan f
    refine ⟨l, g, fun a ↦ ?_⟩
    simpa only [← ConcreteCategory.comp_apply, ← G.map_comp, hr a] using
      congrArg (fun z ↦ G.map (r a) z) (hf a)
  have finite_representatives_above :
      ∀ {J : Type u} [SmallCategory J] [IsFiltered J] (G : J ⥤ Type u)
        (c : Cocone G) (hc : IsColimit c) {α : Type u} [Finite α]
        (j : J) (x : α → c.pt),
        ∃ (k : J) (f : j ⟶ k) (y : α → G.obj k),
          ∀ a, c.ι.app k (y a) = x a := by
    intro J _ _ G c hc α _ j x
    classical
    choose k y hy using fun a ↦ Types.jointly_surjective_of_isColimit hc (x a)
    let f := fun a ↦ IsFiltered.leftToMax j (k a)
    let g := fun a ↦ IsFiltered.rightToMax j (k a)
    obtain ⟨t, r, s, _⟩ := IsFiltered.wideSpan f
    refine ⟨t, r, fun a ↦ G.map (g a ≫ s a) (y a), fun a ↦ ?_⟩
    exact (ConcreteCategory.congr_hom (c.w (g a ≫ s a)) (y a)).trans (hy a)
  have arrow_comp_congr :
      ∀ {C : Type u} [Category.{u} C] {a b c d : Arrow C},
        a = c → b = d →
          ∀ (h : a.right = b.left) (h' : c.right = d.left),
          Arrow.mk (a.hom ≫ eqToHom h ≫ b.hom) =
            Arrow.mk (c.hom ≫ eqToHom h' ≫ d.hom) := by
    intro C _ a b c d ha hb h h'
    subst c
    subst d
    rfl
  let R : S → Arrow V.pt := fun p ↦ Arrow.mk p.val.hom.unop
  obtain ⟨k, c, B, hB⟩ := finite_representatives_above (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows t.right R
  have hw {j k : J} (a : j ⟶ k) :
      (F.map a).toFunctor ⋙ (V.ι.app k).toFunctor = (V.ι.app j).toFunctor :=
    congrArg Cat.Hom.toFunctor (V.w a)
  let C := (F.map c).toFunctor
  let X : S × Bool → F.obj k := fun p ↦
    if p.2 then (B p.1).right else (B p.1).left
  let Y : S × Bool → F.obj k := fun p ↦
    if p.2 then C.obj p.1.val.left.unop else C.obj U
  have hXY (p : S × Bool) : (Cat.objects.mapCocone V).ι.app k (X p) =
      (Cat.objects.mapCocone V).ι.app k (Y p) := by
    rcases p with ⟨p, b⟩
    cases b
    · exact (congrArg Arrow.left (hB p)).trans
        (congrArg (fun H : F.obj t.right ⥤ V.pt ↦ H.obj U) (hw c)).symm
    · exact (congrArg Arrow.right (hB p)).trans
        (congrArg (fun H : F.obj t.right ⥤ V.pt ↦ H.obj p.val.left.unop)
          (hw c)).symm
  obtain ⟨l, d, hd⟩ := finite_stage_eq (F ⋙ Cat.objects)
    (Cat.objects.mapCocone V) hobjects k X Y hXY
  let W := (F.map d).toFunctor
  let B' (p : S) := W.mapArrow.obj (B p)
  have hl (p : S) : (B' p).left = W.obj (C.obj U) := hd (p, false)
  have hr (p : S) : (B' p).right = W.obj (C.obj p.val.left.unop) := hd (p, true)
  let g (p : S) : W.obj (C.obj U) ⟶ W.obj (C.obj p.val.left.unop) :=
    eqToHom (hl p).symm ≫ (B' p).hom ≫ eqToHom (hr p)
  have hg (p : S) : (V.ι.app l).toFunctor.mapArrow.obj (Arrow.mk (g p)) = R p := by
    have he : Arrow.mk (g p) = B' p := by simp [g]
    rw [he]
    exact (congrArg (fun H : F.obj k ⥤ V.pt ↦ H.mapArrow.obj (B p))
      (hw d)).trans (hB p)
  let E := {e : T // e.val.1 ∈ S ∧ e.val.2.1 ∈ S}
  let p₀ : S := ⟨CostructuredArrow.mk (𝟙 (L.obj (op U))), hunit⟩
  let P : E ⊕ Unit → Arrow (F.obj l) := fun a ↦
    match a with
    | .inl e => Arrow.mk (g ⟨e.val.val.2.1, e.property.2⟩ ≫
        W.map (C.map e.val.val.2.2.left.unop))
    | .inr _ => Arrow.mk (g p₀)
  let Q : E ⊕ Unit → Arrow (F.obj l) := fun a ↦
    match a with
    | .inl e => Arrow.mk (g ⟨e.val.val.1, e.property.1⟩)
    | .inr _ => Arrow.mk (𝟙 (W.obj (C.obj U)))
  have hPQ (a : E ⊕ Unit) : (Cat.arrows.mapCocone V).ι.app l (P a) =
      (Cat.arrows.mapCocone V).ι.app l (Q a) := by
    cases a with
    | inl e =>
      let p : S := ⟨e.val.val.1, e.property.1⟩
      let q : S := ⟨e.val.val.2.1, e.property.2⟩
      let h : p.val ⟶ q.val := e.val.val.2.2
      have hh : (V.ι.app l).toFunctor.mapArrow.obj
          (Arrow.mk (W.map (C.map h.left.unop))) =
          Arrow.mk ((V.ι.app t.right).toFunctor.map h.left.unop) := by
        exact (congrArg (fun H : F.obj k ⥤ V.pt ↦
          Arrow.mk (H.map (C.map h.left.unop))) (hw d)).trans
          (congrArg (fun H : F.obj t.right ⥤ V.pt ↦
            Arrow.mk (H.map h.left.unop)) (hw c))
      have he := arrow_comp_congr (hg q) hh rfl rfl
      have hc : q.val.hom.unop ≫
          (V.ι.app t.right).toFunctor.map h.left.unop = p.val.hom.unop := by
        exact congrArg Quiver.Hom.unop (CostructuredArrow.w h)
      change Arrow.mk ((V.ι.app l).toFunctor.map
        (g q ≫ W.map (C.map h.left.unop))) = _
      rw [(V.ι.app l).toFunctor.map_comp]
      have he' : Arrow.mk ((V.ι.app l).toFunctor.map (g q) ≫
          (V.ι.app l).toFunctor.map (W.map (C.map h.left.unop))) =
          Arrow.mk (q.val.hom.unop ≫ (V.ι.app t.right).toFunctor.map h.left.unop) := by
        change Arrow.mk ((V.ι.app l).toFunctor.map (g q) ≫
          eqToHom rfl ≫ (V.ι.app l).toFunctor.map (W.map (C.map h.left.unop))) =
          Arrow.mk (q.val.hom.unop ≫ eqToHom rfl ≫
            (V.ι.app t.right).toFunctor.map h.left.unop) at he
        simpa only [eqToHom_refl, Category.id_comp] using he
      exact he'.trans ((congrArg Arrow.mk hc).trans (hg p).symm)
    | inr a =>
      change (V.ι.app l).toFunctor.mapArrow.obj (Arrow.mk (g p₀)) =
        Arrow.mk ((V.ι.app l).toFunctor.map (𝟙 (W.obj (C.obj U))))
      rw [hg, (V.ι.app l).toFunctor.map_id]
      have ho : (V.ι.app l).toFunctor.obj (W.obj (C.obj U)) =
          (V.ι.app t.right).toFunctor.obj U :=
        (congrArg (fun H : F.obj k ⥤ V.pt ↦ H.obj (C.obj U)) (hw d)).trans
          (congrArg (fun H : F.obj t.right ⥤ V.pt ↦ H.obj U) (hw c))
      simpa [R, p₀, L] using congrArg (fun z ↦ Arrow.mk (𝟙 z)) ho.symm
  obtain ⟨m, a, ha⟩ := finite_stage_eq (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows l P Q hPQ
  let Z := (F.map a).toFunctor
  let v := c ≫ d ≫ a
  let r : Under i := Under.mk (t.hom ≫ v)
  let b : t ⟶ r := Under.homMk v
  have ho (X : F.obj t.right) :
      (F.map v).toFunctor.obj X = Z.obj (W.obj (C.obj X)) := by
    simp [v, Z, W, C]
  let g' (p : S) : (F.map v).toFunctor.obj U ⟶
      (F.map v).toFunctor.obj p.val.left.unop :=
    eqToHom (ho U) ≫ Z.map (g p) ≫ eqToHom (ho p.val.left.unop).symm
  refine ⟨r, b, g', ?_, ?_⟩
  · intro p q h hh
    have he := ha (.inl ⟨⟨⟨p.val, q.val, h⟩, hh⟩, p.property, q.property⟩)
    change Arrow.mk (Z.map (g q ≫ W.map (C.map h.left.unop))) =
      Arrow.mk (Z.map (g p)) at he
    have he' := Arrow.mk_injective _ _ he
    rw [Z.map_comp] at he'
    have hm : (F.map v).toFunctor.map h.left.unop =
        eqToHom (ho q.val.left.unop) ≫ Z.map (W.map (C.map h.left.unop)) ≫
          eqToHom (ho p.val.left.unop).symm := by
      have hv : (F.map v).toFunctor = C ⋙ W ⋙ Z := by simp [v, C, W, Z]
      exact Functor.congr_hom hv h.left.unop
    change g' q ≫ (F.map v).toFunctor.map h.left.unop = g' p
    rw [hm]
    dsimp only [g']
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    rw [← Category.assoc (Z.map (g q)), he']
  · have he := ha (.inr ())
    change Arrow.mk (Z.map (g p₀)) = Arrow.mk (Z.map (𝟙 (W.obj (C.obj U)))) at he
    have he' := Arrow.mk_injective _ _ he
    rw [Z.map_id] at he'
    change g' p₀ = 𝟙 _
    simp [g', he']


end CategoryTheory

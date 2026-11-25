/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Basic.Finite.Sum
import all WeilConjectures.CategoryTheory.FilteredColimitFiniteIsoLift
import all WeilConjectures.CategoryTheory.ColimitSiteRawSectionGenerators

/-! # Lifting a finite family of restrictions and its triangles

Source: Stacks Project, Sites, Tag 0A35 (lemma-compute-pullback-to-limit),
independence of the section presentation; Tag 09YL, finite-diagram observation.
(blueprint: lem-weil-pbc-colimit-site-finite-restriction-family-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

private theorem lift_same_stage_arrow
    {J : Type u} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (ho : IsColimit (Cat.objects.mapCocone V))
    (ha : IsColimit (Cat.arrows.mapCocone V))
    {i : J} (t : Under i) (U W : F.obj t.right)
    (f : (V.ι.app t.right).toFunctor.obj U ⟶ (V.ι.app t.right).toFunctor.obj W) :
    ∃ (r : Under i) (b : t ⟶ r)
      (g : (F.map b.right).toFunctor.obj U ⟶ (F.map b.right).toFunctor.obj W),
      Arrow.mk ((V.ι.app r.right).toFunctor.map g) = Arrow.mk f := by
  classical
  obtain ⟨k, a, b, g, hg⟩ := lift_arrow F V ho ha t.right t.right U W f
  let l := IsFiltered.coeq a b
  let c : k ⟶ l := IsFiltered.coeqHom a b
  let r : Under i := Under.mk (t.hom ≫ a ≫ c)
  let d : t ⟶ r := Under.homMk (a ≫ c) (by simp [r])
  have es : (F.map d.right).toFunctor.obj U =
      (F.map c).toFunctor.obj ((F.map a).toFunctor.obj U) := by simp [d]
  have et : (F.map c).toFunctor.obj ((F.map b).toFunctor.obj W) =
      (F.map d.right).toFunctor.obj W := by
    change (F.map b ≫ F.map c).toFunctor.obj W = (F.map (a ≫ c)).toFunctor.obj W
    rw [← F.map_comp, IsFiltered.coeq_condition a b]
  let g' := eqToHom es ≫ (F.map c).toFunctor.map g ≫ eqToHom et
  refine ⟨r, d, g', ?_⟩
  have hgg : Arrow.mk g' = Arrow.mk ((F.map c).toFunctor.map g) := by simp [g']
  change (V.ι.app l).toFunctor.mapArrow.obj (Arrow.mk g') = Arrow.mk f
  rw [hgg]
  exact (congrArg (fun H : F.obj k ⟶ V.pt ↦ H.toFunctor.mapArrow.obj (Arrow.mk g))
    (V.w c)).trans hg

/-- Source: Stacks Project, Sites, Tags 0A35 and 09YL, finite diagram lifting
in the section presentation.
(blueprint: lem-weil-pbc-colimit-site-finite-restriction-family-lift).

Proof: Lift each restriction arrow and align its endpoints with the prescribed
stage objects by eventual equality in the object colimit. Equalize the two
arrows out of t.right, then put the finitely many resulting refinements at one
common object of Under i using wideSpan. These give arrows g with a single
transition b. The images of the proposed triangles and identity equation agree
in the arrow colimit. Eventual arrow equality, synchronized by wideSpan for the
finite set of edges together with the base identity, makes all of them hold
at one further refinement. Compose b with that refinement and transport along
functoriality of F. Empty edge families are allowed; the base object ensures
that the identity equation is included.
-/
theorem colimit_site_finite_restriction_family_lift
    (J : Type u) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{u, u})
    (V : Cocone F) (hobjects : IsColimit (Cat.objects.mapCocone V))
    (harrows : IsColimit (Cat.arrows.mapCocone V))
    (i : J) (t : Under i) (U : F.obj t.right)
    {α ε : Type u} [Finite α] [Finite ε]
    (W : α → F.obj t.right)
    (f : ∀ q, (V.ι.app t.right).toFunctor.obj U ⟶
      (V.ι.app t.right).toFunctor.obj (W q))
    (src dst : ε → α) (a : ∀ e, W (src e) ⟶ W (dst e))
    (hf : ∀ e, f (src e) ≫ (V.ι.app t.right).toFunctor.map (a e) = f (dst e))
    (q₀ : α) (hW : W q₀ = U)
    (h₀ : f q₀ = eqToHom (congrArg (V.ι.app t.right).toFunctor.obj hW.symm)) :
    ∃ (r : Under i) (b : t ⟶ r)
      (g : ∀ q, (F.map b.right).toFunctor.obj U ⟶
        (F.map b.right).toFunctor.obj (W q)),
      (∀ e, g (src e) ≫ (F.map b.right).toFunctor.map (a e) = g (dst e)) ∧
      g q₀ = eqToHom (congrArg (F.map b.right).toFunctor.obj hW.symm) := by
  classical
  choose r b g hg using fun q ↦ lift_same_stage_arrow F V hobjects harrows t U (W q) (f q)
  obtain ⟨k, d, c, hc⟩ := IsFiltered.wideSpan b
  have ef (q : α) : (F.map (b q).right).toFunctor ⋙ (F.map (c q).right).toFunctor =
      (F.map d.right).toFunctor := by
    exact congrArg Cat.Hom.toFunctor ((F.map_comp _ _).symm.trans
      (congrArg F.map (congrArg Under.Hom.right (hc q))))
  let gk (q : α) : (F.map d.right).toFunctor.obj U ⟶
      (F.map d.right).toFunctor.obj (W q) :=
    eqToHom (congrArg (fun H ↦ H.obj U) (ef q).symm) ≫
      (F.map (c q).right).toFunctor.map (g q) ≫
      eqToHom (congrArg (fun H ↦ H.obj (W q)) (ef q))
  have hgk (q : α) : Arrow.mk ((V.ι.app k.right).toFunctor.map (gk q)) =
      Arrow.mk (f q) := by
    simp only [gk, Functor.map_comp, eqToHom_map,
      Arrow.arrow_mk_eqToHom_comp, Arrow.arrow_mk_comp_eqToHom]
    exact (congrArg (fun H : F.obj (r q).right ⟶ V.pt ↦
      H.toFunctor.mapArrow.obj (Arrow.mk (g q))) (V.w (c q).right)).trans (hg q)
  have htri (e : ε) :
      Arrow.mk ((V.ι.app k.right).toFunctor.map
        (gk (src e) ≫ (F.map d.right).toFunctor.map (a e))) =
      Arrow.mk ((V.ι.app k.right).toFunctor.map (gk (dst e))) := by
    have ha : Arrow.mk ((V.ι.app k.right).toFunctor.map
        ((F.map d.right).toFunctor.map (a e))) =
        Arrow.mk ((V.ι.app t.right).toFunctor.map (a e)) :=
      congrArg (fun H : F.obj t.right ⟶ V.pt ↦ H.toFunctor.mapArrow.obj (Arrow.mk (a e)))
        (V.w d.right)
    have hh := arrow_comp_congr (hgk (src e)) ha rfl rfl
    simp only [eqToHom_refl, Category.id_comp,
      Arrow.mk_hom, hf e] at hh
    simpa only [Functor.map_comp] using hh.trans (hgk (dst e)).symm
  have hid : Arrow.mk ((V.ι.app k.right).toFunctor.map (gk q₀)) =
      Arrow.mk ((V.ι.app k.right).toFunctor.map
        (eqToHom (congrArg (F.map d.right).toFunctor.obj hW.symm))) := by
    rw [eqToHom_map]
    have heq : (V.ι.app k.right).toFunctor.obj ((F.map d.right).toFunctor.obj U) =
        (V.ι.app t.right).toFunctor.obj U :=
      congrArg (fun H : F.obj t.right ⟶ V.pt ↦ H.toFunctor.obj U) (V.w d.right)
    have hh := hgk q₀
    rw [h₀] at hh
    have hmk {X Y : V.pt} (h : X = Y) :
        Arrow.mk (eqToHom h) = Arrow.mk (𝟙 X) := by subst Y; rfl
    exact hh.trans (by
      rw [hmk, hmk]
      exact congrArg (fun X ↦ Arrow.mk (𝟙 X)) heq.symm)
  let X : ε ⊕ Unit → Arrow (F.obj k.right) := fun q ↦
    match q with
    | .inl e => Arrow.mk (gk (src e) ≫ (F.map d.right).toFunctor.map (a e))
    | .inr _ => Arrow.mk (gk q₀)
  let Z : ε ⊕ Unit → Arrow (F.obj k.right) := fun q ↦
    match q with
    | .inl e => Arrow.mk (gk (dst e))
    | .inr _ => Arrow.mk (eqToHom (congrArg (F.map d.right).toFunctor.obj hW.symm))
  obtain ⟨l, v, hv⟩ := finite_stage_eq (F ⋙ Cat.arrows)
    (Cat.arrows.mapCocone V) harrows k.right X Z (fun q ↦ by
      rcases q with e | _
      · exact htri e
      · exact hid)
  let r' : Under i := Under.mk (k.hom ≫ v)
  let c' : k ⟶ r' := Under.homMk v rfl
  let b' : t ⟶ r' := d ≫ c'
  have eb : (F.map b'.right).toFunctor =
      (F.map d.right).toFunctor ⋙ (F.map v).toFunctor := by simp [b', c']
  let g' (q : α) : (F.map b'.right).toFunctor.obj U ⟶
      (F.map b'.right).toFunctor.obj (W q) :=
    eqToHom (congrArg (fun H ↦ H.obj U) eb) ≫
      (F.map v).toFunctor.map (gk q) ≫
      eqToHom (congrArg (fun H ↦ H.obj (W q)) eb.symm)
  refine ⟨r', b', g', ?_, ?_⟩
  · intro e
    have hh := hv (Sum.inl e)
    change Arrow.mk ((F.map v).toFunctor.map
      (gk (src e) ≫ (F.map d.right).toFunctor.map (a e))) =
        Arrow.mk ((F.map v).toFunctor.map (gk (dst e))) at hh
    have hh' := Arrow.mk_injective _ _ hh
    simp only [Functor.map_comp] at hh'
    dsimp only [g']
    rw [Functor.congr_hom eb (a e)]
    simp only [Functor.comp_map, Category.assoc,
      eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    simpa only [Category.assoc] using congrArg
      (fun h ↦ eqToHom (congrArg (fun H ↦ H.obj U) eb) ≫ h ≫
        eqToHom (congrArg (fun H ↦ H.obj (W (dst e))) eb.symm)) hh' 
  · have hh := hv (Sum.inr ())
    change Arrow.mk ((F.map v).toFunctor.map (gk q₀)) =
      Arrow.mk ((F.map v).toFunctor.map
        (eqToHom (congrArg (F.map d.right).toFunctor.obj hW.symm))) at hh
    have hh' := Arrow.mk_injective _ _ hh
    simp only [eqToHom_map] at hh'
    dsimp only [g']
    rw [hh']
    simp


end CategoryTheory

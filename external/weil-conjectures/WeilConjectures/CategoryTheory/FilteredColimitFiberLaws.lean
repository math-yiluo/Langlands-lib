/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredColimitHomCategory
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Category laws on filtered arrow fibers -/

@[expose] public section

universe z

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem hom_induction
    {J : Type z} [SmallCategory J] (F : J ⥤ Cat.{z, z})
    (P : ∀ X Y, FilteredColimitHom F X Y → Prop)
    (hP : ∀ (j : J) (X Y : F.obj j) (f : X ⟶ Y),
      P _ _ (filteredColimitHomι F j f)) :
    ∀ X Y (f : FilteredColimitHom F X Y), P X Y f := by
  intro X Y f
  obtain ⟨a, ha⟩ := f
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective' a
  subst a
  simp only [filteredColimitArrowSource_ι, filteredColimitArrowTarget_ι] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact hP j b.left b.right b.hom

private theorem triple_rep
    {J : Type z} [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z})
    {W X Y Z : colimit (F ⋙ Cat.objects)}
    (f : FilteredColimitHom F W X) (g : FilteredColimitHom F X Y)
    (h : FilteredColimitHom F Y Z) :
    ∃ (j : J) (W' X' Y' Z' : F.obj j) (f' : W' ⟶ X') (g' : X' ⟶ Y')
      (h' : Y' ⟶ Z'),
      (filteredColimitHomι F j f').val = f.val ∧
      (filteredColimitHomι F j g').val = g.val ∧
      (filteredColimitHomι F j h').val = h.val := by
  obtain ⟨j, a, b, ha, hb⟩ :=
    Types.FilteredColimit.jointly_surjective_of_isColimit₂
      (colimit.isColimit (F ⋙ Cat.arrows)) f.val g.val
  obtain ⟨k, d, hd⟩ := Types.jointly_surjective' h.val
  let l := IsFiltered.max j k
  let u := IsFiltered.leftToMax j k
  let v := IsFiltered.rightToMax j k
  let a₀ := (F ⋙ Cat.arrows).map u a
  let b₀ := (F ⋙ Cat.arrows).map u b
  let d₀ := (F ⋙ Cat.arrows).map v d
  have ha₀ : colimit.ι (F ⋙ Cat.arrows) l a₀ = f.val :=
    (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) u) a).trans ha
  have hb₀ : colimit.ι (F ⋙ Cat.arrows) l b₀ = g.val :=
    (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) u) b).trans hb
  have hd₀ : colimit.ι (F ⋙ Cat.arrows) l d₀ = h.val :=
    (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) v) d).trans hd
  have e₁ : colimit.ι (F ⋙ Cat.objects) l a₀.right =
      colimit.ι (F ⋙ Cat.objects) l b₀.left := by
    rw [← filteredColimitArrowTarget_ι, ha₀, f.property.2,
      ← filteredColimitArrowSource_ι, hb₀, g.property.1]
  have e₂ : colimit.ι (F ⋙ Cat.objects) l b₀.right =
      colimit.ι (F ⋙ Cat.objects) l d₀.left := by
    rw [← filteredColimitArrowTarget_ι, hb₀, g.property.2,
      ← filteredColimitArrowSource_ι, hd₀, h.property.1]
  obtain ⟨m, t, et⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (F ⋙ Cat.objects))
      a₀.right b₀.left).mp e₁
  have e₂' : colimit.ι (F ⋙ Cat.objects) m ((F ⋙ Cat.objects).map t b₀.right) =
      colimit.ι (F ⋙ Cat.objects) m ((F ⋙ Cat.objects).map t d₀.left) := by
    simpa only [← ConcreteCategory.comp_apply, colimit.w] using e₂
  obtain ⟨n, s, es⟩ :=
    (Types.FilteredColimit.isColimit_eq_iff' (colimit.isColimit (F ⋙ Cat.objects))
      _ _).mp e₂'
  let q := t ≫ s
  let A := (F ⋙ Cat.arrows).map q a₀
  let B := (F ⋙ Cat.arrows).map q b₀
  let D := (F ⋙ Cat.arrows).map q d₀
  have eA : A.right = B.left := by
    change (F ⋙ Cat.objects).map q a₀.right = (F ⋙ Cat.objects).map q b₀.left
    simp only [q, Functor.map_comp, ConcreteCategory.comp_apply]
    rw [et]
  have eB : B.right = D.left := by
    change (F ⋙ Cat.objects).map q b₀.right = (F ⋙ Cat.objects).map q d₀.left
    simpa only [q, Functor.map_comp, ConcreteCategory.comp_apply] using es
  refine ⟨n, A.left, A.right, B.right, D.right, A.hom,
    eqToHom eA ≫ B.hom, eqToHom eB ≫ D.hom, ?_, ?_, ?_⟩
  · change colimit.ι (F ⋙ Cat.arrows) n (Arrow.mk A.hom) = f.val
    rw [Arrow.mk_eq]
    exact (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) q) a₀).trans ha₀
  · change colimit.ι (F ⋙ Cat.arrows) n (Arrow.mk (eqToHom eA ≫ B.hom)) = g.val
    rw [Arrow.arrow_mk_eqToHom_comp, Arrow.mk_eq]
    exact (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) q) b₀).trans hb₀
  · change colimit.ι (F ⋙ Cat.arrows) n (Arrow.mk (eqToHom eB ≫ D.hom)) = h.val
    rw [Arrow.arrow_mk_eqToHom_comp, Arrow.mk_eq]
    exact (ConcreteCategory.congr_hom (colimit.w (F ⋙ Cat.arrows) q) d₀).trans hd₀

/-- Source: Stacks Project, Sites, proof of Tag 09YL, first paragraph,
and Categories, Section Tag 04AX.
(blueprint: lem-weil-pbc-filtered-colimit-fiber-laws).

Proof: An arbitrary element of a Hom fiber has a stage arrow representative.
For the identity laws choose such a representative and identify its endpoints with
the given objects. The two preservation formulas reduce the assertion to the stage
identity laws. For associativity choose representatives of the three arrows, move
them to a common stage, and use eventual equality in the object colimit to make
both middle endpoint equalities hold at a further stage. Both iterated composites
are then represented by the iterated composites at that stage, by the preservation
formula. Stage associativity equates them. Equality in a fiber is equality of its
underlying arrow colimit elements, since endpoint certificates are propositions.
Thus transporting endpoint equalities introduces no additional choice. The empty
object colimit case has no arrows and the assertions are vacuous. -/
theorem filteredColimit_fiber_laws
    (J : Type z) [SmallCategory J] [IsFiltered J] (F : J ⥤ Cat.{z, z})
    (i : ∀ X : colimit (F ⋙ Cat.objects), FilteredColimitHom F X X)
    (c : ∀ {X Y Z : colimit (F ⋙ Cat.objects)}, FilteredColimitHom F X Y →
      FilteredColimitHom F Y Z → FilteredColimitHom F X Z)
    (hi : ∀ (j : J) (X : F.obj j),
      i (colimit.ι (F ⋙ Cat.objects) j X) = filteredColimitHomι F j (𝟙 X))
    (hc : ∀ (j : J) (X Y Z : F.obj j) (f : X ⟶ Y) (g : Y ⟶ Z),
      c (filteredColimitHomι F j f) (filteredColimitHomι F j g) =
        filteredColimitHomι F j (f ≫ g)) :
    (∀ (X Y : colimit (F ⋙ Cat.objects)) (f : FilteredColimitHom F X Y),
      c (i X) f = f) ∧
    (∀ (X Y : colimit (F ⋙ Cat.objects)) (f : FilteredColimitHom F X Y),
      c f (i Y) = f) ∧
    (∀ (W X Y Z : colimit (F ⋙ Cat.objects))
      (f : FilteredColimitHom F W X) (g : FilteredColimitHom F X Y)
      (h : FilteredColimitHom F Y Z), c (c f g) h = c f (c g h)) := by
  refine ⟨?_, ?_, ?_⟩
  · apply hom_induction F
    intro j X Y f
    rw [hi, hc]
    simp
  · apply hom_induction F
    intro j X Y f
    rw [hi, hc]
    simp
  · intro W X Y Z f g h
    obtain ⟨j, W', X', Y', Z', f', g', h', hf, hg, hh⟩ := triple_rep F f g h
    have hW := (congrArg (filteredColimitArrowSource F) hf).trans f.property.1
    have hX := (congrArg (filteredColimitArrowTarget F) hf).trans f.property.2
    have hY := (congrArg (filteredColimitArrowTarget F) hg).trans g.property.2
    have hZ := (congrArg (filteredColimitArrowTarget F) hh).trans h.property.2
    simp only [filteredColimitHomι, filteredColimitArrowSource_ι,
      filteredColimitArrowTarget_ι, Arrow.mk_left, Arrow.mk_right] at hW hX hY hZ
    subst W
    subst X
    subst Y
    subst Z
    have hf' : filteredColimitHomι F j f' = f := Subtype.ext hf
    have hg' : filteredColimitHomι F j g' = g := Subtype.ext hg
    have hh' : filteredColimitHomι F j h' = h := Subtype.ext hh
    rw [← hf', ← hg', ← hh', hc, hc, hc, hc, Category.assoc]

end CategoryTheory

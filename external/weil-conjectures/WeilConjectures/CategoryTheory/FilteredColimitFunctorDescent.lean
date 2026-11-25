/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.ArrowsFunctor
public import Mathlib.CategoryTheory.Limits.IsLimit
public import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered

/-! # Descent of compatible functors from a filtered colimit

Source: Stacks Project, Sites, proof of Tag 09YL
(blueprint: lem-weil-pbc-filtered-colimit-functor-descent).

The colimits of the object and arrow sets suffice for descent into categories
with arbitrary object and morphism universes.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem arrow_hom_heq {C : Type v} [Category.{w} C] {a b : Arrow C}
    (h : a = b) : HEq a.hom b.hom := by
  cases h
  rfl

private theorem arrow_comp_congr {C : Type v} [Category.{w} C]
    {X Y Z X' Y' Z' : C} (f : X ⟶ Y) (g : Y ⟶ Z) (f' : X' ⟶ Y') (g' : Y' ⟶ Z')
    (hf : Arrow.mk f = Arrow.mk f') (hg : Arrow.mk g = Arrow.mk g') :
    Arrow.mk (f ≫ g) = Arrow.mk (f' ≫ g') := by
  obtain ⟨hX, hY, hf⟩ := (Arrow.mk_eq_mk_iff f f').mp hf
  obtain ⟨_, hZ, hg⟩ := (Arrow.mk_eq_mk_iff g g').mp hg
  subst hX
  subst hY
  subst hZ
  simpa using congrArg Arrow.mk (congrArg₂ (fun f g ↦ f ≫ g) hf hg)

private theorem exists_set_descent
    {J : Type u} [SmallCategory J] (F : J ⥤ Type u) (L : Cocone F)
    (hL : Nonempty (IsColimit L)) (T : Type v)
    (f : ∀ j, F.obj j → T)
    (hf : ∀ (j k : J) (a : j ⟶ k) (x : F.obj j), f k (F.map a x) = f j x) :
    ∃ g : L.pt → T, ∀ j x, g (L.ι.app j x) = f j x := by
  let c : F.CoconeTypes :=
    { pt := T
      ι := f
      ι_naturality := by intro j k a; funext x; exact hf j k a x }
  obtain ⟨g, hg⟩ := ((Types.isColimit_iff_coconeTypesIsColimit L).mp hL).exists_desc c
  exact ⟨g, fun j x ↦ congrFun (hg j) x⟩

/-- Source: Stacks Project, Sites, proof of Tag 09YL, the construction of the
filtered colimit category; the universal property verification is written here.
(blueprint: lem-weil-pbc-filtered-colimit-functor-descent).

Proof: send an object represented at stage j to its image under v j, and an arrow
represented at stage j to its image under v j. Compatibility makes these maps
well-defined: equal representatives agree at a common later stage by the equality
criterion for filtered colimits of sets. Object and arrow representatives exist
by the two set-colimit hypotheses. Source and target of the resulting arrow are
the chosen images of its endpoints, since the stage functors respect endpoints.
To verify identities represent the object at one stage. For composition represent
the two arrows at a common stage. Their middle endpoints have equal images in the
object colimit; after passing to a further stage those endpoints are equal, so
composition is represented by their composite there. Functoriality of v at that
stage proves preservation of composition. The defining representative formulas
give (L.ι.app j).toFunctor ⋙ V = v j, including equality on objects and arrows.
The construction uses only the small source categories; D may have larger object
and hom universes. -/
theorem exists_filteredColimit_functor_descent
    (J : Type u) [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Cat.{u, u}) (L : Cocone F)
    (hobjects : Nonempty (IsColimit (Cat.objects.mapCocone L)))
    (harrows : Nonempty (IsColimit (Cat.arrows.mapCocone L)))
    (D : Type v) [Category.{w} D] (v : ∀ j : J, F.obj j ⥤ D)
    (hcompat : ∀ (j k : J) (a : j ⟶ k), (F.map a).toFunctor ⋙ v k = v j) :
    ∃ V : L.pt ⥤ D, ∀ j : J, (L.ι.app j).toFunctor ⋙ V = v j := by
  classical
  obtain ⟨O, hO⟩ := exists_set_descent (F ⋙ Cat.objects) (Cat.objects.mapCocone L)
    hobjects D (fun j ↦ (v j).obj) (by
      intro j k a x
      exact congrArg (fun G : F.obj j ⥤ D ↦ G.obj x) (hcompat j k a))
  obtain ⟨A, hA⟩ := exists_set_descent (F ⋙ Cat.arrows) (Cat.arrows.mapCocone L)
    harrows (Arrow D) (fun j a ↦ Arrow.mk ((v j).map a.hom)) (by
      intro j k a x
      exact congrArg (fun G : F.obj j ⥤ D ↦ Arrow.mk (G.map x.hom)) (hcompat j k a))
  change ∀ (j : J) (x : F.obj j), O ((L.ι.app j).toFunctor.obj x) = (v j).obj x at hO
  change ∀ (j : J) (x : Arrow (F.obj j)),
    A (Arrow.mk ((L.ι.app j).toFunctor.map x.hom)) = Arrow.mk ((v j).map x.hom) at hA
  have hleft (a : Arrow L.pt) : (A a).left = O a.left := by
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit harrows.some a
    exact (congrArg Arrow.left (hA j x)).trans (hO j x.left).symm
  have hright (a : Arrow L.pt) : (A a).right = O a.right := by
    obtain ⟨j, x, rfl⟩ := Types.jointly_surjective_of_isColimit harrows.some a
    exact (congrArg Arrow.right (hA j x)).trans (hO j x.right).symm
  let M : ∀ {X Y : L.pt}, (X ⟶ Y) → (O X ⟶ O Y) := fun {X Y} f ↦
    eqToHom (hleft (Arrow.mk f)).symm ≫ (A (Arrow.mk f)).hom ≫
      eqToHom (hright (Arrow.mk f))
  have hM {X Y : L.pt} (f : X ⟶ Y) : Arrow.mk (M f) = A (Arrow.mk f) := by
    simp [M]
  have hrep (j : J) {X Y : F.obj j} (f : X ⟶ Y) :
      Arrow.mk (M ((L.ι.app j).toFunctor.map f)) = Arrow.mk ((v j).map f) :=
    (hM _).trans (hA j (Arrow.mk f))
  have hid (X : L.pt) : M (𝟙 X) = 𝟙 (O X) := by
    obtain ⟨j, x, hx⟩ := Types.jointly_surjective_of_isColimit hobjects.some X
    change (L.ι.app j).toFunctor.obj x = X at hx
    change F.obj j at x
    subst X
    apply Arrow.mk_injective
    calc
      Arrow.mk (M (𝟙 ((L.ι.app j).toFunctor.obj x))) =
          Arrow.mk (𝟙 ((v j).obj x)) := by
        simpa only [Functor.map_id] using hrep j (𝟙 x)
      _ = Arrow.mk (𝟙 (O ((L.ι.app j).toFunctor.obj x))) := by rw [hO j x]
  have hcomp {X Y Z : L.pt} (f : X ⟶ Y) (g : Y ⟶ Z) :
      M (f ≫ g) = M f ≫ M g := by
    obtain ⟨j, x, y, hx, hy⟩ :=
      Types.FilteredColimit.jointly_surjective_of_isColimit₂ harrows.some
        (Arrow.mk f) (Arrow.mk g)
    change Arrow (F.obj j) at x y
    change Arrow.mk ((L.ι.app j).toFunctor.map x.hom) = Arrow.mk f at hx
    change Arrow.mk ((L.ι.app j).toFunctor.map y.hom) = Arrow.mk g at hy
    -- Equalize the middle endpoints before composing the representatives.
    have hmid : (Cat.objects.mapCocone L).ι.app j x.right =
        (Cat.objects.mapCocone L).ι.app j y.left :=
      (congrArg Arrow.right hx).trans (congrArg Arrow.left hy).symm
    obtain ⟨k, a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hobjects.some x.right y.left).mp hmid
    change (F.map a).toFunctor.obj x.right = (F.map a).toFunctor.obj y.left at ha
    let f' := (F.map a).toFunctor.map x.hom
    let g' := eqToHom ha ≫ (F.map a).toFunctor.map y.hom
    have hw : (F.map a).toFunctor ⋙ (L.ι.app k).toFunctor =
        (L.ι.app j).toFunctor := by
      exact congrArg Cat.Hom.toFunctor (L.w a)
    have hf' : Arrow.mk ((L.ι.app k).toFunctor.map f') = Arrow.mk f := by
      calc
        _ = Arrow.mk ((L.ι.app j).toFunctor.map x.hom) :=
          congrArg (fun G : F.obj j ⥤ L.pt ↦ Arrow.mk (G.map x.hom)) hw
        _ = _ := hx
    have hg' : Arrow.mk ((L.ι.app k).toFunctor.map g') = Arrow.mk g := by
      dsimp [g']
      rw [Functor.map_comp, eqToHom_map]
      calc
        _ = Arrow.mk ((L.ι.app k).toFunctor.map ((F.map a).toFunctor.map y.hom)) :=
          Arrow.arrow_mk_eqToHom_comp _ _
        _ = Arrow.mk ((L.ι.app j).toFunctor.map y.hom) :=
          congrArg (fun G : F.obj j ⥤ L.pt ↦ Arrow.mk (G.map y.hom)) hw
        _ = _ := hy
    have hc : Arrow.mk ((L.ι.app k).toFunctor.map (f' ≫ g')) = Arrow.mk (f ≫ g) := by
      rw [Functor.map_comp]
      exact arrow_comp_congr _ _ _ _ hf' hg'
    have hMf : Arrow.mk (M ((L.ι.app k).toFunctor.map f')) = Arrow.mk (M f) :=
      (hM _).trans ((congrArg A hf').trans (hM f).symm)
    have hMg : Arrow.mk (M ((L.ι.app k).toFunctor.map g')) = Arrow.mk (M g) :=
      (hM _).trans ((congrArg A hg').trans (hM g).symm)
    apply Arrow.mk_injective
    calc
      Arrow.mk (M (f ≫ g)) = A (Arrow.mk (f ≫ g)) := hM _
      _ = A (Arrow.mk ((L.ι.app k).toFunctor.map (f' ≫ g'))) := congrArg A hc.symm
      _ = Arrow.mk ((v k).map (f' ≫ g')) := hA k (Arrow.mk (f' ≫ g'))
      _ = Arrow.mk ((v k).map f' ≫ (v k).map g') := by rw [Functor.map_comp]
      _ = Arrow.mk (M ((L.ι.app k).toFunctor.map f') ≫
          M ((L.ι.app k).toFunctor.map g')) :=
        arrow_comp_congr _ _ _ _ (hrep k f').symm (hrep k g').symm
      _ = Arrow.mk (M f ≫ M g) := arrow_comp_congr _ _ _ _ hMf hMg
  let V : L.pt ⥤ D := { obj := O, map := M, map_id := hid, map_comp := hcomp }
  refine ⟨V, fun j ↦ ?_⟩
  apply Functor.hext
  · exact hO j
  · intro X Y f
    exact arrow_hom_heq (hrep j f)

end CategoryTheory

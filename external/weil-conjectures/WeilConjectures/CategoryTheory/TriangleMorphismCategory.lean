/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.IsSaturatedTriangulatedMultiplicativeSystem
public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.Filtered.Final
import WeilConjectures.CategoryTheory.TriangleCommonRefinement
import WeilConjectures.CategoryTheory.Triangulated.DenominatorTriangleCompletion

/-! # Incoming morphisms of distinguished triangles

Source: Stacks Project, Derived Categories, Tag 05R9, dual cofiltered form
(blueprint: lem-pur-triangle-morphism-category-05r9).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

/-- Incoming morphisms of distinguished triangles with all components in `S` form a
cofiltered category, and each vertex projection to the denominator category is initial.
Source: Stacks Project, Derived Categories, Tag 05R9, dual cofiltered form
(blueprint: lem-pur-triangle-morphism-category-05r9).

Proof:
1. Complete any prescribed denominator at a vertex to a morphism of distinguished triangles
   using `lem-pur-triangle-completion-ms6-05r9`. This supplies the existence part of initiality.
2. The identity triangle morphism gives an object by MS1. Common refinements and equalizers
   from `lem-pur-triangle-common-refinement-ms3-05r9` give cofilteredness.
3. For two objects over the same denominator, take a common refinement. MS3 equalizes the
   two induced vertex maps after a further denominator. Complete that denominator to a
   triangle morphism using `lem-pur-triangle-completion-ms6-05r9` and compose by MS1. This
   supplies a connecting span in the costructured arrow category, hence initiality at the
   first vertex. Rotate triangles by TR2 and use MS5 to obtain the other two vertices.

The category is built directly from Mathlib's restricted over-category and full subcategory.
`W` requires all three components to lie in `S`, both for objects and for arrows. The full
subcategory `P` requires the source triangle to be distinguished. The targets `S.Over ⊤ _`
allow every commuting triangle as a morphism, as in Stacks Tag 05Q4. -/
theorem triangle_morphism_category_cofiltered_initial
    {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (S : MorphismProperty C) (hS : S.IsSaturatedMultiplicativeSystem)
    [S.IsCompatibleWithTriangulation] (T : Triangle C) (_hT : T ∈ distTriang C) :
    letI : S.HasLeftCalculusOfFractions := hS.1.1
    let W : MorphismProperty (Triangle C) :=
      S.inverseImage Triangle.π₁ ⊓ (S.inverseImage Triangle.π₂ ⊓ S.inverseImage Triangle.π₃)
    let P : ObjectProperty (W.Over W T) := fun x ↦ x.left ∈ distTriang C
    let p₁ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₁ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₁ x.obj.prop.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₁
        (Triangle.π₁.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    let p₂ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₂ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₂ x.obj.prop.2.1
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₂
        (Triangle.π₂.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    let p₃ : P.FullSubcategory ⥤ S.Over ⊤ T.obj₃ := {
      obj := fun x ↦ MorphismProperty.Over.mk ⊤ x.obj.hom.hom₃ x.obj.prop.2.2
      map := fun f ↦ MorphismProperty.Over.homMk f.hom.left.hom₃
        (Triangle.π₃.congr_map (MorphismProperty.Over.w f.hom))
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
    IsCofiltered P.FullSubcategory ∧ p₁.Initial ∧ p₂.Initial ∧ p₃.Initial := by
  classical
  let : S.HasLeftCalculusOfFractions := hS.1.1
  let : S.HasRightCalculusOfFractions := hS.1.2
  intro W P p₁ p₂ p₃
  obtain ⟨href, heq⟩ := triangle_common_refinement_and_equalization S hS T _hT
  let : Nonempty P.FullSubcategory := ⟨⟨MorphismProperty.Over.mk W (𝟙 T)
    ⟨S.id_mem _, S.id_mem _, S.id_mem _⟩, _hT⟩⟩
  let : IsCofiltered P.FullSubcategory := {
    cone_objs := by
      intro x y
      let D : Bool → Triangle C := fun i ↦ if i then y.obj.left else x.obj.left
      let s : ∀ i : Bool, D i ⟶ T := fun i ↦ by
        cases i
        · exact x.obj.hom
        · exact y.obj.hom
      obtain ⟨U, t, hU, ht₁, ht₂, ht₃, ha⟩ := href Bool D s
        (by
          intro i
          cases i
          · exact x.property
          · exact y.property)
        (by
          intro i
          cases i
          · exact x.obj.prop
          · exact y.obj.prop)
      let z : P.FullSubcategory := ⟨MorphismProperty.Over.mk W t ⟨ht₁, ht₂, ht₃⟩, hU⟩
      obtain ⟨a, ha₁, ha₂, ha₃, haw⟩ := ha false
      obtain ⟨b, hb₁, hb₂, hb₃, hbw⟩ := ha true
      exact ⟨z, ObjectProperty.homMk (MorphismProperty.Over.homMk a haw
        ⟨ha₁, ha₂, ha₃⟩), ObjectProperty.homMk (MorphismProperty.Over.homMk b hbw
        ⟨hb₁, hb₂, hb₃⟩), trivial⟩
    cone_maps := by
      intro x y a b
      obtain ⟨U, r, q, hU, hr₁, hr₂, hr₃, hq₁, hq₂, hq₃, hqw, h₁, h₂, h₃⟩ :=
        heq x.obj.left y.obj.left x.obj.hom y.obj.hom x.property y.property
          x.obj.prop.1 x.obj.prop.2.1 x.obj.prop.2.2
          y.obj.prop.1 y.obj.prop.2.1 y.obj.prop.2.2
          a.hom.left b.hom.left
          a.hom.prop_hom_left.1 a.hom.prop_hom_left.2.1 a.hom.prop_hom_left.2.2
          b.hom.prop_hom_left.1 b.hom.prop_hom_left.2.1 b.hom.prop_hom_left.2.2
          (MorphismProperty.Over.w a.hom) (MorphismProperty.Over.w b.hom)
      let z : P.FullSubcategory := ⟨MorphismProperty.Over.mk W r ⟨hr₁, hr₂, hr₃⟩, hU⟩
      let f : z ⟶ x := ObjectProperty.homMk
        (MorphismProperty.Over.homMk q hqw ⟨hq₁, hq₂, hq₃⟩)
      refine ⟨z, f, ?_⟩
      apply ObjectProperty.hom_ext
      apply MorphismProperty.Over.Hom.ext
      ext
      · exact h₁
      · exact h₂
      · exact h₃ }
  refine ⟨inferInstance, ?_, ?_, ?_⟩
  · apply Functor.initial_of_exists_of_isCofiltered p₁
    · intro d
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₂, hφ₃⟩ :=
        (denominator_triangle_completion S hS T _hT).1 d.left d.hom d.prop
      have hs : S φ.hom₁ := hφ ▸ d.prop
      let x : P.FullSubcategory :=
        ⟨MorphismProperty.Over.mk W φ ⟨hs, hφ₂, hφ₃⟩, hU⟩
      refine ⟨x, ⟨MorphismProperty.Over.homMk (𝟙 _) ?_⟩⟩
      simpa [p₁, x] using hφ.symm
    · intro d c a b
      obtain ⟨X, v, hv, hab⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        a.left b.left d.hom d.prop
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₂, hφ₃⟩ :=
        (denominator_triangle_completion S hS c.obj.left c.property).1 X v hv
      have hs : S φ.hom₁ := hφ ▸ hv
      have hφS : W φ := ⟨hs, hφ₂, hφ₃⟩
      let x : P.FullSubcategory := ⟨MorphismProperty.Over.mk W (φ ≫ c.obj.hom)
        (W.comp_mem _ _ hφS c.obj.prop), hU⟩
      let t : x ⟶ c := ObjectProperty.homMk
        (MorphismProperty.Over.homMk φ rfl hφS)
      refine ⟨x, t, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      change φ.hom₁ ≫ a.left = φ.hom₁ ≫ b.left
      simpa only [hφ] using hab
  · apply Functor.initial_of_exists_of_isCofiltered p₂
    · intro d
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₁, hφ₃⟩ :=
        (denominator_triangle_completion S hS T _hT).2.1 d.left d.hom d.prop
      have hs : S φ.hom₂ := hφ ▸ d.prop
      let x : P.FullSubcategory :=
        ⟨MorphismProperty.Over.mk W φ ⟨hφ₁, hs, hφ₃⟩, hU⟩
      refine ⟨x, ⟨MorphismProperty.Over.homMk (𝟙 _) ?_⟩⟩
      simpa [p₂, x] using hφ.symm
    · intro d c a b
      obtain ⟨X, v, hv, hab⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        a.left b.left d.hom d.prop
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₁, hφ₃⟩ :=
        (denominator_triangle_completion S hS c.obj.left c.property).2.1 X v hv
      have hs : S φ.hom₂ := hφ ▸ hv
      have hφS : W φ := ⟨hφ₁, hs, hφ₃⟩
      let x : P.FullSubcategory := ⟨MorphismProperty.Over.mk W (φ ≫ c.obj.hom)
        (W.comp_mem _ _ hφS c.obj.prop), hU⟩
      let t : x ⟶ c := ObjectProperty.homMk
        (MorphismProperty.Over.homMk φ rfl hφS)
      refine ⟨x, t, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      change φ.hom₂ ≫ a.left = φ.hom₂ ≫ b.left
      simpa only [hφ] using hab
  · apply Functor.initial_of_exists_of_isCofiltered p₃
    · intro d
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₁, hφ₂⟩ :=
        (denominator_triangle_completion S hS T _hT).2.2 d.left d.hom d.prop
      have hs : S φ.hom₃ := hφ ▸ d.prop
      let x : P.FullSubcategory :=
        ⟨MorphismProperty.Over.mk W φ ⟨hφ₁, hφ₂, hs⟩, hU⟩
      refine ⟨x, ⟨MorphismProperty.Over.homMk (𝟙 _) ?_⟩⟩
      simpa [p₃, x] using hφ.symm
    · intro d c a b
      obtain ⟨X, v, hv, hab⟩ := MorphismProperty.HasRightCalculusOfFractions.ext
        a.left b.left d.hom d.prop
        ((MorphismProperty.Over.w a).trans (MorphismProperty.Over.w b).symm)
      obtain ⟨A, B, f, g, h, hU, φ, hφ, hφ₁, hφ₂⟩ :=
        (denominator_triangle_completion S hS c.obj.left c.property).2.2 X v hv
      have hs : S φ.hom₃ := hφ ▸ hv
      have hφS : W φ := ⟨hφ₁, hφ₂, hs⟩
      let x : P.FullSubcategory := ⟨MorphismProperty.Over.mk W (φ ≫ c.obj.hom)
        (W.comp_mem _ _ hφS c.obj.prop), hU⟩
      let t : x ⟶ c := ObjectProperty.homMk
        (MorphismProperty.Over.homMk φ rfl hφS)
      refine ⟨x, t, ?_⟩
      apply MorphismProperty.Over.Hom.ext
      change φ.hom₃ ≫ a.left = φ.hom₃ ≫ b.left
      simpa only [hφ] using hab

end CategoryTheory

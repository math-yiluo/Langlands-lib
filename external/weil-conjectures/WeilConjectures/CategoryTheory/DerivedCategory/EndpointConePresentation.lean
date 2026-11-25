/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.CommutativeSquareLift
import WeilConjectures.CategoryTheory.DerivedCategory.ConeSquareUnrotation

/-! # Cone models with prescribed endpoint components -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false

/-- Two distinguished triangles and a commuting square on their connecting arrows
admit strict mapping-cone models with those first and third components. The middle
component is not prescribed.

Source: Stacks Project, Derived Categories, Tags 014D and 05QK (cone and rotation),
and Tag 05RR (localization of the homotopy category at quasi-isomorphisms).
(blueprint: lem-pc-derived-endpoint-cone-presentation).

Proof: Rotate both triangles twice, so their connecting arrows are the first arrows.
Represent their third vertices and shifted first vertices by complexes. The
calculus of fractions for quasi-isomorphisms in the homotopy category expresses
the two endpoint maps and connecting arrows by roofs. Successive common
refinements of these finitely many roofs give representatives for all four maps,
and a further refinement witnesses the equality of the two composites in the
homotopy category. Choose chain maps representing them and a homotopy for that
equality. Replace the first arrow with the cylinder factorization of Tag 014D (Lemma 13.9.6);
it is a degreewise split injection and the projection is a homotopy equivalence.
Tag 014D (Lemma 13.9.5) changes the second vertical map by a homotopy so the square commutes
strictly. These replacements preserve the four localized vertices and maps.
Take the functorial mapping cones of this strict square. The
resulting third component completes the prescribed endpoint square. Rotate back
twice. The canonical double-cone deformation retractions, with the rotation signs,
identify this rotated diagram with a strict cone diagram of the original first
arrows. Transport to the two original distinguished triangles using their cone
isomorphisms. The isomorphisms agree at the prescribed first and third vertices;
the middle isomorphisms are supplied by the cone comparison. The four first-arrow
and cone-inclusion identities follow from these triangle isomorphisms. The first
and cone components are the specified maps because they came from the initial
strictification. No requirement is made on the middle component, which is essential.
This applies to zero objects and split triangles without any extra assumption. -/
theorem derived_endpoint_cone_presentation
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (T T' : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang (DerivedCategory C))
    (hT' : T' ∈ distTriang (DerivedCategory C))
    (a : T.obj₁ ⟶ T'.obj₁) (c : T.obj₃ ⟶ T'.obj₃)
    (h : T.mor₃ ≫ a⟦(1 : ℤ)⟧' =
      c ≫ T'.mor₃) :
    ∃ (A B A' B' : CochainComplex C ℤ)
      (t : A ⟶ B) (t' : A' ⟶ B') (α : A ⟶ A') (β : B ⟶ B')
      (hc : t ≫ β = α ≫ t')
      (e₁ : DerivedCategory.Q.obj A ≅ T.obj₁)
      (e₂ : DerivedCategory.Q.obj B ≅ T.obj₂)
      (e₃ : DerivedCategory.Q.obj (CochainComplex.mappingCone t) ≅ T.obj₃)
      (e₁' : DerivedCategory.Q.obj A' ≅ T'.obj₁)
      (e₂' : DerivedCategory.Q.obj B' ≅ T'.obj₂)
      (e₃' : DerivedCategory.Q.obj (CochainComplex.mappingCone t') ≅ T'.obj₃),
      DerivedCategory.Q.map t ≫ e₂.hom = e₁.hom ≫ T.mor₁ ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr t) ≫ e₃.hom =
        e₂.hom ≫ T.mor₂ ∧
      DerivedCategory.Q.map t' ≫ e₂'.hom = e₁'.hom ≫ T'.mor₁ ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.inr t') ≫ e₃'.hom =
        e₂'.hom ≫ T'.mor₂ ∧
      DerivedCategory.Q.map α ≫ e₁'.hom = e₁.hom ≫ a ∧
      DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫ e₃'.hom =
        e₃.hom ≫ c := by
  obtain ⟨K, L, K', L', g, g', s, r, hs, eX, eY, eX', eY', hg, hg', ha, hb⟩ :=
    derived_commutative_square_lift T.mor₃ T'.mor₃ c (a⟦(1 : ℤ)⟧') h
  let e := isoTriangleOfIso₁₂ _ T.rotate.rotate
    (DerivedCategory.mappingCone_triangle_distinguished g)
    (rot_of_distTriang _ (rot_of_distTriang _ hT)) eX eY hg
  let e' := isoTriangleOfIso₁₂ _ T'.rotate.rotate
    (DerivedCategory.mappingCone_triangle_distinguished g')
    (rot_of_distTriang _ (rot_of_distTriang _ hT')) eX' eY' hg'
  let t := (CochainComplex.mappingCone.inr g)⟦(-1 : ℤ)⟧'
  let t' := (CochainComplex.mappingCone.inr g')⟦(-1 : ℤ)⟧'
  let α := r⟦(-1 : ℤ)⟧'
  let β := (CochainComplex.mappingCone.map g g' s r hs)⟦(-1 : ℤ)⟧'
  have hc : t ≫ β = α ≫ t' := by
    dsimp only [t, t', α, β]
    rw [← Functor.map_comp, ← Functor.map_comp]
    have hh : CochainComplex.mappingCone.inr g ≫
        CochainComplex.mappingCone.map g g' s r hs = r ≫ CochainComplex.mappingCone.inr g' :=
      (CochainComplex.mappingCone.triangleMap g g' s r hs).comm₂
    rw [hh]
  obtain ⟨d, d', hα, hγ⟩ :=
    derived_cone_square_unrotation g g' s r hs T T' e e' hc
  refine ⟨_, _, _, _, t, t', α, β, hc,
    Triangle.π₁.mapIso d, Triangle.π₂.mapIso d, Triangle.π₃.mapIso d,
    Triangle.π₁.mapIso d', Triangle.π₂.mapIso d', Triangle.π₃.mapIso d',
    d.hom.comm₁, d.hom.comm₂, d'.hom.comm₁, d'.hom.comm₂, ?_, ?_⟩
  · change DerivedCategory.Q.map α ≫ d'.hom.hom₁ = d.hom.hom₁ ≫ a
    apply (shiftFunctor (DerivedCategory C) (1 : ℤ)).map_injective
    rw [hα, Functor.map_comp]
    have hr : DerivedCategory.Q.map r ≫ e'.hom.hom₂ =
        e.hom.hom₂ ≫ a⟦(1 : ℤ)⟧' := by simpa [e, e'] using hb
    simp only [hr, Iso.inv_hom_id_triangle_hom₂_assoc]
  · change DerivedCategory.Q.map (CochainComplex.mappingCone.map t t' α β hc) ≫
      d'.hom.hom₃ = d.hom.hom₃ ≫ c
    rw [hγ]
    have hr : DerivedCategory.Q.map s ≫ e'.hom.hom₁ = e.hom.hom₁ ≫ c := by
      simpa [e, e'] using ha
    simp only [hr, Iso.inv_hom_id_triangle_hom₁_assoc]

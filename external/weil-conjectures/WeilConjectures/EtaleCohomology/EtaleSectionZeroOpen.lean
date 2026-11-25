/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion

/-! # The zero locus of an étale section is Zariski open

Source: Stacks Project, Tag 04FR (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor AlgebraicGeometry

namespace AlgebraicGeometry.Scheme

/-- The zero locus theorem for a section of an abelian sheaf on the small étale site.
Source: Stacks Project, Tag 04FR, clauses (1)--(3) (auxiliary; not a blueprint node).

Proof:
1. Form the union of the open subschemes where `s` restricts to zero. Open immersions
are étale by `definition-torsion-sheaves--3`, so these are site objects.
The sheaf condition (`situation-conventions`) gives zero on this union,
including an empty union; maximality follows from the construction.
2. Every site arrow is étale by cancellation. Its image is open by
`lem-weil-pbc-etale-morphism-open-map`, and the map onto that image is a singleton
étale cover. Sheaf separatedness descends vanishing to the image. Conversely,
containment in the union gives factorization and hence zero restriction.
3. Compute the geometric stalk (`def-weil-pbc-geometric-stalks`) using a small
cofinal family of affine pointed neighbourhoods. Representatives exist by
`lem-weil-pbc-affine-etale-essentially-small-cover`; an affine open around the lifted
point refines any neighbourhood. Cofilteredness follows from
`definition-torsion-sheaves--3`, and
`lem-weil-pbc-colimit-initial-full-subcategory` identifies the small colimit and its
coprojections with the stalk. Restrict `s` to a pointed affine refinement of `V`.
4. If the germ is zero, regard the abelian groups as integer modules and apply
`lem-weil-pbc-filtered-colimit-modules-elementwise`: some pointed refinement has zero
restriction. Its image lies in the union by step 2, so the geometric point lies there.
5. Conversely, a geometric point in the union factors through its open immersion.
The stalk coprojections identify the germ of `s` with that of its zero restriction.
-/
theorem etale_section_zero_open
    (T : Scheme.{u})
    (F : Sheaf (T.smallEtaleTopology) AddCommGrpCat.{u + 1})
    (V : T.Etale)
    (s : (F.1.obj (Opposite.op V) : AddCommGrpCat.{u + 1}).carrier)
    : ∃ (W : T.Etale) (i : W ⟶ V),
        IsOpenImmersion i.left ∧
        (∀ (V' : T.Etale) (h : V' ⟶ V),
          (F.1.map h.op) s = 0 ↔ Set.range h.left ⊆ Set.range i.left) ∧
        (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω]
          (v : Spec (.of Ω) ⟶ V.left),
          (pointSmallEtale (v ≫ V.hom)).toPresheafFiber V (Over.homMk v) F.1 s = 0 ↔
            ∃ (y : Spec (.of Ω) ⟶ W.left), y ≫ i.left = v) := by
  classical
  let G :=
    (sheafCompose T.smallEtaleTopology
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj F
  let z : G.obj.obj (Opposite.op V) :=
    (0 : (F.obj.obj (Opposite.op V) : AddCommGrpCat.{u + 1}).carrier)
  obtain ⟨W, hW⟩ := exists_etaleSections_equal_open_etale_criterion T G V s z
  let i : Scheme.Etale.mk (W.ι ≫ V.hom) ⟶ V := MorphismProperty.Over.homMk W.ι rfl
  refine ⟨Scheme.Etale.mk (W.ι ≫ V.hom), i, ?_, ?_, ?_⟩
  · change IsOpenImmersion W.ι
    infer_instance
  · intro V' h
    have hh := hW V' h
    change (F.obj.map h.op) s = 0 ↔ _
    have hh' := hh.symm
    change (CategoryTheory.forget AddCommGrpCat).map (F.obj.map h.op) s =
      (CategoryTheory.forget AddCommGrpCat).map (F.obj.map h.op) z ↔ _ at hh'
    rw [show (F.obj.map h.op) s = 0 ↔
        (CategoryTheory.forget AddCommGrpCat).map (F.obj.map h.op) s =
          (CategoryTheory.forget AddCommGrpCat).map (F.obj.map h.op) z from by
      simp [z]]
    have hirange : Set.range i.left = (W : Set V.left) := by
      change Set.range W.ι = (W : Set V.left)
      exact Scheme.Opens.range_ι W
    rw [hirange]
    simpa [z] using hh'
  · intro Ω _ _ v
    let Φ := pointSmallEtale (v ≫ V.hom)
    let z₀ : Φ.fiber.obj V := Over.homMk v rfl
    have : PreservesFilteredColimitsOfSize.{u, u}
        (CategoryTheory.forget AddCommGrpCat.{u + 1}) :=
      preservesFilteredColimitsOfSize_shrink.{u, u + 1, u, u + 1} _
    constructor
    · intro hs
      have heq : Φ.toPresheafFiber V z₀ F.obj s =
          Φ.toPresheafFiber V z₀ F.obj 0 := by
        simpa only [map_zero] using hs
      obtain ⟨V', k, w, hw, hk⟩ :=
        (Φ.toPresheafFiber_eq_iff' (P := F.obj) V z₀ s 0).mp heq
      have hk0 : (F.obj.map k.op) s = 0 := by
        simpa only [map_zero] using hk
      have hkw : Set.range k.left ⊆ (W : Set V.left) := by
        have hh := (hW V' k).2
        have hkeq : (ConcreteCategory.hom (G.obj.map k.op)) s =
            (ConcreteCategory.hom (G.obj.map k.op)) z := by
          change (F.obj.map k.op) s = (F.obj.map k.op) (0 : _)
          simp [hk0]
        exact hh hkeq
      have hvw : Set.range v ⊆ (W : Set V.left) := by
        rintro x ⟨q, rfl⟩
        have hw' := congrArg (fun a => a.left) hw
        change w.left ≫ k.left = v at hw'
        have hq : k.left (w.left q) ∈ (W : Set V.left) :=
          hkw ⟨w.left q, rfl⟩
        have hx' := congrArg (fun a => a q) hw'
        have hx'' : v q = k.left (w.left q) := by
          exact hx'.symm
        exact hx'' ▸ hq
      have hvw' : Set.range v ⊆ Set.range W.ι := by
        rw [Scheme.Opens.range_ι]
        exact hvw
      refine ⟨IsOpenImmersion.lift W.ι v hvw',
        IsOpenImmersion.lift_fac _ _ _⟩
    · rintro ⟨y, hy⟩
      let zW : Φ.fiber.obj (Scheme.Etale.mk (W.ι ≫ V.hom)) :=
        Over.homMk y (by
          change y ≫ W.ι ≫ V.hom = v ≫ V.hom
          simpa [i] using congrArg (fun a => a ≫ V.hom) hy)
      have hmap : (F.obj.map i.op) s = 0 := by
        have hh := (hW (Scheme.Etale.mk (W.ι ≫ V.hom)) i).1
        have hsub : Set.range i.left ⊆ (W : Set V.left) := by
          change Set.range W.ι ⊆ (W : Set V.left)
          rw [Scheme.Opens.range_ι]
        have hh' := hh hsub
        change (CategoryTheory.forget AddCommGrpCat).map (F.obj.map i.op) s =
          (CategoryTheory.forget AddCommGrpCat).map (F.obj.map i.op) z at hh'
        simpa [z] using hh'
      have hfiber : Φ.fiber.map i zW = z₀ := by
        apply Over.OverMorphism.ext
        change y ≫ i.left = v
        exact hy
      have hn := Φ.toPresheafFiber_w i zW F.obj
      have hn' := ConcreteCategory.congr_hom hn s
      change (Φ.toPresheafFiber _ zW F.obj) ((F.obj.map i.op) s) =
        (Φ.toPresheafFiber V (Φ.fiber.map i zW) F.obj) s at hn'
      rw [hmap, map_zero, hfiber] at hn'
      simpa using hn'.symm

end AlgebraicGeometry.Scheme

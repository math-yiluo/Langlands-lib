/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive

import Mathlib.CategoryTheory.Comma.StructuredArrow.Small

/-!
# Objectwise tensor product and internal hom of presheaves

Source: the Weil conjectures blueprint, `chap-The-pro-etale-site`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-presheaf.md`, clauses 1--2 and
both Hom formulas (blueprint: det-def-sfb-sheaf-tensor-presheaf).

The tensor is Mathlib's `Monoidal.functorCategoryMonoidal`; its symmetry is
`Monoidal.functorCategorySymmetric`. The internal hom is the existing
`Enriched.FunctorCategory.functorEnrichedHom`, not a second construction.
The only missing interface is existence of its ends for a possibly large essentially
small site. The theorem below supplies the global and slice end instances. With these,
`MonoidalClosed.FunctorCategory.monoidalClosed`,
`Presheaf.functorEnrichedHomCoyonedaObjEquiv`, and
`MonoidalClosed.FunctorCategory.homEquiv` give the remaining clauses of the node.
-/

@[expose] public section

universe uC vC uA vA w

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.MonoidalClosed

namespace CategoryTheory

/-- Extend the canonical small-model end along preimage isomorphisms and verify
its universal property. This implements steps 2–3 of the presheaf tensor node.
Source: `det-def-sfb-sheaf-tensor-presheaf`, clause 2; the projection transport
calculation is also used in the upstream `precompEnrichedHomInv`. -/
private theorem hasEnrichedHom_of_essentiallySmall
    {J : Type uC} [Category.{vC} J] [EssentiallySmall.{w} J]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [MonoidalClosed A] (F G : J ⥤ A) :
    Enriched.FunctorCategory.HasEnrichedHom A F G :=
  open Category MonoidalCategory Enriched Enriched.FunctorCategory in
  by
  let E := (equivSmallModel.{w} J).inverse
  let : HasEnrichedHom A (E ⋙ F) (E ⋙ G) := inferInstance
  let p := fun j ↦ enrichedHomπ A (E ⋙ F) (E ⋙ G) (E.objPreimage j) ≫
    eHomWhiskerRight A (F.map (E.objObjPreimageIso j).inv) _ ≫
    eHomWhiskerLeft A _ (G.map (E.objObjPreimageIso j).hom)
  have hp : ∀ ⦃i j : J⦄ (f : i ⟶ j),
      p i ≫ (diagram A F G |>.obj (Opposite.op i)).map f =
        p j ≫ ((diagram A F G).map f.op).app j := by
    intro i j f
    dsimp only [p]
    simp only [diagram_obj_map, diagram_map_app, Quiver.Hom.unop_op]
    let g := E.preimage ((E.objObjPreimageIso i).hom ≫ f ≫ (E.objObjPreimageIso j).inv)
    have hg : E.map g = (E.objObjPreimageIso i).hom ≫ f ≫
        (E.objObjPreimageIso j).inv := E.map_preimage _
    have h1 : (E.objObjPreimageIso i).hom ≫ f =
        E.map g ≫ (E.objObjPreimageIso j).hom := by simp [hg]
    have h2 : (E.objObjPreimageIso i).inv ≫ E.map g =
        f ≫ (E.objObjPreimageIso j).inv := by simp [hg]
    have hc := enrichedHom_condition A (E ⋙ F) (E ⋙ G) g
    simp only [Functor.comp_map, Functor.comp_obj] at hc
    simp only [assoc]
    rw [← eHomWhiskerLeft_comp, ← G.map_comp, h1, G.map_comp, eHomWhiskerLeft_comp,
      ← eHom_whisker_exchange_assoc, reassoc_of% hc, ← eHomWhiskerRight_comp_assoc,
      ← F.map_comp, h2, eHom_whisker_exchange, F.map_comp, eHomWhiskerRight_comp_assoc]
    rfl
  let W : Wedge (diagram A F G) := Wedge.mk _ p hp
  refine ⟨⟨⟨W, ?_⟩⟩⟩
  let lift := fun s : Wedge (diagram A F G) ↦
    end_.lift (F := diagram A (E ⋙ F) (E ⋙ G)) (fun k ↦ s.ι (E.obj k))
      (fun i j f ↦ by simpa using Wedge.condition s (E.map f))
  refine Multifork.IsLimit.mk _ lift ?_ ?_
  · intro s j
    change J at j
    change lift s ≫ p j = s.ι j
    dsimp only [lift, p]
    rw [← assoc, ← assoc, end_.lift_π]
    have hc := Wedge.condition s (E.objObjPreimageIso j).hom
    simp only [diagram_obj_map, diagram_map_app, Quiver.Hom.unop_op] at hc
    simp only [assoc]
    rw [← eHom_whisker_exchange, reassoc_of% hc, ← eHomWhiskerRight_comp,
      ← F.map_comp, Iso.inv_hom_id, F.map_id, eHomWhiskerRight_id]
    exact Category.comp_id _
  · intro s m hm
    change s.pt ⟶ enrichedHom A (E ⋙ F) (E ⋙ G) at m
    apply end_.hom_ext (F := diagram A (E ⋙ F) (E ⋙ G))
    intro k
    dsimp only [lift]
    rw [end_.lift_π]
    have hc := enrichedHom_condition A (E ⋙ F) (E ⋙ G)
      (E.preimage (E.objObjPreimageIso (E.obj k)).hom)
    simp only [Functor.comp_map, Functor.comp_obj, Functor.map_preimage] at hc
    have h := hm (E.obj k)
    change m ≫ p (E.obj k) = s.ι (E.obj k) at h
    rw [← h]
    dsimp only [p]
    rw [← eHom_whisker_exchange, reassoc_of% hc, ← eHomWhiskerRight_comp,
      ← F.map_comp, Iso.inv_hom_id, F.map_id, eHomWhiskerRight_id, comp_id]

/-- Existence of the global and slice ends used by the canonical presheaf internal hom.
The first family supplies the enriched bifunctor used by the closed structure, and the
second supplies the end at every object of the site. Neither the object universe of the
site nor either coefficient universe is identified with the smallness universe `w`.

Source: the Weil conjectures blueprint, `chap-The-pro-etale-site`,
`sk-def-sfb-sheaf-tensor/det-def-sfb-sheaf-tensor-presheaf.md`, clause 2 and both
Hom formulas (blueprint: det-def-sfb-sheaf-tensor-presheaf).

Proof of the node, following its seven steps:
1. Use the pointwise tensor on functors: objects and arrows are tensor products of their
components, the unit is constant, and associators, unitors and symmetry are componentwise.
The coefficient coherence identities prove the presheaf identities after evaluation.
2. Choose a small full subcategory meeting every isomorphism class of the site. For a
fixed `U`, its arrows into `U` form a small full subcategory of `C/U` meeting every
isomorphism class, since the Hom sets are `w`-small. The same applies to `C` itself.
3. For either indexing category, take the equalizer of the two product maps between the
diagonal internal Homs and the mixed internal Homs indexed by arrows. The required small
products and equalizer exist by `lem-coef-grothendieck-small-limits`. Their universal
property identifies maps into this object with wedges. Extend a wedge from the small full
subcategory along chosen isomorphisms. The wedge equation makes this independent of the
isomorphism chosen and enforces the equation on every arrow. Thus it is an end over the
whole category, even when that category has a larger object universe. This proves the two
end-existence families stated below, without choosing an undetermined object.
4. For `u : U' ⟶ U`, reindex the wedge by composition `C/U' ⥤ C/U`. Uniqueness of maps to
the end proves the restriction identity and composition laws. Pre- and postcomposition
supply the contravariance in `F` and covariance in `G`.
5. Curry each wedge projection using the coefficient tensor--Hom adjunction. The wedge
equation becomes naturality of the maps `F(V) ⊗ B ⟶ G(V)` on the slice. Uncurrying is
inverse, giving `Presheaf.functorEnrichedHomCoyonedaObjEquiv` and compatibility with
restriction in `U`.
6. A transformation `χ : F ⊗ H ⟶ G` gives the local family at `U` whose component at
`v : V ⟶ U` is `F(V) ◁ H(v)` followed by `χ.app V`. Naturality of `χ` gives the wedge
equation, and uniqueness of maps to the end makes these families natural in `U`.
7. Conversely evaluate the family of `ψ : H ⟶ [F,G]` at the identity arrow of each slice.
Naturality of `ψ` recovers its other components; the wedge condition gives naturality of
`χ`. The constructions are inverse, and pre- and postcomposition commute with them.
This is `MonoidalClosed.FunctorCategory.homEquiv`, natural in all three variables, and
`MonoidalClosed.FunctorCategory.adj` gives the stated closed structure.
-/
theorem presheaf_enrichedHoms_exist
    {C : Type uC} [Category.{vC} C] [EssentiallySmall.{w} C]
    {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{w} A]
    [MonoidalCategory A] [SymmetricCategory A] [MonoidalClosed A]
    [MonoidalPreadditive A] :
    (∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasEnrichedHom A F G) ∧
      (∀ (F G : Cᵒᵖ ⥤ A), Enriched.FunctorCategory.HasFunctorEnrichedHom A F G) := by
  constructor
  · intro F G
    exact hasEnrichedHom_of_essentiallySmall F G
  · intro F G U
    have : LocallySmall.{w} Cᵒᵖ := locallySmall_of_essentiallySmall Cᵒᵖ
    have : EssentiallySmall.{w} (Under U) :=
      inferInstanceAs (EssentiallySmall.{w} (StructuredArrow U (𝟭 Cᵒᵖ)))
    exact hasEnrichedHom_of_essentiallySmall (Under.forget U ⋙ F) (Under.forget U ⋙ G)

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful

/-! # Identifying a completed arrow by its whole-system equation

Source: blueprint coefficient changes, paragraph (3).
-/

@[expose] public section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- An endpoint transported through a fully faithful realization, using the
specified source and target realizations and the prescribed realized endpoint.
Source: blueprint coefficient changes (3), realization
(blueprint: lem-diagonal-completed-arrow-transport). -/
noncomputable def diagonalTransportedEndpoint
    {C C' E E' : Type*}
    [Category C] [Category C'] [Category E] [Category E']
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    [F'.Full] [F'.Faithful] (e : P ⋙ F' ≅ F ⋙ V)
    {X : C} {X' : C'} {A : E} {A' : E'}
    (s : F.obj X ≅ A) (s' : F'.obj X' ≅ A') (a : V.obj A ≅ A') :
    P.obj X ≅ X' :=
  F'.preimageIso (e.app X ≪≫ V.mapIso s ≪≫ a ≪≫ s'.symm)

/-- Transport through a fully faithful realization satisfies the full endpoint
square, by cancellation of the target realization.
Source: blueprint coefficient changes (3), realization
(blueprint: lem-diagonal-completed-arrow-transport).
Proof: apply the defining preimage equation, expand the composite isomorphism,
and cancel the inverse target realization with its forward map. -/
theorem diagonalTransportedEndpoint_normalization
    {C C' E E' : Type*}
    [Category C] [Category C'] [Category E] [Category E']
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    [F'.Full] [F'.Faithful] (e : P ⋙ F' ≅ F ⋙ V)
    {X : C} {X' : C'} {A : E} {A' : E'}
    (s : F.obj X ≅ A) (s' : F'.obj X' ≅ A') (a : V.obj A ≅ A') :
    e.hom.app X ≫ V.map s.hom ≫ a.hom =
      F'.map (diagonalTransportedEndpoint P F F' V e s s' a).hom ≫ s'.hom := by
  simp only [diagonalTransportedEndpoint, Functor.preimageIso_hom,
    Functor.map_preimage, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The full realization equation for a transported mapped endpoint.
Source: blueprint coefficient changes (3), realization
(blueprint: lem-diagonal-completed-arrow-transport). -/
def DiagonalTransportedEndpointMapProperty
    {C C' E E' D : Type*}
    [Category C] [Category C'] [Category E] [Category E'] [Category D]
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    (e : P ⋙ F' ≅ F ⋙ V)
    {X : C} {X' : C'} {A : E} {M N : D}
    (s : F.obj X ≅ A) (G : D ⥤ E') (s' : F'.obj X' ≅ G.obj N)
    (a : V.obj A ≅ G.obj M) (b : M ≅ N)
    (i : P.obj X ≅ X') : Prop :=
  e.hom.app X ≫ V.map s.hom ≫ a.hom ≫ G.map b.hom = F'.map i.hom ≫ s'.hom

/-- The directly transported mapped endpoint satisfies its named normalization.
Source: blueprint coefficient changes (3), realization
(blueprint: lem-diagonal-completed-arrow-transport).
Proof: apply the preimage normalization to the composite endpoint and expand its hom. -/
theorem diagonalTransportedEndpointMap_normalization
    {C C' E E' D : Type*}
    [Category C] [Category C'] [Category E] [Category E'] [Category D]
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    [F'.Full] [F'.Faithful] (e : P ⋙ F' ≅ F ⋙ V)
    {X : C} {X' : C'} {A : E} {M N : D}
    (s : F.obj X ≅ A) (G : D ⥤ E') (s' : F'.obj X' ≅ G.obj N)
    (a : V.obj A ≅ G.obj M) (b : M ≅ N) :
    DiagonalTransportedEndpointMapProperty P F F' V e s G s' a b
      (diagonalTransportedEndpoint P F F' V e s s' (a ≪≫ G.mapIso b)) := by
  simpa only [DiagonalTransportedEndpointMapProperty, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc] using
      diagonalTransportedEndpoint_normalization P F F' V e s s' (a ≪≫ G.mapIso b)

/-- Scalar comparison and uniqueness of a completed lift recover a completed
square from its entire restricted square.

Source: blueprint coefficient changes (3), identification of completed arrows.
(blueprint: lem-diagonal-completed-arrow-transport).

Proof: conjugate the pulled arrow by the source and target isomorphisms.
Naturality of scalar comparison identifies its restriction with the given new
arrow. The uniqueness clause identifies these two completed arrows. Cancel the
source isomorphism to obtain the completed square. -/
theorem diagonalCompletedArrow_of_restricted_square
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (r : C ⥤ D) (r' : C' ⥤ D') (P : C ⥤ C') (U : D ⥤ D')
    (e : r ⋙ U ≅ P ⋙ r')
    {X Y : C} {X' Y' : C'}
    (a : P.obj X ≅ X') (b : P.obj Y ≅ Y')
    (δ : X ⟶ Y) (δ' : X' ⟶ Y')
    (h : U.map (r.map δ) ≫ e.hom.app Y ≫ r'.map b.hom =
      (e.hom.app X ≫ r'.map a.hom) ≫ r'.map δ')
    (unique : ∀ z : X' ⟶ Y', r'.map z = r'.map δ' → z = δ') :
    P.map δ ≫ b.hom = a.hom ≫ δ' := by
  have he := e.hom.naturality δ
  change U.map (r.map δ) ≫ e.hom.app Y = e.hom.app X ≫ r'.map (P.map δ) at he
  have hh : r'.map (P.map δ ≫ b.hom) = r'.map (a.hom ≫ δ') := by
    apply (cancel_epi (e.hom.app X)).1
    calc
      e.hom.app X ≫ r'.map (P.map δ ≫ b.hom) =
          U.map (r.map δ) ≫ e.hom.app Y ≫ r'.map b.hom := by
        simpa only [Functor.map_comp, Category.assoc] using
          (congrArg (fun z ↦ z ≫ r'.map b.hom) he).symm
      _ = e.hom.app X ≫ r'.map (a.hom ≫ δ') := by
        simpa only [Functor.map_comp, Category.assoc] using h
  have hz : a.inv ≫ P.map δ ≫ b.hom = δ' := by
    apply unique
    calc
      r'.map (a.inv ≫ P.map δ ≫ b.hom) =
          r'.map a.inv ≫ r'.map (P.map δ ≫ b.hom) := by rw [r'.map_comp]
      _ = r'.map a.inv ≫ r'.map (a.hom ≫ δ') := by rw [hh]
      _ = r'.map δ' := by
        rw [← r'.map_comp, ← Category.assoc, a.inv_hom_id, Category.id_comp]
  have hz' := congrArg (fun z ↦ a.hom ≫ z) hz
  simpa only [← Category.assoc, a.hom_inv_id, Category.id_comp] using hz'

/-- A comparison of realization functors carries any completed arrow square
through prescribed source and target realization endpoints.

Source: blueprint coefficient changes (3), final realization.
(blueprint: lem-diagonal-completed-arrow-transport).

Proof: expand the realized arrow using its source and target isomorphisms.
The source endpoint equation cancels the inverse source realization. Naturality
of the functor comparison moves the arrow to the new realization. Substitute the
completed square, then use the target endpoint equation. -/
theorem diagonalCompletedArrow_realize
    {C C' E E' : Type*}
    [Category C] [Category C'] [Category E] [Category E']
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    (e : P ⋙ F' ≅ F ⋙ V)
    {X Y : C} {X' Y' : C'} {A B : E} {A' B' : E'}
    (s : F.obj X ≅ A) (t : F.obj Y ≅ B)
    (s' : F'.obj X' ≅ A') (t' : F'.obj Y' ≅ B')
    (a : P.obj X ≅ X') (b : P.obj Y ≅ Y')
    (α : V.obj A ⟶ A') (β : V.obj B ⟶ B')
    (hs : e.hom.app X ≫ V.map s.hom ≫ α = F'.map a.hom ≫ s'.hom)
    (ht : e.hom.app Y ≫ V.map t.hom ≫ β = F'.map b.hom ≫ t'.hom)
    (δ : X ⟶ Y) (δ' : X' ⟶ Y')
    (hδ : P.map δ ≫ b.hom = a.hom ≫ δ') :
    V.map (s.inv ≫ F.map δ ≫ t.hom) ≫ β =
      α ≫ s'.inv ≫ F'.map δ' ≫ t'.hom := by
  have hv : V.map s.hom ≫ V.map s.inv = 𝟙 _ := by
    rw [← V.map_comp, s.hom_inv_id, V.map_id]
  have hs' : F'.map a.hom = e.hom.app X ≫ V.map s.hom ≫ α ≫ s'.inv := by
    have h := congrArg (fun z ↦ z ≫ s'.inv) hs
    simpa only [Category.assoc, s'.hom_inv_id, Category.comp_id] using h.symm
  apply (cancel_epi (e.hom.app X ≫ V.map s.hom)).1
  calc
    (e.hom.app X ≫ V.map s.hom) ≫
        (V.map (s.inv ≫ F.map δ ≫ t.hom) ≫ β) =
      e.hom.app X ≫ V.map (F.map δ) ≫ V.map t.hom ≫ β := by
        simp only [Functor.map_comp, Category.assoc]
        rw [reassoc_of% hv]
    _ = F'.map (P.map δ) ≫ e.hom.app Y ≫ V.map t.hom ≫ β := by
      simpa only [Functor.comp_map, Category.assoc] using
        congrArg (fun z ↦ z ≫ V.map t.hom ≫ β) (e.hom.naturality δ).symm
    _ = F'.map (P.map δ) ≫ F'.map b.hom ≫ t'.hom := by
      simpa only [Category.assoc] using congrArg (fun z ↦ F'.map (P.map δ) ≫ z) ht
    _ = F'.map a.hom ≫ F'.map δ' ≫ t'.hom := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ F'.map z ≫ t'.hom) hδ
    _ = (e.hom.app X ≫ V.map s.hom) ≫
        (α ≫ s'.inv ≫ F'.map δ' ≫ t'.hom) := by
      simpa only [Category.assoc] using
        congrArg (fun z ↦ z ≫ F'.map δ' ≫ t'.hom) hs'

/-- Realize a completed square with a mapped source endpoint, retaining its named
normalization predicate until the category parameters are abstract.

Source: blueprint coefficient changes (3), supported-source realization.
(blueprint: lem-diagonal-completed-arrow-transport).

Proof: unfold the named source normalization in abstract categories, apply the
realization diagram chase, and reassociate the two factors of the source map. -/
theorem diagonalCompletedMappedArrow_realize
    {C C' E E' D : Type*}
    [Category C] [Category C'] [Category E] [Category E'] [Category D]
    (P : C ⥤ C') (F : C ⥤ E) (F' : C' ⥤ E') (V : E ⥤ E')
    (e : P ⋙ F' ≅ F ⋙ V)
    {X Y : C} {X' Y' : C'} {A B : E} {B' : E'} {M N : D}
    (s : F.obj X ≅ A) (t : F.obj Y ≅ B)
    (G : D ⥤ E') (s' : F'.obj X' ≅ G.obj N) (t' : F'.obj Y' ≅ B')
    (a : P.obj X ≅ X') (b : P.obj Y ≅ Y')
    (q : V.obj A ≅ G.obj M) (r : M ≅ N) (β : V.obj B ⟶ B')
    (hs : DiagonalTransportedEndpointMapProperty P F F' V e s G s' q r a)
    (ht : e.hom.app Y ≫ V.map t.hom ≫ β = F'.map b.hom ≫ t'.hom)
    (δ : X ⟶ Y) (δ' : X' ⟶ Y')
    (hδ : P.map δ ≫ b.hom = a.hom ≫ δ') :
    V.map (s.inv ≫ F.map δ ≫ t.hom) ≫ β =
      q.hom ≫ G.map r.hom ≫ s'.inv ≫ F'.map δ' ≫ t'.hom := by
  have h := diagonalCompletedArrow_realize P F F' V e s t s' t' a b
    (q.hom ≫ G.map r.hom) β hs ht δ δ' hδ
  simpa only [Category.assoc] using h

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

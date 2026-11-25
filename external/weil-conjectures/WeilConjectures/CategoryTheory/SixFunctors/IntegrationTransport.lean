/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Iso

/-! # Transport of a trace integration identity

Source: diagonal tower coefficient changes, proof paragraphs (1)--(2).
(blueprint: lem-diagonal-coefficient-integration-transport).
-/

@[expose] public section
set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
open CategoryTheory
namespace CategoryTheory

/-- A natural direct-image comparison carries an integration identity through
its source, class and trace squares. Only the unit comparison needs to be
invertible for this implication; no general preservation of inverse limits or
base-change theorem is used.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraphs (1)--(2).
(blueprint: lem-diagonal-coefficient-integration-transport).

Proof: precompose the desired identity by the unit isomorphism. Use the
supported-source square, the class square, naturality of the direct-image
comparison, and the trace square, in that order. The result is the image of
the original integration composite, hence the identity. Cancel the unit
isomorphism. This also works for zero objects and for noninvertible comparison
components away from the coefficient unit. -/
theorem integration_transport
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    (F : C ⥤ D) (F' : C' ⥤ D') (U : C ⥤ C') (V : D ⥤ D')
    (mate : F ⋙ V ⟶ U ⋙ F')
    {S L : C} {T : D} {S' L' : C'} {T' : D'}
    (s : U.obj S ⟶ S') (line : U.obj L ⟶ L') (e : V.obj T ≅ T')
    (a : T ⟶ F.obj S) (delta : S ⟶ L) (trace : F.obj L ⟶ T)
    (a' : T' ⟶ F'.obj S') (delta' : S' ⟶ L') (trace' : F'.obj L' ⟶ T')
    (hsource : V.map a ≫ mate.app S ≫ F'.map s = e.hom ≫ a')
    (hdelta : U.map delta ≫ line = s ≫ delta')
    (htrace : V.map trace ≫ e.hom = mate.app L ≫ F'.map line ≫ trace')
    (h : a ≫ F.map delta ≫ trace = 𝟙 T) :
    a' ≫ F'.map delta' ≫ trace' = 𝟙 T' := by
  apply (cancel_epi e.hom).1
  have hn := mate.naturality delta
  change V.map (F.map delta) ≫ mate.app L = mate.app S ≫ F'.map (U.map delta) at hn
  calc
    e.hom ≫ (a' ≫ F'.map delta' ≫ trace') =
        V.map a ≫ mate.app S ≫ F'.map (s ≫ delta') ≫ trace' := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ z ≫ F'.map delta' ≫ trace') hsource.symm
    _ = V.map a ≫ mate.app S ≫ F'.map (U.map delta ≫ line) ≫ trace' := by
      rw [hdelta]
    _ = V.map a ≫ V.map (F.map delta) ≫ mate.app L ≫ F'.map line ≫ trace' := by
      simpa only [Functor.map_comp, Category.assoc] using
        congrArg (fun z ↦ V.map a ≫ z ≫ F'.map line ≫ trace') hn.symm
    _ = V.map a ≫ V.map (F.map delta) ≫ V.map trace ≫ e.hom := by
      rw [htrace]
    _ = e.hom ≫ 𝟙 T' := by
      simpa only [Functor.map_comp, Functor.map_id, Category.assoc,
        Category.id_comp, Category.comp_id] using
          congrArg (fun z ↦ V.map z ≫ e.hom) h

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.EssentialImage
public import Mathlib.CategoryTheory.NatIso

/-! Descent of natural comparisons along a full essentially surjective functor. -/

@[expose] public noncomputable section
set_option autoImplicit false

namespace CategoryTheory.RingedSiteGlobalRHom

/-- A natural isomorphism descends along a full essentially surjective functor.

Source: the representative-to-derived-object descent in Stacks Project, Tag 08JA.
(blueprint: lem-sfb-global-rhom-full-essentially-surjective-descent).

Proof: choose an object preimage and its comparison isomorphism for each target
object. Conjugate the given comparison by those isomorphisms. Lift the conjugate
of an arbitrary target morphism using fullness; naturality of the original
comparison gives naturality after conjugation. -/
def descendIso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (P : C ⥤ D) [P.Full] [P.EssSurj] {F G : D ⥤ E}
    (e : P ⋙ F ≅ P ⋙ G) : F ≅ G := by
  refine NatIso.ofComponents (fun X ↦
    F.mapIso (P.objObjPreimageIso X).symm ≪≫ e.app (P.objPreimage X) ≪≫
      G.mapIso (P.objObjPreimageIso X)) ?_
  intro X Y f
  have h := e.hom.naturality
    (P.preimage ((P.objObjPreimageIso X).hom ≫ f ≫ (P.objObjPreimageIso Y).inv))
  dsimp only [Functor.comp_map] at h
  rw [P.map_preimage] at h
  simp only [Functor.map_comp, Category.assoc] at h
  dsimp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
  apply (cancel_epi (F.map (P.objObjPreimageIso X).hom)).mp
  apply (cancel_mono (G.map (P.objObjPreimageIso Y).inv)).mp
  simpa [Category.assoc] using h

end CategoryTheory.RingedSiteGlobalRHom

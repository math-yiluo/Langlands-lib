/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal

/-!
# Postcomposition of sheaves with a lax monoidal functor

For a lax monoidal functor `G : A ⥤ B` preserving sheaves, the postcomposition
`sheafCompose J G : Sheaf J A ⥤ Sheaf J B` is lax monoidal for the sheafified tensor products:
it is isomorphic to the composite of the lax monoidal inclusion of sheaves into presheaves, of
postcomposition with `G` on presheaves and of sheafification.

## Main definitions

- `CategoryTheory.sheafComposeLaxMonoidal`: the lax monoidal structure.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G]

attribute [local instance] Sheaf.monoidalCategory

/-- The postcomposition `sheafCompose J G` is the sheafification of the postcomposition of the
underlying presheaves. -/
noncomputable def sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso :
    sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj G ⋙ presheafToSheaf J B ≅
      sheafCompose J G :=
  Functor.isoWhiskerLeft (sheafCompose J G) (asIso (sheafificationAdjunction J B).counit) ≪≫
    (sheafCompose J G).rightUnitor

variable [G.LaxMonoidal]

/-- The postcomposition of sheaves with a lax monoidal functor is lax monoidal. -/
noncomputable instance sheafComposeLaxMonoidal : (sheafCompose J G).LaxMonoidal :=
  Functor.LaxMonoidal.transport (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)

/-- The underlying presheaf of `sheafCompose J G` is the postcomposition of the underlying
presheaf, as a monoidal isomorphism: at `P` it is the unit of sheafification, invertible on the
sheaf `G ∘ P`, followed by the transport isomorphism. -/
noncomputable def sheafToPresheafCompWhiskeringRightIsoSheafCompose :
    sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj G ≅
      sheafCompose J G ⋙ sheafToPresheaf J B :=
  have : IsIso (Functor.whiskerLeft (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj G)
      (sheafificationAdjunction J B).unit) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun P ↦ isIso_toSheafify J ((sheafCompose J G).obj P).property
  (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj G).rightUnitor.symm ≪≫
    asIso (Functor.whiskerLeft _ (sheafificationAdjunction J B).unit) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _) _ ≪≫
    Functor.isoWhiskerRight (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G) _

instance : NatTrans.IsMonoidal (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom := by
  have := Functor.LaxMonoidal.natTransIsMonoidal_of_transport
    (sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso J G)
  dsimp only [sheafToPresheafCompWhiskeringRightIsoSheafCompose, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, Functor.isoWhiskerRight_hom]
  infer_instance

section WhiskerRight

variable (C) {D E : Type*} [Category D] [Category E] [MonoidalCategory D] [MonoidalCategory E]
  {F : D ⥤ E} {G : E ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal] [G.LaxMonoidal] [adj.IsMonoidal]

/-- Postcomposing with a monoidal adjunction gives a monoidal adjunction of functor
categories. -/
instance Adjunction.isMonoidal_whiskerRight : (adj.whiskerRight C).IsMonoidal where
  leftAdjoint_ε := by
    ext X
    simp [Adjunction.IsMonoidal.leftAdjoint_ε (adj := adj)]
  leftAdjoint_μ P Q := by
    ext X
    simp [Adjunction.IsMonoidal.leftAdjoint_μ (adj := adj)]

end WhiskerRight

section ComposeAndSheafify

open Functor.OplaxMonoidal Functor.LaxMonoidal

variable {B' : Type*} [Category B'] [MonoidalCategory B'] [BraidedCategory B']
  [(J.W (A := B')).IsMonoidal] [HasWeakSheafify J B']
  {L : B' ⥤ A} {R : A ⥤ B'} (adj : L ⊣ R) [J.HasSheafCompose R]
  [L.OplaxMonoidal] [R.LaxMonoidal] [adj.IsMonoidal]

/-- The sheafified postcomposition with a left adjoint `F` of a lax monoidal functor is oplax
monoidal, being left adjoint to the lax monoidal `sheafCompose J G`. -/
noncomputable abbrev composeAndSheafifyOplaxMonoidal :
    (Sheaf.composeAndSheafify J L).OplaxMonoidal :=
  (Sheaf.adjunction J adj).leftAdjointOplaxMonoidal

omit [BraidedCategory A] [BraidedCategory B'] [L.OplaxMonoidal] [adj.IsMonoidal] in
lemma isMonoidal_sheafAdjunction :
    letI := composeAndSheafifyOplaxMonoidal J adj
    (Sheaf.adjunction J adj).IsMonoidal := by
  let := (Sheaf.adjunction J adj).leftAdjointOplaxMonoidal
  infer_instance

omit [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B] [BraidedCategory A] [BraidedCategory B'] in
/-- If `L` is strong monoidal, the comparison `δ : L_*(S ⊗ T) ⟶ L_* S ⊗ L_* T` of the sheafified
postcomposition `L_*` is an isomorphism. On sheafifications of presheaves this follows from the
conjugate triangle `CategoryTheory.conjugateEquiv_symm_app_tensor_comp_δ`, sheafification after
postcomposition being strong monoidal; in general from the naturality of `δ` along the counit
isomorphisms of sheafification. -/
lemma isIso_δ_composeAndSheafify {L : B' ⥤ A} [L.Monoidal] (adj : L ⊣ R) [adj.IsMonoidal]
    (S T : Sheaf J B') :
    letI := composeAndSheafifyOplaxMonoidal J adj
    IsIso (δ (Sheaf.composeAndSheafify J L) S T) := by
  let := composeAndSheafifyOplaxMonoidal J adj
  have := isMonoidal_sheafAdjunction J adj
  have : IsIso (δ ((Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J A) S.obj T.obj) := by
    rw [Functor.OplaxMonoidal.comp_δ]
    infer_instance
  have := isIso_δ_of_conjugateIso
    ((sheafificationAdjunction J B').comp (Sheaf.adjunction J adj))
    ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J A))
    (sheafToPresheafCompWhiskeringRightIsoSheafCompose J R) S.obj T.obj
  rw [Functor.OplaxMonoidal.comp_δ] at this
  have : IsIso (δ (Sheaf.composeAndSheafify J L) ((presheafToSheaf J B').obj S.obj)
      ((presheafToSheaf J B').obj T.obj)) :=
    IsIso.of_isIso_comp_left
      ((Sheaf.composeAndSheafify J L).map (δ (presheafToSheaf J B') S.obj T.obj)) _
  let εS : (presheafToSheaf J B').obj S.obj ⟶ S := (sheafificationAdjunction J B').counit.app S
  let εT : (presheafToSheaf J B').obj T.obj ⟶ T := (sheafificationAdjunction J B').counit.app T
  have : IsIso ((Sheaf.composeAndSheafify J L).map (εS ⊗ₘ εT) ≫
      δ (Sheaf.composeAndSheafify J L) S T) := by
    rw [← Functor.OplaxMonoidal.δ_natural]
    infer_instance
  exact IsIso.of_isIso_comp_left ((Sheaf.composeAndSheafify J L).map (εS ⊗ₘ εT)) _
omit [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B] [BraidedCategory A] [BraidedCategory B'] in
/-- If `L` is strong monoidal, the comparison `η : L_* 𝟙 ⟶ 𝟙` of the sheafified postcomposition
is an isomorphism, by the conjugate triangle
`CategoryTheory.conjugateEquiv_symm_app_unit_comp_η`. -/
lemma isIso_η_composeAndSheafify {L : B' ⥤ A} [L.Monoidal] (adj : L ⊣ R) [adj.IsMonoidal] :
    letI := composeAndSheafifyOplaxMonoidal J adj
    IsIso (η (Sheaf.composeAndSheafify J L)) := by
  let := composeAndSheafifyOplaxMonoidal J adj
  have := isMonoidal_sheafAdjunction J adj
  have : IsIso (η ((Functor.whiskeringRight _ _ _).obj L ⋙ presheafToSheaf J A)) := by
    rw [Functor.OplaxMonoidal.comp_η]
    infer_instance
  have := isIso_η_of_conjugateIso
    ((sheafificationAdjunction J B').comp (Sheaf.adjunction J adj))
    ((adj.whiskerRight Cᵒᵖ).comp (sheafificationAdjunction J A))
    (sheafToPresheafCompWhiskeringRightIsoSheafCompose J R)
  rw [Functor.OplaxMonoidal.comp_η] at this
  exact IsIso.of_isIso_comp_left
    ((Sheaf.composeAndSheafify J L).map (η (presheafToSheaf J B'))) _

/-- If `L` is strong monoidal, the sheafified postcomposition with `L` is strong monoidal, its
oplax structure being `CategoryTheory.composeAndSheafifyOplaxMonoidal`. -/
noncomputable abbrev composeAndSheafifyMonoidal {L : B' ⥤ A} [L.Monoidal] (adj : L ⊣ R)
    [adj.IsMonoidal] : (Sheaf.composeAndSheafify J L).Monoidal :=
  let := composeAndSheafifyOplaxMonoidal J adj
  have := isIso_η_composeAndSheafify J adj
  have := isIso_δ_composeAndSheafify J adj
  .ofOplaxMonoidal _

end ComposeAndSheafify

end CategoryTheory

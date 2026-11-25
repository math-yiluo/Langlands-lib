/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.PoincareDuality.ProjectionCoherence

/-!

# The exceptional projection morphism and refinements, abstractly

For a compactification `X ⟶[i] Z ⟶[p] Y` of `f`, the exceptional projection morphism is
```
P (I K) ⊗ B ⟶ P (I K ⊗ Ps B) ⟶ P (I (K ⊗ Is Ps B)) ⟶ P (I (K ⊗ Fs B)),
```
the projection morphism of `Ps ⊣ P` (the proper `p`), the inverse of the projection comparison of
`I ⊣ Is` (the open immersion `i`) and the identification `Fs ≅ Ps ⋙ Is`. A refinement
`h : Z ⟶ Z₁` of a second compactification `X ⟶[i₁] Z₁ ⟶[p₁] Y` (with `i ≫ h = i₁` cartesian and
`h ≫ p₁ = p`) gives the comparison `ρ : P₁ ∘ I₁ ⟶ P ∘ I`, the composite of the pushforward
comparison `I₁ ⟶ H ∘ I` (the unit of `Hs ⊣ H` followed by the inverse of the restriction
comparison) and of `H ⋙ P₁ ≅ P`. This file shows that `ρ` intertwines the exceptional projection
morphisms (`CategoryTheory.Adjunction.whiskerRight_refinement_comp_exceptionalProjection`), for
abstract adjunctions: this is the independence of the projection formula from the
compactification (blueprint `prop-sf-pf-coherence`; SGA 4, Exposé XVII, 5.2.2).

For the trivial compactification `(j, 𝟙)` of an open immersion, with `Gs ≅ 𝟭` and the conjugate
`G ≅ 𝟭`, the exceptional projection morphism followed by the projection comparison of `I ⊣ Is` is
the identification
(`CategoryTheory.Adjunction.trivial_exceptionalProjection_comp_projectionComparison`).

-/

@[expose] public section

open CategoryTheory MonoidalCategory

namespace CategoryTheory.Adjunction

variable {𝒳 𝒵 𝒵₁ 𝒴 : Type*} [Category 𝒳] [Category 𝒵] [Category 𝒵₁] [Category 𝒴]
  [MonoidalCategory 𝒳] [MonoidalCategory 𝒵] [MonoidalCategory 𝒵₁] [MonoidalCategory 𝒴]
  {I : 𝒳 ⥤ 𝒵} {Is : 𝒵 ⥤ 𝒳} [Is.Monoidal] (bi : I ⊣ Is)
  {I₁ : 𝒳 ⥤ 𝒵₁} {I₁s : 𝒵₁ ⥤ 𝒳} [I₁s.Monoidal] (bi₁ : I₁ ⊣ I₁s)
  {Hs : 𝒵₁ ⥤ 𝒵} {H : 𝒵 ⥤ 𝒵₁} [Hs.Monoidal] (ah : Hs ⊣ H)
  (e : I₁s ≅ Hs ⋙ Is)

omit [MonoidalCategory 𝒳] [MonoidalCategory 𝒵] [MonoidalCategory 𝒵₁] [Is.Monoidal] [I₁s.Monoidal]
  [Hs.Monoidal] in
/-- The restriction comparison `I ⟶ Hs ∘ I₁` is natural. -/
@[reassoc]
lemma restrictionComparison_naturality {M M' : 𝒳} (φ : M ⟶ M') :
    I.map φ ≫ restrictionComparison bi bi₁ e M' =
      restrictionComparison bi bi₁ e M ≫ Hs.map (I₁.map φ) := by
  have h₁ := bi₁.unit_naturality φ
  have h₂ := e.hom.naturality (I₁.map φ)
  simp only [Functor.comp_map] at h₂
  have h₃ := bi.counit_naturality (Hs.map (I₁.map φ))
  rw [restrictionComparison, restrictionComparison, Category.assoc, ← h₃, ← I.map_comp_assoc,
    ← I.map_comp_assoc]
  congr 2
  simp only [Category.assoc]
  rw [← reassoc_of% h₁, h₂]

variable [∀ M, IsIso (restrictionComparison bi bi₁ e M)]

/-- The pushforward comparison `I₁ ⟶ H ∘ I` of a refinement: the unit of `Hs ⊣ H` followed by
`H` of the inverse of the restriction comparison. -/
noncomputable def refinementPushforward (M : 𝒳) : I₁.obj M ⟶ H.obj (I.obj M) :=
  ah.unit.app (I₁.obj M) ≫ H.map (inv (restrictionComparison bi bi₁ e M))

omit [MonoidalCategory 𝒳] [MonoidalCategory 𝒵] [MonoidalCategory 𝒵₁] [Is.Monoidal] [I₁s.Monoidal]
  [Hs.Monoidal] in
/-- The pushforward comparison of a refinement is natural. -/
@[reassoc]
lemma refinementPushforward_naturality {M M' : 𝒳} (φ : M ⟶ M') :
    I₁.map φ ≫ refinementPushforward bi bi₁ ah e M' =
      refinementPushforward bi bi₁ ah e M ≫ H.map (I.map φ) := by
  have h := restrictionComparison_naturality bi bi₁ e φ
  have h' : inv (restrictionComparison bi bi₁ e M) ≫ I.map φ =
      Hs.map (I₁.map φ) ≫ inv (restrictionComparison bi bi₁ e M') := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [refinementPushforward, Category.assoc, ← H.map_comp, h']
  rw [H.map_comp, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (ah.unit_naturality _).symm

variable {Ps : 𝒴 ⥤ 𝒵} {P : 𝒵 ⥤ 𝒴} [Ps.Monoidal] (ap : Ps ⊣ P)
  {P₁s : 𝒴 ⥤ 𝒵₁} {P₁ : 𝒵₁ ⥤ 𝒴} [P₁s.Monoidal] (ap₁ : P₁s ⊣ P₁)
  {Fs : 𝒴 ⥤ 𝒳}

open Functor.LaxMonoidal in
/-- **The refinement comparison intertwines the exceptional projection morphisms**: for a
refinement `h` of compactifications `(i, p)` and `(i₁, p₁)` of `f`, with `κ : H ⋙ P₁ ≅ P`
(`h ≫ p₁ = p`) compatible with the projection morphisms (`hpm`), `τ : Ps ≅ P₁s ⋙ Hs` and the
identifications `εP : Fs ≅ Ps ⋙ Is`, `εP₁ : Fs ≅ P₁s ⋙ I₁s` compatible with `e` (`hε`), the
comparison `ρ = P₁ (I₁ ⟶ H I) ≫ κ` carries the exceptional projection morphism of `(i₁, p₁)` to
that of `(i, p)`:
```
P₁ (I₁ K) ⊗ B --ρ_K ▷ B--> P (I K) ⊗ B
     |                          |
 PF^{(i₁,p₁)}                 PF^{(i,p)}
     v                          v
P₁ (I₁ (K ⊗ Fs B)) --ρ--> P (I (K ⊗ Fs B))
```
-/
lemma whiskerRight_refinement_comp_exceptionalProjection
    (he : ∀ X Y, μ I₁s X Y ≫ e.hom.app (X ⊗ Y) =
      (e.hom.app X ⊗ₘ e.hom.app Y) ≫ μ (Hs ⋙ Is) X Y)
    [∀ K N, IsIso (bi.projectionComparison K N)] [∀ K N, IsIso (bi₁.projectionComparison K N)]
    (κ : H ⋙ P₁ ≅ P) (τ : Ps ≅ P₁s ⋙ Hs)
    (hpm : ∀ A B, ap.projectionMorphism A B = κ.inv.app A ▷ B ≫
      ap₁.projectionMorphism (H.obj A) B ≫ P₁.map (ah.projectionMorphism A (P₁s.obj B)) ≫
        κ.hom.app _ ≫ P.map (A ◁ τ.inv.app B))
    (εP : Fs ≅ Ps ⋙ Is) (εP₁ : Fs ≅ P₁s ⋙ I₁s)
    (hε : ∀ B, εP₁.hom.app B ≫ e.hom.app (P₁s.obj B) = εP.hom.app B ≫ Is.map (τ.hom.app B))
    (K : 𝒳) (B : 𝒴) :
    (P₁.map (refinementPushforward bi bi₁ ah e K) ≫ κ.hom.app (I.obj K)) ▷ B ≫
        ap.projectionMorphism (I.obj K) B ≫
        P.map (inv (bi.projectionComparison K (Ps.obj B)) ≫ I.map (K ◁ εP.inv.app B)) =
      ap₁.projectionMorphism (I₁.obj K) B ≫
        P₁.map (inv (bi₁.projectionComparison K (P₁s.obj B)) ≫ I₁.map (K ◁ εP₁.inv.app B)) ≫
        P₁.map (refinementPushforward bi bi₁ ah e (K ⊗ Fs.obj B)) ≫
        κ.hom.app (I.obj (K ⊗ Fs.obj B)) := by
  set N := P₁s.obj B
  -- the projection formula of the refinement `h`
  have hr := projectionComparison_comp_refinement bi bi₁ e ah he K N
  have hinner : refinementPushforward bi bi₁ ah e K ▷ N ≫
      ah.projectionMorphism (I.obj K) N =
      inv (bi₁.projectionComparison K N) ≫
        refinementPushforward bi bi₁ ah e (K ⊗ I₁s.obj N) ≫
        H.map (I.map (K ◁ e.hom.app N) ≫ bi.projectionComparison K (Hs.obj N)) := by
    rw [IsIso.eq_inv_comp]
    exact hr
  -- the identifications of the inverse images
  have hε' : e.hom.app N ≫ Is.map (τ.inv.app B) ≫ εP.inv.app B = εP₁.inv.app B := by
    rw [← cancel_epi (εP₁.hom.app B), reassoc_of% (hε B)]
    rw [← Is.map_comp_assoc, Iso.hom_inv_id_app, Is.map_id, Category.id_comp,
      Iso.hom_inv_id_app, Iso.hom_inv_id_app]
  have hpc := bi.projectionComparison_natural_right K (τ.inv.app B)
  have hpc' : bi.projectionComparison K (Hs.obj N) ≫ I.obj K ◁ τ.inv.app B ≫
      inv (bi.projectionComparison K (Ps.obj B)) =
      I.map (K ◁ Is.map (τ.inv.app B)) := by
    rw [← reassoc_of% hpc, IsIso.hom_inv_id, Category.comp_id]
  have hfinal : refinementPushforward bi bi₁ ah e K ▷ N ≫
      ah.projectionMorphism (I.obj K) N ≫
      H.map (I.obj K ◁ τ.inv.app B ≫ inv (bi.projectionComparison K (Ps.obj B)) ≫
        I.map (K ◁ εP.inv.app B)) =
      inv (bi₁.projectionComparison K N) ≫ I₁.map (K ◁ εP₁.inv.app B) ≫
        refinementPushforward bi bi₁ ah e (K ⊗ Fs.obj B) := by
    rw [reassoc_of% hinner, refinementPushforward_naturality]
    have hmid : (I.map (K ◁ e.hom.app N) ≫ bi.projectionComparison K (Hs.obj N)) ≫
        I.obj K ◁ τ.inv.app B ≫ inv (bi.projectionComparison K (Ps.obj B)) ≫
        I.map (K ◁ εP.inv.app B) = I.map (K ◁ εP₁.inv.app B) := by
      rw [Category.assoc, reassoc_of% hpc', ← I.map_comp, ← I.map_comp, ← whiskerLeft_comp,
        ← whiskerLeft_comp, hε']
    rw [← H.map_comp, hmid]
  rw [hpm (I.obj K) B]
  simp only [comp_whiskerRight, Category.assoc]
  erw [hom_inv_whiskerRight_assoc (κ.app (I.obj K)) B]
  rw [ap₁.projectionMorphism_natural_left_assoc]
  congr 1
  rw [← P.map_comp, ← κ.hom.naturality, Functor.comp_map, ← P₁.map_comp_assoc,
    ← P₁.map_comp_assoc, Category.assoc, hfinal]
  simp only [P₁.map_comp, Category.assoc]
  rfl

section Trivial

open Functor.OplaxMonoidal

variable {C : Type*} [Category C] [MonoidalCategory C]

/-- The projection morphism of the identity adjunction is the identity. -/
lemma id_projectionMorphism (A B : C) :
    (Adjunction.id (C := C)).projectionMorphism A B = 𝟙 _ := by
  simp only [projectionMorphism, id_δ, Category.id_comp, homEquiv_unit]
  simp

variable {Gs G : C ⥤ C} [Gs.OplaxMonoidal] (ag : Gs ⊣ G) (ηs : Gs ≅ 𝟭 C)

/-- For an adjunction `Gs ⊣ G` with a monoidal identification `ηs : Gs ≅ 𝟭`, the projection
morphism followed by the conjugate identification `G ≅ 𝟭` is that identification whiskered by `B`,
followed by `A ◁ ηs⁻¹`. -/
lemma projectionMorphism_comp_conjugate_id
    (hηs : ∀ X Y, δ Gs X Y ≫ (ηs.hom.app X ⊗ₘ ηs.hom.app Y) = ηs.hom.app (X ⊗ Y)) (A B : C) :
    ag.projectionMorphism A B ≫
        (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.app (A ⊗ Gs.obj B) =
      (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.app A ▷ B ≫ A ◁ ηs.inv.app B := by
  rw [projectionMorphism_eq_of_iso ag Adjunction.id ηs (fun X Y ↦ by simpa using hηs X Y),
    id_projectionMorphism]
  have h := (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.naturality (A ◁ ηs.inv.app B)
  simp only [Functor.id_map] at h
  simp only [Category.id_comp, Category.assoc, h]
  rw [← Category.assoc ((conjugateIsoEquiv Adjunction.id ag ηs).hom.app _)]
  erw [(conjugateIsoEquiv ag Adjunction.id ηs.symm).inv_hom_id_app]
  simp


open Functor.LaxMonoidal in
/-- **The exceptional projection morphism of the trivial compactification** `(j, 𝟙)`, for
abstract adjunctions: through the identification `G ≅ 𝟭` conjugate to `ηs : Gs ≅ 𝟭`, the composite
of the projection morphism of `Gs ⊣ G`, the inverse projection comparison of `I ⊣ Is` and
`Is ηs`, followed by the projection comparison of `I ⊣ Is`, is the identification:
```
G (I K) ⊗ B --PF--> G (I (K ⊗ Is B))
     |                     |
  (G ≅ 𝟭) ▷ B           G ≅ 𝟭
     v                     v
  I K ⊗ B <------π----- I (K ⊗ Is B)
```
-/
lemma trivial_exceptionalProjection_comp_projectionComparison {D : Type*} [Category D]
    [MonoidalCategory D] {I : D ⥤ C} {Is : C ⥤ D} [Is.LaxMonoidal] (bi : I ⊣ Is)
    (hηs : ∀ X Y, δ Gs X Y ≫ (ηs.hom.app X ⊗ₘ ηs.hom.app Y) = ηs.hom.app (X ⊗ Y)) (K : D) (B : C)
    [IsIso (bi.projectionComparison K (Gs.obj B))] :
    (ag.projectionMorphism (I.obj K) B ≫
        G.map (inv (bi.projectionComparison K (Gs.obj B)) ≫ I.map (K ◁ Is.map (ηs.hom.app B)))) ≫
      (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.app (I.obj (K ⊗ Is.obj B)) ≫
        bi.projectionComparison K B =
      (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.app (I.obj K) ▷ B := by
  have hn := (conjugateIsoEquiv ag Adjunction.id ηs.symm).hom.naturality
    (inv (bi.projectionComparison K (Gs.obj B)) ≫ I.map (K ◁ Is.map (ηs.hom.app B)))
  simp only [Functor.id_map] at hn
  have hq := bi.projectionComparison_natural_right K (ηs.hom.app B)
  simp only [Functor.id_obj] at hq
  rw [Category.assoc, reassoc_of% hn, hq, IsIso.inv_hom_id_assoc,
    reassoc_of% (projectionMorphism_comp_conjugate_id ag ηs hηs (I.obj K) B),
    ← whiskerLeft_comp, Iso.inv_hom_id_app]
  erw [whiskerLeft_id, Category.comp_id]

end Trivial

end CategoryTheory.Adjunction

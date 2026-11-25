/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Restrict
import WeilConjectures.AlgebraicGeometry.DerivedTensorOpenRestrictionNatural
import Mathlib.CategoryTheory.Localization.Prod
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization

/-! # Coherent descent through open restriction

Source: Stacks Project, Tags 08EU and 08FE.
(blueprint: lem-pc-open-restriction-tensor-counit-descent).
-/

@[expose] public section

universe u w
open CategoryTheory MonoidalCategory
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings (f ⁻¹ᵁ U).toScheme.toRingedSpace))]
variable [HasDerivedCategory.{u}
  (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]


private theorem tensor_descent
    {C D CO DO : Type*} [Category* C] [Category* D] [Category* CO] [Category* DO]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory CO] [MonoidalCategory DO]
    (F : C ⥤ D) (FO : CO ⥤ DO) (rY : C ⥤ CO) (rX : D ⥤ DO)
    (W : MorphismProperty C) [rY.IsLocalization W] [W.ContainsIdentities]
    (alpha : F ⋙ rX ≅ rY ⋙ FO)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (rhoY : tensor C ⋙ rY ≅ rY.prod rY ⋙ tensor CO)
    (rhoX : tensor D ⋙ rX ≅ rX.prod rX ⋙ tensor DO) :
    ∃ s : tensor CO ⋙ FO ≅ FO.prod FO ⋙ tensor DO,
      ∀ A B : C,
        alpha.inv.app (A ⊗ B) ≫ rX.map (t.hom.app (A, B)) ≫
          rhoX.hom.app (F.obj A, F.obj B) ≫
          (alpha.hom.app A ⊗ₘ alpha.hom.app B) =
        FO.map (rhoY.hom.app (A, B)) ≫ s.hom.app (rY.obj A, rY.obj B) := by
  let L := rY.prod rY
  let FL := tensor CO ⋙ FO
  let FR := FO.prod FO ⋙ tensor DO
  let e : L ⋙ FL ≅ L ⋙ FR :=
    Functor.isoWhiskerRight rhoY.symm FO ≪≫
      Functor.isoWhiskerLeft (tensor C) alpha.symm ≪≫
      Functor.isoWhiskerRight t rX ≪≫
      Functor.isoWhiskerLeft (F.prod F) rhoX ≪≫
      Functor.isoWhiskerRight (NatIso.prod alpha alpha) (tensor DO)
  let s := Localization.liftNatIso L (W.prod W) (L ⋙ FL) (L ⋙ FR) FL FR e
  refine ⟨s, ?_⟩
  intro A B
  have h := Localization.liftNatTrans_app L (W.prod W)
    (L ⋙ FL) (L ⋙ FR) FL FR e.hom (A, B)
  change s.hom.app (rY.obj A, rY.obj B) = _ at h
  dsimp [Localization.Lifting.iso, e] at h
  rw [h]
  simp only [Category.assoc, ← FO.map_comp_assoc, Iso.hom_inv_id_app, Category.id_comp]
  simp

private theorem counit_restriction
    {C D CO DO : Type*} [Category* C] [Category* D] [Category* CO] [Category* DO]
    {F : C ⥤ D} {G : D ⥤ C} {FO : CO ⥤ DO} {GO : DO ⥤ CO}
    (p : F ⊣ G) (q : FO ⊣ GO) (rY : C ⥤ CO) (rX : D ⥤ DO)
    (alpha : F ⋙ rX ≅ rY ⋙ FO) (beta : G ⋙ rY ≅ rX ⋙ GO)
    (h : ∀ (A : C) (B : D) (v : F.obj A ⟶ B),
      rY.map (p.homEquiv A B v) ≫ beta.hom.app B =
        q.homEquiv (rY.obj A) (rX.obj B) (alpha.inv.app A ≫ rX.map v))
    (B : D) :
    alpha.inv.app (G.obj B) ≫ rX.map (p.counit.app B) =
      FO.map (beta.hom.app B) ≫ q.counit.app (rX.obj B) := by
  have hB := h (G.obj B) B (p.counit.app B)
  have he : p.homEquiv (G.obj B) B (p.counit.app B) = 𝟙 (G.obj B) := by
    rw [← p.homEquiv_symm_id, Equiv.apply_symm_apply]
  rw [he, rY.map_id, Category.id_comp] at hB
  have hh := congrArg (q.homEquiv (rY.obj (G.obj B)) (rX.obj B)).symm hB
  simp only [Equiv.symm_apply_apply] at hh
  rw [q.homEquiv_counit] at hh
  exact hh.symm

private theorem tensor_counit_compatibility
    {C D CO DO : Type*} [Category* C] [Category* D] [Category* CO] [Category* DO]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory CO] [MonoidalCategory DO]
    {F : C ⥤ D} {G : D ⥤ C} {FO : CO ⥤ DO} {GO : DO ⥤ CO}
    (p : F ⊣ G) (q : FO ⊣ GO) (rY : C ⥤ CO) (rX : D ⥤ DO)
    (alpha : F ⋙ rX ≅ rY ⋙ FO) (beta : G ⋙ rY ≅ rX ⋙ GO)
    (t : tensor C ⋙ F ≅ F.prod F ⋙ tensor D)
    (s : tensor CO ⋙ FO ≅ FO.prod FO ⋙ tensor DO)
    (rhoY : tensor C ⋙ rY ≅ rY.prod rY ⋙ tensor CO)
    (rhoX : tensor D ⋙ rX ≅ rX.prod rX ⋙ tensor DO)
    (ht : ∀ A B : C,
      alpha.inv.app (A ⊗ B) ≫ rX.map (t.hom.app (A, B)) ≫
        rhoX.hom.app (F.obj A, F.obj B) ≫
        (alpha.hom.app A ⊗ₘ alpha.hom.app B) =
      FO.map (rhoY.hom.app (A, B)) ≫ s.hom.app (rY.obj A, rY.obj B))
    (hc : ∀ B : D, alpha.inv.app (G.obj B) ≫ rX.map (p.counit.app B) =
      FO.map (beta.hom.app B) ≫ q.counit.app (rX.obj B))
    (A : C) (B : D) :
    alpha.inv.app (A ⊗ G.obj B) ≫
      rX.map (t.hom.app (A, G.obj B) ≫ (𝟙 (F.obj A) ⊗ₘ p.counit.app B)) ≫
      (rhoX.hom.app (F.obj A, B) ≫ (alpha.hom.app A ⊗ₘ 𝟙 (rX.obj B))) =
    FO.map (rhoY.hom.app (A, G.obj B) ≫ (𝟙 (rY.obj A) ⊗ₘ beta.hom.app B)) ≫
      (s.hom.app (rY.obj A, GO.obj (rX.obj B)) ≫
        (𝟙 (FO.obj (rY.obj A)) ⊗ₘ q.counit.app (rX.obj B))) := by
  have hn := rhoX.hom.naturality
    ((𝟙 (F.obj A), p.counit.app B) :
      (F.obj A, F.obj (G.obj B)) ⟶ (F.obj A, B))
  change rX.map (𝟙 (F.obj A) ⊗ₘ p.counit.app B) ≫
      rhoX.hom.app (F.obj A, B) =
    rhoX.hom.app (F.obj A, F.obj (G.obj B)) ≫
      (rX.map (𝟙 (F.obj A)) ⊗ₘ rX.map (p.counit.app B)) at hn
  rw [rX.map_id] at hn
  have hc' : rX.map (p.counit.app B) = alpha.hom.app (G.obj B) ≫
      FO.map (beta.hom.app B) ≫ q.counit.app (rX.obj B) := by
    rw [← hc B, Iso.hom_inv_id_app_assoc]
  have hs := s.hom.naturality
    ((𝟙 (rY.obj A), beta.hom.app B) :
      (rY.obj A, rY.obj (G.obj B)) ⟶ (rY.obj A, GO.obj (rX.obj B)))
  change FO.map (𝟙 (rY.obj A) ⊗ₘ beta.hom.app B) ≫
      s.hom.app (rY.obj A, GO.obj (rX.obj B)) =
    s.hom.app (rY.obj A, rY.obj (G.obj B)) ≫
      (FO.map (𝟙 (rY.obj A)) ⊗ₘ FO.map (beta.hom.app B)) at hs
  rw [FO.map_id] at hs
  have he :
      (𝟙 (rX.obj (F.obj A)) ⊗ₘ
        (alpha.hom.app (G.obj B) ≫ FO.map (beta.hom.app B) ≫
          q.counit.app (rX.obj B))) ≫ (alpha.hom.app A ⊗ₘ 𝟙 (rX.obj B)) =
      (alpha.hom.app A ⊗ₘ alpha.hom.app (G.obj B)) ≫
        (𝟙 (FO.obj (rY.obj A)) ⊗ₘ FO.map (beta.hom.app B)) ≫
        (𝟙 (FO.obj (rY.obj A)) ⊗ₘ q.counit.app (rX.obj B)) := by
    simp only [tensorHom_comp_tensorHom]
    congr 1 <;> simp
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc (rX.map (𝟙 (F.obj A) ⊗ₘ p.counit.app B))
    (rhoX.hom.app (F.obj A, B)) (alpha.hom.app A ⊗ₘ 𝟙 (rX.obj B)), hn]
  simp only [Category.assoc]
  rw [hc', he]
  have ht' := congrArg (fun k ↦ k ≫
      ((𝟙 (FO.obj (rY.obj A)) ⊗ₘ FO.map (beta.hom.app B)) ≫
        (𝟙 (FO.obj (rY.obj A)) ⊗ₘ q.counit.app (rX.obj B)))) (ht A (G.obj B))
  simp only [Category.assoc] at ht'
  rw [ht']
  rw [← Category.assoc (s.hom.app (rY.obj A, rY.obj (G.obj B)))
    (𝟙 (FO.obj (rY.obj A)) ⊗ₘ FO.map (beta.hom.app B))
    (𝟙 (FO.obj (rY.obj A)) ⊗ₘ q.counit.app (rX.obj B)), ← hs]
  simp only [Category.assoc]

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Tensor comparison and counit descend together before taking an adjunction transpose.
Source: Stacks Project, Tag 08EU, first sentence of proof; Tag 08FE.
Proof: construct rhoX and rhoY naturally on K-flat total tensor models, using exact
restriction and its compatibility with tensor and totalization; descend these maps
and their inverses to the specified small derived localizations. Open restriction is
a localization, as is its product with itself. Conjugate the restriction of t by rhoX,
rhoY and alpha to obtain an isomorphism between the restrictions of the two local
bifunctors. Full faithfulness of precomposition with this product localization lifts
it uniquely to s. Its factorization identity gives compatibility on every pair of
global inputs. The assumed Hom-equivalence compatibility
identifies the restricted counit of p with that of q: take the source object to be
the direct image of B and the input morphism to be p's counit, whose p-transpose
is the identity, and use injectivity of q's Hom equivalence.
Combine this counit identity with the tensor naturality square. Their composite is
the displayed identity between morphisms BEFORE transposing along q. Thus this is
the tensor/counit step, not an assertion comparing projection mates as arrows.
No quasi-coherence or invertibility of a projection mate is used. All localization
counits and K-flat restriction comparisons apply unchanged when the open is empty.
(blueprint: lem-pc-open-restriction-tensor-counit-descent). -/
theorem exists_openRestriction_tensor_counit_descent
    (p : derivedPullback f ⊣ schemeDerivedDirectImage f)
    (t : tensor (schemeDerivedCategory Y) ⋙ derivedPullback f ≅
      (derivedPullback f).prod (derivedPullback f) ⋙ tensor (schemeDerivedCategory X)) :
    let rX := (schemeOpenRestriction X (f ⁻¹ᵁ U)).mapDerivedCategory
    let rY := (schemeOpenRestriction Y U).mapDerivedCategory
    ∀ (q : derivedPullback (f ∣_ U) ⊣ schemeDerivedDirectImage (f ∣_ U))
      (alpha : derivedPullback f ⋙ rX ≅ rY ⋙ derivedPullback (f ∣_ U))
      (beta : schemeDerivedDirectImage f ⋙ rY ≅ rX ⋙ schemeDerivedDirectImage (f ∣_ U)),
    (∀ (A : schemeDerivedCategory Y) (B : schemeDerivedCategory X)
      (v : (derivedPullback f).obj A ⟶ B),
      rY.map (p.homEquiv A B v) ≫ beta.hom.app B =
        q.homEquiv (rY.obj A) (rX.obj B) (alpha.inv.app A ≫ rX.map v)) →
    ∃ (s : tensor (schemeDerivedCategory U.toScheme) ⋙ derivedPullback (f ∣_ U) ≅
        (derivedPullback (f ∣_ U)).prod (derivedPullback (f ∣_ U)) ⋙
          tensor (schemeDerivedCategory (f ⁻¹ᵁ U).toScheme))
      (rhoY : tensor (schemeDerivedCategory Y) ⋙ rY ≅
        rY.prod rY ⋙ tensor (schemeDerivedCategory U.toScheme))
      (rhoX : tensor (schemeDerivedCategory X) ⋙ rX ≅
        rX.prod rX ⋙ tensor (schemeDerivedCategory (f ⁻¹ᵁ U).toScheme)),
      ∀ (A : schemeDerivedCategory Y) (B : schemeDerivedCategory X),
        alpha.inv.app (A ⊗ (schemeDerivedDirectImage f).obj B) ≫
          rX.map (t.hom.app (A, (schemeDerivedDirectImage f).obj B) ≫
            (𝟙 ((derivedPullback f).obj A) ⊗ₘ p.counit.app B)) ≫
          (rhoX.hom.app ((derivedPullback f).obj A, B) ≫
            (alpha.hom.app A ⊗ₘ 𝟙 (rX.obj B))) =
        (derivedPullback (f ∣_ U)).map (rhoY.hom.app (A, (schemeDerivedDirectImage f).obj B) ≫
          (𝟙 (rY.obj A) ⊗ₘ beta.hom.app B)) ≫
          (s.hom.app (rY.obj A, (schemeDerivedDirectImage (f ∣_ U)).obj (rX.obj B)) ≫
            (𝟙 ((derivedPullback (f ∣_ U)).obj (rY.obj A)) ⊗ₘ
              q.counit.app (rX.obj B))) := by
  intro rX rY q alpha beta h
  let WY : MorphismProperty (schemeDerivedCategory.{u, w} Y) := (MorphismProperty.isomorphisms
    (schemeDerivedCategory.{u, u} U.toScheme)).inverseImage rY
  have hloc : rY.IsLocalization WY := schemeDerivedOpenRestriction_isLocalization.{u, w, u} Y U
  -- Keep the comparison types intact when selecting their witnesses.
  let rhoY := Classical.choice (derivedTensor_openRestriction_natIso.{u, w, u} Y U)
  let rhoX := Classical.choice (derivedTensor_openRestriction_natIso.{u, w, u} X (f ⁻¹ᵁ U))
  refine (@tensor_descent
    (schemeDerivedCategory.{u, w} Y) (schemeDerivedCategory.{u, w} X)
    (schemeDerivedCategory.{u, u} U.toScheme) (schemeDerivedCategory.{u, u} (f ⁻¹ᵁ U).toScheme)
    _ _ _ _
    (schemeDerivedTensorMonoidal.{u, w} Y) (schemeDerivedTensorMonoidal.{u, w} X)
    (schemeDerivedTensorMonoidal.{u, u} U.toScheme)
    (schemeDerivedTensorMonoidal.{u, u} (f ⁻¹ᵁ U).toScheme)
    (derivedPullback.{u, w} f) (derivedPullback.{u, u} (f ∣_ U))
    rY rX WY hloc (MorphismProperty.ContainsIdentities.inverseImage rY)
    alpha t rhoY rhoX).elim fun s ht ↦ ?_
  refine ⟨s, rhoY, rhoX, ?_⟩
  intro A B
  exact @tensor_counit_compatibility
    (schemeDerivedCategory.{u, w} Y) (schemeDerivedCategory.{u, w} X)
    (schemeDerivedCategory.{u, u} U.toScheme) (schemeDerivedCategory.{u, u} (f ⁻¹ᵁ U).toScheme)
    _ _ _ _
    (schemeDerivedTensorMonoidal.{u, w} Y) (schemeDerivedTensorMonoidal.{u, w} X)
    (schemeDerivedTensorMonoidal.{u, u} U.toScheme)
    (schemeDerivedTensorMonoidal.{u, u} (f ⁻¹ᵁ U).toScheme)
    (derivedPullback.{u, w} f) (schemeDerivedDirectImage.{u, w, w} f)
    (derivedPullback.{u, u} (f ∣_ U)) (schemeDerivedDirectImage.{u, u, u} (f ∣_ U))
    p q rY rX alpha beta t s rhoY rhoX ht
    (counit_restriction p q rY rX alpha beta h) A B

end AlgebraicGeometry

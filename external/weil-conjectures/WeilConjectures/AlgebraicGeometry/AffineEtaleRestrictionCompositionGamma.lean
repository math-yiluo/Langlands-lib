/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FullAffineEtaleSite
public import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Affine étale inverse-image composition coherence -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

/-- Source: Stacks Project, Sites 03CB and 03CC.
(blueprint: lem-weil-pbc-affine-etale-restriction-composition-gamma)
(blueprint: lem-weil-pbc-affine-etale-restriction-composition-gamma)
Proof: conjugate pullbackComp by t, then cancel the fully faithful affine inclusion.
The map-preimage identity and cancellation of t give the displayed equation. -/
theorem affineEtale_restriction_composition_gamma
    (U : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        X.FullAffineEtale ⥤ Y.FullAffineEtale)
      (t : ∀ {X Y : Scheme.{u}} (h : Y ⟶ X) [IsAffineHom h],
        U h ⋙ fullAffineEtaleInclusion Y ≅
          fullAffineEtaleInclusion X ⋙ (MorphismProperty.Over.pullback @Etale ⊤ h)) :
    ∃ (gamma : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
        [IsAffineHom f] [IsAffineHom g], U f ⋙ U g ≅ U (g ≫ f)),
    (∀ (X Y Z : Scheme.{u}) (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g] (V : X.FullAffineEtale),
      (fullAffineEtaleInclusion Z).map ((gamma f g).hom.app V) ≫ (t (g ≫ f)).hom.app V =
        (t g).hom.app ((U f).obj V) ≫
          (MorphismProperty.Over.pullback @Etale ⊤ g).map ((t f).hom.app V) ≫
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).inv.app V.obj) := by
  have (S : Scheme.{u}) : (fullAffineEtaleInclusion S).Full := by
    dsimp [fullAffineEtaleInclusion]
    infer_instance
  have (S : Scheme.{u}) : (fullAffineEtaleInclusion S).Faithful := by
    dsimp [fullAffineEtaleInclusion]
    infer_instance
  let gamma : ∀ {X Y Z : Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ Y)
      [IsAffineHom f] [IsAffineHom g], U f ⋙ U g ≅ U (g ≫ f) :=
    fun {X Y Z} f g _ _ ↦ Functor.fullyFaithfulCancelRight
      (fullAffineEtaleInclusion Z)
      ((Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft (U f) (t g) ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (t f) (MorphismProperty.Over.pullback @Etale ⊤ g) ≪≫
        Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (fullAffineEtaleInclusion X)
          (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) g f).symm ≪≫
        (t (g ≫ f)).symm)
  refine ⟨gamma, ?_⟩
  intro X Y Z f g _ _ V
  dsimp [gamma]
  simp [Category.assoc]
  rfl

end AlgebraicGeometry.Scheme

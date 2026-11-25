/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMate
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars

/-!
# Composition of normalized scalar/pullback comparisons

The normalized comparison is already identified with the inverse scalar-adjunction mate
in `EtaleProEtaleScalarMate`. Transport that identification to exact derived inverse image.
The existing derived restriction square respects geometric composition. Its scalar-adjunction
transposes therefore compose, and inversion gives the stated forward comparison.

## References

* Stacks Project, with the ordinary composition of Tag 03D8 and the K-flat normalization of Tag 0G7E
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory
open scoped CategoryTheory.Functor
universe u

private theorem transposePasting
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (S₂ : A₂ ⥤ B₂)
    (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁) (U₂ : B₂ ⥤ A₂)
    (a₀ : S₀ ⊣ U₀) (a₁ : S₁ ⊣ U₁) (a₂ : S₂ ⊣ U₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (P : B₀ ⥤ B₁) (Q : B₁ ⥤ B₂)
    (r₀₁ : F ⋙ S₁ ⟶ S₀ ⋙ P) (r₁₂ : G ⋙ S₂ ⟶ S₁ ⋙ Q)
    (d₀₁ : U₀ ⋙ F ⟶ P ⋙ U₁) (d₁₂ : U₁ ⋙ G ⟶ Q ⋙ U₂)
    (N : A₀)
    (h₀₁ : a₁.unit.app (F.obj N) ≫ U₁.map (r₀₁.app N) =
      F.map (a₀.unit.app N) ≫ d₀₁.app (S₀.obj N))
    (h₁₂ : a₂.unit.app (G.obj (F.obj N)) ≫ U₂.map (r₁₂.app (F.obj N)) =
      G.map (a₁.unit.app (F.obj N)) ≫ d₁₂.app (S₁.obj (F.obj N))) :
    a₂.unit.app (G.obj (F.obj N)) ≫
        U₂.map (r₁₂.app (F.obj N) ≫ Q.map (r₀₁.app N)) =
      G.map (F.map (a₀.unit.app N)) ≫
        G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N)) := by
  have hn := d₁₂.naturality (r₀₁.app N)
  simp only [Functor.comp_obj, Functor.comp_map] at hn
  simp only [Functor.map_comp]
  rw [reassoc_of% h₁₂, ← hn, ← G.map_comp_assoc, h₀₁, G.map_comp, Category.assoc]

private theorem reverseComposition
    {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
    [Category A₀] [Category A₁] [Category A₂]
    [Category B₀] [Category B₁] [Category B₂]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (S₂ : A₂ ⥤ B₂)
    (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁) (U₂ : B₂ ⥤ A₂)
    (a₀ : S₀ ⊣ U₀) (a₁ : S₁ ⊣ U₁) (a₂ : S₂ ⊣ U₂)
    (F : A₀ ⥤ A₁) (G : A₁ ⥤ A₂) (H : A₀ ⥤ A₂)
    (P : B₀ ⥤ B₁) (Q : B₁ ⥤ B₂) (R : B₀ ⥤ B₂)
    (r₀₁ : F ⋙ S₁ ⟶ S₀ ⋙ P) (r₁₂ : G ⋙ S₂ ⟶ S₁ ⋙ Q)
    (r₀₂ : H ⋙ S₂ ⟶ S₀ ⋙ R)
    (d₀₁ : U₀ ⋙ F ⟶ P ⋙ U₁) (d₁₂ : U₁ ⋙ G ⟶ Q ⋙ U₂)
    (d₀₂ : U₀ ⋙ H ⟶ R ⋙ U₂) (a : H ≅ F ⋙ G) (b : R ≅ P ⋙ Q)
    (N : A₀)
    (h₀₁ : a₁.unit.app (F.obj N) ≫ U₁.map (r₀₁.app N) =
      F.map (a₀.unit.app N) ≫ d₀₁.app (S₀.obj N))
    (h₁₂ : a₂.unit.app (G.obj (F.obj N)) ≫ U₂.map (r₁₂.app (F.obj N)) =
      G.map (a₁.unit.app (F.obj N)) ≫ d₁₂.app (S₁.obj (F.obj N)))
    (h₀₂ : a₂.unit.app (H.obj N) ≫ U₂.map (r₀₂.app N) =
      H.map (a₀.unit.app N) ≫ d₀₂.app (S₀.obj N))
    (hd : d₀₂.app (S₀.obj N) ≫ U₂.map (b.hom.app (S₀.obj N)) =
      a.hom.app (U₀.obj (S₀.obj N)) ≫
        G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N))) :
    S₂.map (a.hom.app N) ≫ r₁₂.app (F.obj N) ≫ Q.map (r₀₁.app N) =
      r₀₂.app N ≫ b.hom.app (S₀.obj N) := by
  apply (a₂.homEquiv _ _).injective
  conv_lhs => rw [a₂.homEquiv_naturality_left]
  conv_rhs => rw [a₂.homEquiv_naturality_right]
  simp only [Adjunction.homEquiv_unit, Functor.comp_obj]
  rw [transposePasting S₀ S₁ S₂ U₀ U₁ U₂ a₀ a₁ a₂ F G P Q
    r₀₁ r₁₂ d₀₁ d₁₂ N h₀₁ h₁₂, h₀₂]
  rw [Category.assoc, hd]
  have hn := a.hom.naturality (a₀.unit.app N)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.comp_map] at hn
  simpa only [Functor.id_obj, Functor.comp_obj, Category.assoc] using congrArg
    (fun t ↦ t ≫ G.map (d₀₁.app (S₀.obj N)) ≫ d₁₂.app (P.obj (S₀.obj N))) hn.symm

private theorem transportReverseUnit
    {A₀ A₁ B₀ B₁ : Type*}
    [Category A₀] [Category A₁] [Category B₀] [Category B₁]
    (S₀ : A₀ ⥤ B₀) (S₁ : A₁ ⥤ B₁) (U₀ : B₀ ⥤ A₀) (U₁ : B₁ ⥤ A₁)
    (a₀ : S₀ ⊣ U₀) (a₁ : S₁ ⊣ U₁)
    (F F' : A₀ ⥤ A₁) (P P' : B₀ ⥤ B₁) (e : F ≅ F') (f : P ≅ P')
    (r : F ⋙ S₁ ⟶ S₀ ⋙ P) (d : U₀ ⋙ F' ⟶ P' ⋙ U₁) (N : A₀)
    (hu : a₁.unit.app (F.obj N) ≫ U₁.map (r.app N) =
      F.map (a₀.unit.app N) ≫ e.hom.app (U₀.obj (S₀.obj N)) ≫
        d.app (S₀.obj N) ≫ U₁.map (f.inv.app (S₀.obj N))) :
    a₁.unit.app (F'.obj N) ≫
        U₁.map (S₁.map (e.inv.app N) ≫ r.app N ≫ f.hom.app (S₀.obj N)) =
      F'.map (a₀.unit.app N) ≫ d.app (S₀.obj N) := by
  have hun := a₁.unit.naturality (e.inv.app N)
  simp only [Functor.id_map, Functor.comp_map] at hun
  have hn := e.inv.naturality (a₀.unit.app N)
  simp only [Functor.map_comp]
  rw [← reassoc_of% hun, reassoc_of% hu, ← reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc, ← U₁.map_comp,
    Iso.inv_hom_id_app, U₁.map_id, Category.comp_id]

namespace AlgebraicGeometry.Etale

private noncomputable def scalarExactIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    scalarExtension φ W ⋙ (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙ scalarExtension φ Z :=
  Functor.isoWhiskerLeft _
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm ≪≫
    scalarPullbackIso φ f ≪≫ Functor.isoWhiskerRight
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _

private theorem restrictionIso_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    upperStarRestrictScalarsIso φ f = upperStarRestrictScalarsIsoSheaf φ f := by
  let a := (Sheaf.restrictCoextendScalarsAdj W.smallEtaleTopology φ).comp
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
  let b := (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f).comp
    (Sheaf.restrictCoextendScalarsAdj Z.smallEtaleTopology φ)
  apply Iso.ext
  apply (conjugateEquiv b a).injective
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom]
  exact (congrArg Iso.inv ((conjugateIsoEquiv a b).apply_symm_apply (Iso.refl _))).symm

private noncomputable def restrictionExactIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    Sheaf.derivedRestrictScalars W.smallEtaleTopology φ ⋙
        (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ≅
      (upperStar (ModuleCat.{u + 1} B) f).mapDerivedCategory ⋙
        Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ :=
  Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ f)

attribute [local irreducible] restrictionExactIso

private theorem scalarExact_inverse_unit
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (N : DerivedCategoryModule A W) :
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        ((upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.obj N) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((scalarExactIso φ f).inv.app N) =
    (upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory.map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).unit.app N) ≫
      (restrictionExactIso φ f).hom.app
        ((scalarExtension φ W).obj N) := by
  have hr : (scalarPullbackIso φ f).inv = ProEtale.scalarPullbackReverseEtale φ f :=
    (congrArg Iso.inv (scalarPullback_eq φ f)).symm
  have hu := unit_mateEquiv_symm
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ))
    (TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom) N
  change L(upperStar (ModuleCat.{u + 1} A) f).map
      ((Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)).unit.app N) ≫
        (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ W).obj N) =
    (Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)).unit.app
        (L(upperStar (ModuleCat.{u + 1} A) f).obj N) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((ProEtale.scalarPullbackReverseEtale φ f).app N) at hu
  rw [← hr] at hu
  have he : scalarRestrictionPullbackIso φ f =
      Functor.isoWhiskerLeft _
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
      restrictionExactIso φ f ≪≫ Functor.isoWhiskerRight
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f).symm _ := by
    unfold restrictionExactIso
    rfl
  rw [he] at hu
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Iso.symm_hom] at hu
  simpa only [scalarExactIso, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc] using
    transportReverseUnit (scalarExtension φ W) (scalarExtension φ Z)
      (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
      (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
      _ _ _ _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
      (scalarPullbackIso φ f).inv
      (restrictionExactIso φ f).hom N hu.symm

private theorem scalarExact_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}} (v : T₁ ⟶ T₂) (j : X ⟶ T₁)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} B) j v)).hom.app
        ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((scalarExactIso φ v).hom.app N) ≫
      (scalarExactIso φ j).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
    (scalarExactIso φ (j ≫ v)).hom.app N ≫ (scalarExtension φ X).map
      ((Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) j v)).hom.app
        N) := by
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (upperStarRestrictScalarsIso φ v) (upperStarRestrictScalarsIso φ j)
    (upperStarRestrictScalarsIso φ (j ≫ v))
    (upperStarComp (ModuleCat.{u + 1} A) j v)
    (upperStarComp (ModuleCat.{u + 1} B) j v)
    (fun M ↦ by simpa using congr_app (upperStarRestrictScalarsIso_comp_hom φ j v) M)
    ((scalarExtension φ T₂).obj N)
  have hr := reverseComposition
    (scalarExtension φ T₂) (scalarExtension φ T₁) (scalarExtension φ X)
    (Sheaf.derivedRestrictScalars T₂.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars T₁.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
    (Adjunction.ofIsRightAdjoint _) (Adjunction.ofIsRightAdjoint _)
    (Adjunction.ofIsRightAdjoint _)
    (upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} A) (j ≫ v)).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) v).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (upperStar (ModuleCat.{u + 1} B) (j ≫ v)).mapDerivedCategory
    (scalarExactIso φ v).inv (scalarExactIso φ j).inv (scalarExactIso φ (j ≫ v)).inv
    (restrictionExactIso φ v).hom (restrictionExactIso φ j).hom
    (restrictionExactIso φ (j ≫ v)).hom
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} A) j v))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp (ModuleCat.{u + 1} B) j v)) N
    (scalarExact_inverse_unit φ v N)
    (scalarExact_inverse_unit φ j
      ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N))
    (scalarExact_inverse_unit φ (j ≫ v) N)
    (by simpa only [restrictionExactIso, ← restrictionIso_eq] using hd)
  apply (cancel_epi ((scalarExactIso φ (j ≫ v)).inv.app N)).1
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% hr]
  simp only [Functor.comp_obj,
    ← (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app,
    (upperStar (ModuleCat.{u + 1} B) j).mapDerivedCategory.map_id,
    Category.id_comp, Category.comp_id]

/-- The normalized scalar/pullback comparison commutes with composition of inverse images.
The displayed transports express left-derived inverse images as the levelwise exact functors. -/
theorem scalarPullback_composition
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {X T₁ T₂ : Scheme.{u}}
    (v : T₁ ⟶ T₂) (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂) (h : j₁ ≫ v = j₂)
    (N : DerivedCategoryModule A T₂) :
    (Functor.mapDerivedCategoryNatIso
          (upperStarComp (ModuleCat.{u + 1} B) j₁ v j₂ h.symm) ≪≫
        (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app ((scalarExtension φ T₂).obj N) ≫
      (upperStar (ModuleCat.{u + 1} B) j₁).mapDerivedCategory.map
        ((Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) v).symm ≪≫
        scalarPullbackIso φ v ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) v) _).hom.app N) ≫
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₁).symm ≪≫
        scalarPullbackIso φ j₁ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₁) _).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).mapDerivedCategory.obj N) =
      (Functor.isoWhiskerLeft _
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j₂).symm ≪≫
        scalarPullbackIso φ j₂ ≪≫ Functor.isoWhiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j₂) _).hom.app N ≫
        (scalarExtension φ X).map
          ((Functor.mapDerivedCategoryNatIso
              (upperStarComp (ModuleCat.{u + 1} A) j₁ v j₂ h.symm) ≪≫
            (Functor.mapDerivedCategoryCompIso _ _).symm).hom.app N)  := by
  subst j₂
  simpa only [scalarExactIso, Functor.mapDerivedCategoryTriangleIso] using
    scalarExact_composition φ v j₁ N

end AlgebraicGeometry.Etale

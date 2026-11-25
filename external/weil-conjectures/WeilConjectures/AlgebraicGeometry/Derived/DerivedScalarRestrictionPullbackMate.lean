/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities

/-! # Invertibility of the derived scalar and geometric pullback mate

Source: Stacks 07A4 and 0G7E; blueprint scalar-six direct-image proof,
finite rings paragraph (blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).
The proofs use flat resolutions and the normalized scalar adjunction units.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
attribute [local instance] pbcRestriction_isRightAdjoint
private theorem transport_left_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F F' : A ⥤ C} {G G' : B ⥤ D} (e : F' ≅ F) (g : G' ≅ G)
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂)
    [IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)))] :
    IsIso (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _
      (Functor.whiskerLeft U₁ e.hom ≫ τ ≫ Functor.whiskerRight g.inv U₂)))) := by
  have (P : A) : IsIso ((𝟙 E₁ : E₁ ⟶ E₁).app P) := by
    change IsIso (𝟙 _)
    infer_instance
  have (P : C) : IsIso ((𝟙 E₂ : E₂ ⟶ E₂).app P) := by
    change IsIso (𝟙 _)
    infer_instance
  apply (NatTrans.isIso_iff_isIso_app _).2
  intro P
  apply localized_mate_isIso_at a₁ a₂ a₁ a₂
    (𝟭 A) (𝟭 B) (𝟭 C) (𝟭 D) (𝟙 E₁) (𝟙 E₂)
    (Iso.refl U₁) (Iso.refl U₂) e g τ
    (Functor.whiskerLeft U₁ e.hom ≫ τ ≫ Functor.whiskerRight g.inv U₂)
    (fun P ↦ by simp) (fun P ↦ by simp) (fun N ↦ by simp) P

universe u
-- Elaborate local-relation flatness across both site presentations.
private theorem pro_flat (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (upperStar (ModuleCat.{u + 1} A) f).PreservesFlat := by
  have := MorphismProperty.Over.representablyFlat_pullback @WeaklyEtale f
  refine ⟨fun hF ↦ ?_⟩
  exact flat_pullback_of_local_relations (G := MorphismProperty.Over.pullback
    @WeaklyEtale ⊤ f) (Scheme.ProEt.coverPreserving_overPullback f) hF

private theorem pro_ordinary_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv (scalarAdjunction (Scheme.ProEt.topology Y) a)
      (scalarAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).hom))) := by
  apply isIso_left_mate_of_iterated
    (scalarAdjunction (Scheme.ProEt.topology Y) a)
    (scalarAdjunction (Scheme.ProEt.topology X) a)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
  have h := mate_of_conjugate
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) a)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) a)
    (Iso.refl _) (show lowerStar (ModuleCat.{u + 1} B) f ⋙
      Sheaf.restrictScalars (Scheme.ProEt.topology Y) a ⟶
      Sheaf.restrictScalars (Scheme.ProEt.topology X) a ⋙
        lowerStar (ModuleCat.{u + 1} A) f from 𝟙 _) (by
      ext F V x
      simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
        Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
        Category.id_comp]
      exact congrArg (fun k ↦ k.hom x)
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} a).right_triangle_components
          _))
  change (mateEquiv _ _ (TwoSquare.mk _ _ _ _
    (upperStarRestrictScalarsIso a f).hom)) = _ at h
  rw [h]
  infer_instance
-- Instantiate the normalized flat-resolution comparison.
private theorem pro_computed_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (upperStarRestrictScalarsIso a f)).hom))) := by
  have := pro_flat A f
  have : IsIso (((mateEquiv
      (scalarAdjunction (Scheme.ProEt.topology Y) a)
      (scalarAdjunction (Scheme.ProEt.topology X) a)).symm
      (TwoSquare.mk _ _ _ _ (upperStarRestrictScalarsIso a f).symm.inv))) := by
    simpa only [Iso.symm_inv] using pro_ordinary_iso a f
  have h := derived_mate_isIso_of_flat
    (A := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A))
    (B := Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} B))
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (D := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (scalarAdjunction (Scheme.ProEt.topology Y) a)
    (scalarAdjunction (Scheme.ProEt.topology X) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a)
    (upperStar (ModuleCat.{u + 1} A) f)
    (upperStar (ModuleCat.{u + 1} B) f)
    (upperStarRestrictScalarsIso a f).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (upperStarRestrictScalarsIso a f).symm).inv =
      (Functor.mapDerivedCategoryNatIso (upperStarRestrictScalarsIso a f)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm (upperStarRestrictScalarsIso a f).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

/-- The pro-etale inverse scalar mate is invertible for arbitrary coefficient maps.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).
Proof: the ordinary left mate is invertible by iterated mates and pointwise
restriction/coextension. Representably flat base change preserves the local relation
criterion for flat sheaves. The resulting flat K-flat resolutions compute the
left derived scalar mate. Finally transport the mate across uniqueness of scalar
left adjoints and the canonical exact geometric comparison. -/
theorem proEtaleScalarPullbackMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        (Scheme.ProEt.topology Y) a))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        (Scheme.ProEt.topology X) a))).symm
      (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso a f).hom))) := by
  have := pro_computed_iso a f
  have := isIso_left_mate_change_adjunction
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology Y) a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology X) a))
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology Y) a).adjunction
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) a).adjunction
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom
  exact transport_left_mate
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology Y) a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      (Scheme.ProEt.topology X) a))
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIso a f)).hom
-- Instantiate the normalized flat-resolution comparison.
private theorem et_computed_iso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData Y.smallEtaleTopology a).adjunction
      (scalarDerivedAdjunctionData X.smallEtaleTopology a).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom))) := by
  have hOrd : IsIso (((mateEquiv
      (scalarAdjunction Y.smallEtaleTopology a)
      (scalarAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).hom))) := by
    apply isIso_left_mate_of_iterated (scalarAdjunction Y.smallEtaleTopology a)
      (scalarAdjunction X.smallEtaleTopology a)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    rw [Etale.underived_mate]
    infer_instance
  have : IsIso (((mateEquiv
      (scalarAdjunction Y.smallEtaleTopology a)
      (scalarAdjunction X.smallEtaleTopology a)).symm
      (TwoSquare.mk _ _ _ _ (Etale.upperStarRestrictScalarsIsoSheaf a f).symm.inv))) := by
    simpa only [Iso.symm_inv] using hOrd
  have h := derived_mate_isIso_of_flat
    (A := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B := Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (D := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (scalarAdjunction Y.smallEtaleTopology a)
    (scalarAdjunction X.smallEtaleTopology a)
    (scalarDerivedAdjunctionData Y.smallEtaleTopology a)
    (scalarDerivedAdjunctionData X.smallEtaleTopology a)
    (Etale.upperStar (ModuleCat.{u + 1} A) f)
    (Etale.upperStar (ModuleCat.{u + 1} B) f)
    (Etale.upperStarRestrictScalarsIsoSheaf a f).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (Etale.upperStarRestrictScalarsIsoSheaf a f).symm).inv =
      (Functor.mapDerivedCategoryNatIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm (Etale.upperStarRestrictScalarsIsoSheaf a f).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

/-- The etale inverse scalar mate is invertible for arbitrary coefficient maps.
Source: Stacks 07A4 and 0G7E
(blueprint: lem-sfb-proetale-scalar-pullback-mate-invertible).
Proof: apply the ordinary restriction/direct-image mate identity, then the flat
resolution comparison. Etale pullback preserves flatness stalkwise. Uniqueness of
left adjoints and the exact geometric comparison transport invertibility to the
specified scalar adjunction. -/
theorem etaleScalarPullbackMate_isIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (a : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (((mateEquiv
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        Y.smallEtaleTopology a))
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
        X.smallEtaleTopology a))).symm
      (TwoSquare.mk _ _ _ _ (Etale.scalarRestrictionPullbackIso a f).hom))) := by
  have := et_computed_iso a f
  have := isIso_left_mate_change_adjunction
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      Y.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      X.smallEtaleTopology a))
    (scalarDerivedAdjunctionData Y.smallEtaleTopology a).adjunction
    (scalarDerivedAdjunctionData X.smallEtaleTopology a).adjunction
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom
  exact transport_left_mate
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      Y.smallEtaleTopology a))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars
      X.smallEtaleTopology a))
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) f)
    (Functor.mapDerivedCategorySquareIso (Etale.upperStarRestrictScalarsIsoSheaf a f)).hom
end AlgebraicGeometry.ProEtale

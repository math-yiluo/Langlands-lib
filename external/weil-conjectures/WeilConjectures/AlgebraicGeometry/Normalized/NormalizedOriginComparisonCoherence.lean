/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedOriginScalarComparisons
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-!
# Coherence of comparison with quotient scalar extension

## References

* Stacks Tags 06YY, 07A4 and 09B1, coefficient-reduction refinement
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.TwoSquare
namespace AlgebraicGeometry.ProEtale

section MateComposition
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*}
  [Category A₀] [Category A₁] [Category A₂]
  [Category B₀] [Category B₁] [Category B₂]
  {L₁ : A₀ ⥤ A₁} {R₁ : A₁ ⥤ A₀} {L₂ : A₁ ⥤ A₂} {R₂ : A₂ ⥤ A₁}
  {L₃ : A₀ ⥤ A₂} {R₃ : A₂ ⥤ A₀}
  {l₁ : B₀ ⥤ B₁} {r₁ : B₁ ⥤ B₀} {l₂ : B₁ ⥤ B₂} {r₂ : B₂ ⥤ B₁}
  {l₃ : B₀ ⥤ B₂} {r₃ : B₂ ⥤ B₀}
  (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃)
  (b₁ : l₁ ⊣ r₁) (b₂ : l₂ ⊣ r₂) (b₃ : l₃ ⊣ r₃)
  {F₀ : A₀ ⥤ B₀} {F₁ : A₁ ⥤ B₁} {F₂ : A₂ ⥤ B₂}
  (t₁ : TwoSquare R₁ F₁ F₀ r₁) (t₂ : TwoSquare R₂ F₂ F₁ r₂)
  (t₃ : TwoSquare R₃ F₂ F₀ r₃)
  (eA : R₂ ⋙ R₁ ≅ R₃) (eB : r₂ ⋙ r₁ ≅ r₃)
  (h : (t₂ ≫ₕ t₁).whiskerTop eA.inv = t₃.whiskerBottom eB.inv)

include h in
private theorem mateComp :
    (((mateEquiv a₁ b₁).symm t₁) ≫ᵥ ((mateEquiv a₂ b₂).symm t₂)).whiskerLeft
        (Adjunction.leftAdjointCompIso a₁ a₂ a₃ eA).hom =
    ((mateEquiv a₃ b₃).symm t₃).whiskerRight
        (Adjunction.leftAdjointCompIso b₁ b₂ b₃ eB).hom := by
  apply (mateEquiv a₃ (b₁.comp b₂)).injective
  rw [conjugateEquiv_mateEquiv_vcomp a₃ (a₁.comp a₂) (b₁.comp b₂),
    mateEquiv_conjugateEquiv_vcomp a₃ b₃ (b₁.comp b₂)]
  rw [mateEquiv_hcomp a₁ b₁ a₂ b₂]
  simp only [Equiv.apply_symm_apply, Adjunction.leftAdjointCompIso_hom,
    Adjunction.leftAdjointCompNatTrans]
  exact h
end MateComposition

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem mateUnit
    {C D : Type*} [Category C] [Category D]
    {L₁ R₁ : C ⥤ C} {L₂ R₂ : D ⥤ D}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (F : C ⥤ D)
    (e₁ : R₁ ≅ 𝟭 C) (e₂ : R₂ ≅ 𝟭 D) (X : C) :
    ((mateEquiv adj₁ adj₂).symm
      (TwoSquare.mk _ _ _ _
        (Functor.whiskerRight e₁.hom F ≫ Functor.whiskerLeft F e₂.inv))).app X ≫
      F.map ((adj₁.leftAdjointIdIso e₁).hom.app X) =
    (adj₂.leftAdjointIdIso e₂).hom.app (F.obj X) := by
  let u₁ := adj₁.leftAdjointIdIso e₁
  let u₂ := adj₂.leftAdjointIdIso e₂
  have hu : adj₁.unit.app X ≫ e₁.hom.app (L₁.obj X) ≫ u₁.hom.app X = 𝟙 X := by
    have hn := e₁.hom.naturality (u₁.hom.app X)
    dsimp only [Functor.id_map] at hn
    rw [← hn]
    have h := unit_conjugateEquiv Adjunction.id adj₁ u₁.hom X
    simp only [u₁, Adjunction.conjugateEquiv_leftAdjointIdIso_hom,
      Adjunction.id_unit, NatTrans.id_app, Category.id_comp] at h
    rw [← Category.assoc, ← h]
    exact e₁.inv_hom_id_app X
  change _ ≫ F.map (u₁.hom.app X) = u₂.hom.app (F.obj X)
  simp only [mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Functor.comp_map,
    Functor.map_comp, L₂.map_id, Category.id_comp, Category.assoc]
  rw [← reassoc_of% (Adjunction.leftAdjointIdIso_hom_app adj₂ e₂ (F.obj (L₁.obj X)))]
  simp only [Functor.id_obj, Category.id_comp]
  change L₂.map (F.map (adj₁.unit.app X)) ≫
    L₂.map (F.map (e₁.hom.app (L₁.obj X))) ≫
    (u₂.hom.app (F.obj (L₁.obj X))) ≫ F.map (u₁.hom.app X) = _
  have hn := u₂.hom.naturality (F.map (u₁.hom.app X))
  dsimp only [Functor.id_map] at hn
  rw [← hn]
  rw [← L₂.map_comp_assoc, ← L₂.map_comp_assoc,
    ← F.map_comp, ← F.map_comp, Category.assoc, hu, F.map_id X, L₂.map_id (F.obj X)]
  exact Category.id_comp _

private theorem ordinaryRestrictionUnit (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    (pbcComparisonRestrict T (RingHom.id R)).inv =
      Functor.whiskerRight
        (normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl).hom
        (comparisonUpperStar (ModuleCat.{u + 1} R) T) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).leftUnitor.hom ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).rightUnitor.inv ≫
      Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} R) T)
        (normalizedOriginRestrictionUnit (Scheme.ProEt.topology T) (RingHom.id R) rfl).inv := by
  let a := comparisonAdjunction (ModuleCat.{u + 1} R) T
  let b := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology (RingHom.id R)
  let c := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) (RingHom.id R)
  change (conjugateEquiv (a.comp c) (b.comp a)).symm (𝟙 _) = _
  apply (conjugateEquiv (a.comp c) (b.comp a)).injective
  rw [Equiv.apply_symm_apply]
  symm
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _ a]
  rw [← conjugateEquiv_comp _ (a.comp Adjunction.id)]
  rw [← conjugateEquiv_comp _ (Adjunction.id.comp a)]
  rw [conjugateEquiv_whiskerLeft c Adjunction.id a,
    conjugateEquiv_whiskerRight Adjunction.id b a,
    conjugateEquiv_leftUnitor_hom a]
  have hr : conjugateEquiv (a.comp Adjunction.id) a
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).rightUnitor.inv =
      (comparisonLowerStar (ModuleCat.{u + 1} R) T).leftUnitor.hom := by
    ext X
    simp
  rw [hr]
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Category.id_comp, Category.assoc]
  dsimp only [b, c, normalizedOriginRestrictionUnit, Sheaf.restrictCoextendScalarsAdj]
  simp only [Functor.comp_obj, Functor.id_obj,
    conjugateEquiv_apply_app, Adjunction.id_unit, NatTrans.id_app, Functor.id_map,
    Category.id_comp, Functor.map_comp, Adjunction.id_counit, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.assoc, ObjectProperty.FullSubcategory.comp_hom,
    sheafCompose_map_hom, NatTrans.comp_app, Functor.whiskerRight_app, ModuleCat.hom_comp,
    LinearMap.coe_comp, Function.comp_apply, ObjectProperty.FullSubcategory.id_hom,
    ModuleCat.hom_id]
  rename_i U x
  apply ModuleCat.CoextendScalars.ext
  apply LinearMap.ext
  intro r
  change R at r
  let M := ((comparisonLowerStar (ModuleCat.{u + 1} R) T).obj X).obj.obj U
  let z : (ModuleCat.coextendScalars (RingHom.id R)).obj M := x
  change r • (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z) (1 : R) =
    (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z) r
  have h := (ModuleCat.CoextendScalars.equiv (RingHom.id R) M z).map_smul r (1 : R)
  simpa [ModuleCat.restrictScalars.smul_def, mul_one] using h.symm

private theorem derivedRestrictionUnit (T : Scheme.{u})
    (R : Type (u + 1)) [CommRing R] :
    (pbcDerivedComparisonRestrict T (RingHom.id R)).inv =
      Functor.whiskerRight
        (Functor.mapDerivedCategoryNatIso
          (normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory ≫
      Functor.whiskerLeft
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory
        (Functor.mapDerivedCategoryNatIso
          (normalizedOriginRestrictionUnit (Scheme.ProEt.topology T) (RingHom.id R) rfl) ≪≫
          Functor.mapDerivedCategoryIdIso _).inv := by
  have ho (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R)) :
      (pbcComparisonRestrict T (RingHom.id R)).hom.app X ≫
        (comparisonUpperStar (ModuleCat.{u + 1} R) T).map
          ((normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl).hom.app
            X) =
      (normalizedOriginRestrictionUnit (Scheme.ProEt.topology T) (RingHom.id R) rfl).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) T).obj X) := by
    apply (cancel_epi ((pbcComparisonRestrict T (RingHom.id R)).inv.app X)).1
    rw [Iso.inv_hom_id_app_assoc, ordinaryRestrictionUnit]
    simp
  ext K
  have h := Functor.mapDerivedCategorySquareIso_hom_app_id
    (pbcComparisonRestrict T (RingHom.id R))
    (normalizedOriginRestrictionUnit T.smallEtaleTopology (RingHom.id R) rfl)
    (normalizedOriginRestrictionUnit (Scheme.ProEt.topology T) (RingHom.id R) rfl) ho K
  change (pbcDerivedComparisonRestrict T (RingHom.id R)).hom.app K ≫ _ = _ at h
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  apply (cancel_epi ((pbcDerivedComparisonRestrict T (RingHom.id R)).hom.app K)).1
  rw [Iso.hom_inv_id_app]
  rw [← Category.assoc, h, Iso.hom_inv_id_app]
  rfl

private theorem comparisonScalarUnit (T : Scheme.{u})
    {R : Type (u + 1)} [CommRing R] (φ : R →+* R) (hφ : φ = RingHom.id R)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.map
      ((normalizedOriginScalarUnit T.smallEtaleTopology φ hφ).hom.app K) =
    (pbcComparisonReduction T φ).inv.app K ≫
      (normalizedOriginScalarUnit (Scheme.ProEt.topology T) φ hφ).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) := by
  subst φ
  apply (cancel_epi ((pbcComparisonReduction T (RingHom.id R)).hom.app K)).1
  simp only [Iso.hom_inv_id_app_assoc]
  change (pbcComparisonReductionMap T (RingHom.id R)).app K ≫ _ = _
  unfold pbcComparisonReductionMap
  rw [derivedRestrictionUnit]
  exact mateUnit _ _ _ _ _ K

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ordinaryRestrictionComp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ) :
    (pbcComparisonRestrict T χ).hom ≫
      Functor.whiskerRight (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).inv
        (comparisonUpperStar (ModuleCat.{u + 1} R) T) =
    Functor.whiskerLeft (comparisonUpperStar (ModuleCat.{u + 1} V) T)
        (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight (pbcComparisonRestrict T ψ).hom
        (Sheaf.restrictScalars (Scheme.ProEt.topology T) φ) ≫
      (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft (Sheaf.restrictScalars T.smallEtaleTopology ψ)
        (pbcComparisonRestrict T φ).hom ≫ (Functor.associator _ _ _).inv := by
  let aR := comparisonAdjunction (ModuleCat.{u + 1} R) T
  let aS := comparisonAdjunction (ModuleCat.{u + 1} S) T
  let aV := comparisonAdjunction (ModuleCat.{u + 1} V) T
  let eφ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology φ
  let eψ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology ψ
  let eχ := Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology χ
  let pφ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) φ
  let pψ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) ψ
  let pχ := Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) χ
  apply (conjugateEquiv ((eψ.comp eφ).comp aR) (aV.comp pχ)).injective
  rw [← conjugateEquiv_comp _ (eχ.comp aR)]
  rw [← conjugateEquiv_comp _ (aV.comp (pψ.comp pφ))]
  rw [← conjugateEquiv_comp _ ((aV.comp pψ).comp pφ)]
  rw [← conjugateEquiv_comp _ ((eψ.comp aS).comp pφ)]
  rw [← conjugateEquiv_comp _ (eψ.comp (aS.comp pφ))]
  rw [← conjugateEquiv_comp _ (eψ.comp (eφ.comp aR))]
  have hc {U V : Type (u + 1)} [CommRing U] [CommRing V] (f : U →+* V) :
      conjugateEquiv
        ((Sheaf.restrictCoextendScalarsAdj T.smallEtaleTopology f).comp
          (comparisonAdjunction (ModuleCat.{u + 1} U) T))
        ((comparisonAdjunction (ModuleCat.{u + 1} V) T).comp
          (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology T) f))
        (pbcComparisonRestrict T f).hom = 𝟙 _ := by
    change (conjugateEquiv _ _)
      ((conjugateEquiv _ _).symm (𝟙 _)) = _
    exact Equiv.apply_symm_apply _ _
  simp only [conjugateEquiv_whiskerRight, conjugateEquiv_whiskerLeft,
    conjugateEquiv_associator_hom, conjugateEquiv_associator_inv]
  dsimp only [aR, aS, aV, eφ, eψ, eχ, pφ, pψ, pχ]
  rw [hc, hc, hc]
  ext X : 2
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, NatTrans.id_app,
    Category.comp_id, Category.id_comp]
  ext U : 3
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem derivedRestrictionComp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V))) :
    (pbcDerivedComparisonRestrict T χ).hom.app K ≫
      (comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.map
        ((Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology h).inv.app K) =
    (Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) h).inv.app
        ((comparisonUpperStar (ModuleCat.{u + 1} V) T).mapDerivedCategory.obj K) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ).map
        ((pbcDerivedComparisonRestrict T ψ).hom.app K) ≫
      (pbcDerivedComparisonRestrict T φ).hom.app
        ((Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ).obj K) := by
  have ho (X : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} V)) :=
    congr_app (ordinaryRestrictionComp T φ ψ χ h) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Category.comp_id, Category.id_comp] at ho
  have hd := Functor.mapDerivedCategorySquareIso_hom_app_comp
    (pbcComparisonRestrict T ψ) (pbcComparisonRestrict T φ)
    (pbcComparisonRestrict T χ)
    (Sheaf.restrictScalarsCompIso (Scheme.ProEt.topology T) φ ψ χ h).symm
    (Sheaf.restrictScalarsCompIso T.smallEtaleTopology φ ψ χ h).symm ho K
  exact hd

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
private theorem comparisonScalarComp (T : Scheme.{u})
    {R S V : Type (u + 1)} [CommRing R] [CommRing S] [CommRing V]
    (φ : R →+* S) (ψ : S →+* V) (χ : R →+* V) (h : χ = ψ.comp φ)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (comparisonUpperStar (ModuleCat.{u + 1} V) T).mapDerivedCategory.map
        ((pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ h).hom.app K) ≫
      (pbcComparisonReduction T χ).inv.app K =
    (pbcComparisonReduction T ψ).inv.app
        ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) ≫
      (pbcFixedScalarExtension (Scheme.ProEt.topology T) ψ).map
        ((pbcComparisonReduction T φ).inv.app K) ≫
      (pbcFixedScalarExtensionComp (Scheme.ProEt.topology T) φ ψ χ h).hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) := by
  let t₁ := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T φ).inv
  let t₂ := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T ψ).inv
  let t₃ := TwoSquare.mk _ _ _ _ (pbcDerivedComparisonRestrict T χ).inv
  let eA := Sheaf.derivedRestrictScalarsCompIso T.smallEtaleTopology h
  let eB := Sheaf.derivedRestrictScalarsCompIso (Scheme.ProEt.topology T) h
  have ht : (t₂ ≫ₕ t₁).whiskerTop eA.inv = t₃.whiskerBottom eB.inv := by
    ext X
    dsimp [t₁, t₂, t₃, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom]
    simp only [Category.id_comp, Category.comp_id]
    apply (cancel_epi ((pbcDerivedComparisonRestrict T χ).hom.app X)).1
    rw [← Category.assoc, ← Category.assoc, derivedRestrictionComp]
    simp [Category.assoc, ← Functor.map_comp]
    rfl
  have hm := mateComp
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars T.smallEtaleTopology χ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) ψ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) χ))
    t₁ t₂ t₃ eA eB ht
  have hmK := congrArg (fun w ↦ w.app K) hm
  dsimp only [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
    TwoSquare.mk, NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app] at hmK
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hmK
  change (pbcFixedScalarExtension (Scheme.ProEt.topology T) ψ).map
      ((pbcComparisonReduction T φ).hom.app K) ≫
    (pbcComparisonReduction T ψ).hom.app
      ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K) ≫
    (comparisonUpperStar (ModuleCat.{u + 1} V) T).mapDerivedCategory.map
      ((pbcFixedScalarExtensionComp T.smallEtaleTopology φ ψ χ h).hom.app K) =
    (pbcFixedScalarExtensionComp (Scheme.ProEt.topology T) φ ψ χ h).hom.app
      ((comparisonUpperStar (ModuleCat.{u + 1} R) T).mapDerivedCategory.obj K) ≫
    (pbcComparisonReduction T χ).hom.app K at hmK
  apply (cancel_epi ((pbcComparisonReduction T ψ).hom.app
    ((pbcFixedScalarExtension T.smallEtaleTopology φ).obj K))).1
  apply (cancel_epi ((pbcFixedScalarExtension (Scheme.ProEt.topology T) ψ).map
    ((pbcComparisonReduction T φ).hom.app K))).1
  rw [reassoc_of% hmK]
  simp only [Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarTensorPullbackNormalization

/-! # Unbounded proper mate projection step

This is the proper-factor identity used in the restricted coefficient projection.
It removes the bounded-below witnesses from the existing mate calculation; the
remaining open-factor calculation is handled by the parent theorem.
(blueprint: lem-pur-etale-quotient-tensor-projection-proper-mate)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

-- Keep derived functors and chosen adjoints abstract while elaborating the diagrams.
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory
  ProEtale.pbcFixedScalarExtension derivedTensor upperStar lowerStar

private theorem unbounded_restricted_mate_tensor
    {C₁ : Type*} {D₁ : Type*} {C₂ : Type*} {D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    {F₁ : C₁ ⥤ D₁} {R₁ : D₁ ⥤ C₁} {F₂ : C₂ ⥤ D₂} {R₂ : D₂ ⥤ C₂}
    (adj₁ : F₁ ⊣ R₁) (adj₂ : F₂ ⊣ R₂)
    (S : C₁ ⥤ C₂) (S' : D₁ ⥤ D₂) (U : C₂ ⥤ C₁) (U' : D₂ ⥤ D₁)
    (c : S ⋙ F₂ ⟶ F₁ ⋙ S') (a : U ⋙ F₁ ⟶ F₂ ⋙ U')
    (T : C₁ ⥤ C₁) (T' : D₁ ⥤ D₁)
    (e : S ⋙ U ≅ T) (e' : S' ⋙ U' ≅ T')
    (t : ∀ X, F₁.obj (T.obj X) ⟶ T'.obj (F₁.obj X))
    (h : ∀ X, a.app (S.obj X) ≫ U'.map (c.app X) ≫ e'.hom.app (F₁.obj X) =
      F₁.map (e.hom.app X) ≫ t X) (J : D₁) :
    U.map ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ c)).app J) ≫
        (mateEquiv adj₂ adj₁ (TwoSquare.mk _ _ _ _ a)).app (S'.obj J) =
      e.hom.app (R₁.obj J) ≫
        adj₁.homEquiv _ _ (t (R₁.obj J) ≫ T'.map (adj₁.counit.app J)) ≫
        R₁.map (e'.inv.app J) := by
  let b := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ c)).app J
  let d := (mateEquiv adj₂ adj₁ (TwoSquare.mk _ _ _ _ a)).app (S'.obj J)
  have hb : F₂.map b ≫ adj₂.counit.app (S'.obj J) =
      c.app (R₁.obj J) ≫ S'.map (adj₁.counit.app J) :=
    mateEquiv_counit adj₁ adj₂ (TwoSquare.mk _ _ _ _ c) J
  have hd : F₁.map d ≫ adj₁.counit.app (U'.obj (S'.obj J)) =
      a.app (R₂.obj (S'.obj J)) ≫ U'.map (adj₂.counit.app (S'.obj J)) :=
    mateEquiv_counit adj₂ adj₁ (TwoSquare.mk _ _ _ _ a) (S'.obj J)
  change U.map b ≫ d = e.hom.app (R₁.obj J) ≫
    adj₁.homEquiv _ (T'.obj J)
      (t (R₁.obj J) ≫ T'.map (adj₁.counit.app J)) ≫ R₁.map (e'.inv.app J)
  apply (cancel_mono (R₁.map (e'.hom.app J))).1
  simp only [Category.assoc]
  erw [← R₁.map_comp, Iso.inv_hom_id_app, R₁.map_id, Category.comp_id]
  apply (adj₁.homEquiv _ _).symm.injective
  conv_rhs =>
    rw [adj₁.homEquiv_naturality_left_symm]
    rw [Equiv.symm_apply_apply]
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  rw [adj₁.counit_naturality]
  dsimp only [Functor.comp_obj]
  rw [reassoc_of% hd]
  have hn := a.naturality b
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← Category.assoc, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [← U'.map_comp_assoc, hb, U'.map_comp, Category.assoc]
  have he := e'.hom.naturality (adj₁.counit.app J)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  rw [he]
  simpa only [Category.assoc] using
    congrArg (fun k ↦ k ≫ T'.map (adj₁.counit.app J)) (h (R₁.obj J))

private def unbounded_restricted_tensor_comparison
    {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    {S : C₁ ⥤ C₂} {S' : D₁ ⥤ D₂} {U : C₂ ⥤ C₁} {U' : D₂ ⥤ D₁}
    {F₁ : C₁ ⥤ D₁} {F₂ : C₂ ⥤ D₂} {T' : D₁ ⥤ D₁}
    (c : S ⋙ F₂ ⟶ F₁ ⋙ S') (a : U ⋙ F₁ ⟶ F₂ ⋙ U')
    (e' : S' ⋙ U' ⟶ T') : (S ⋙ U) ⋙ F₁ ⟶ F₁ ⋙ T' where
  app X := a.app (S.obj X) ≫ U'.map (c.app X) ≫ e'.app (F₁.obj X)
  naturality X Y k := by
    have ha := a.naturality (S.map k)
    have hc := c.naturality k
    have he := e'.naturality (F₁.map k)
    dsimp only [Functor.comp_map, Functor.comp_obj] at ha hc he ⊢
    rw [reassoc_of% ha, ← U'.map_comp_assoc, hc, U'.map_comp, Category.assoc]
    rw [he]
    simp only [Category.assoc]

private theorem unbounded_scalar_natTrans_ext
    {A : Type (u + 1)} [CommRing A] (W : Scheme.{u})
    {D : Type*} [Category D] {F G : DerivedCategoryModule A W ⥤ D}
    (α β : F ⟶ G)
    (h : ∀ P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ,
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
        α.app (_root_.DerivedCategory.Q.obj P) = β.app (_root_.DerivedCategory.Q.obj P)) :
    α = β := by
  refine Localization.natTrans_ext _root_.DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) (fun K ↦ ?_)
  obtain ⟨P, π, hπ, _, hP⟩ := CochainComplex.exists_quasiIso_flat_kFlat K
  have := hπ
  apply (cancel_epi (F.map (_root_.DerivedCategory.Q.map π))).1
  rw [α.naturality, β.naturality, h P hP]

private theorem unbounded_scalar_tensor_pullback_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (C : DerivedCategoryModule A W) :
    (scalarRestrictionPullbackIso φ f).hom.app ((scalarExtension φ W).obj C) ≫
        (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
          ((scalarPullbackIso φ f).hom.app C) ≫
        (scalarTensorIso φ Z).hom.app (L(upperStar (ModuleCat.{u + 1} A) f).obj C) =
      L(upperStar (ModuleCat.{u + 1} A) f).map ((scalarTensorIso φ W).hom.app C) ≫
        ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
          (scalarCoefficient φ W) ≫
        ((derivedTensor (ModuleCat.{u + 1} A) Z).obj
          (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map
          (scalarCoefficientPullbackIso φ f).hom := by
  let FA := L(upperStar (ModuleCat.{u + 1} A) f)
  let SW := scalarExtension φ W
  let UW := Sheaf.derivedRestrictScalars W.smallEtaleTopology φ
  let TZ := (derivedTensor (ModuleCat.{u + 1} A) Z).flip.obj (scalarCoefficient φ Z)
  let α : (SW ⋙ UW) ⋙ FA ⟶ FA ⋙ TZ :=
    unbounded_restricted_tensor_comparison (scalarPullbackIso φ f).hom
      (scalarRestrictionPullbackIso φ f).hom (scalarTensorIso φ Z).hom
  let β : (SW ⋙ UW) ⋙ FA ⟶ FA ⋙ TZ :=
    Functor.whiskerRight (scalarTensorIso φ W).hom FA ≫
      (derivedTensorRightCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} A) f (scalarCoefficient φ W)).hom ≫
      Functor.whiskerLeft FA
        ((derivedTensor (ModuleCat.{u + 1} A) Z).flip.map
          (scalarCoefficientPullbackIso φ f).hom)
  have h : α = β := by
    apply unbounded_scalar_natTrans_ext W
    intro P hP
    have hc := (scalarPullbackIso_existsUnique φ f).choose_spec.1 P hP
    have hm := scalarTensorPullback_normalization_kFlat φ f P hP
      ((scalarPullbackIso φ f).hom.app (_root_.DerivedCategory.Q.obj P))
      hc
    simpa only [α, β, unbounded_restricted_tensor_comparison, FA, SW, UW, TZ,
      Functor.comp_obj,
      Functor.comp_map, Functor.map_id, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc,
      derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
      leftDerivedUpperStarTensorIso_hom, Functor.flip_map_app] using hm
  have hC := NatTrans.congr_app h C
  simpa only [α, β, unbounded_restricted_tensor_comparison, FA, SW, UW, TZ,
      Functor.comp_obj,
      Functor.comp_map, Functor.map_id, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
    leftDerivedUpperStarTensorIso_hom, Functor.flip_map_app] using hC

/-- The unbounded scalar mate followed by direct-image restriction is the proper
projection map after the canonical scalar/tensor identification.
Source: Zheng, Proposition 2.29(2), Construction 2.26; Stacks Tag 0GL6.
(blueprint: lem-pur-etale-quotient-tensor-projection-proper-mate).

Proof: resolve an arbitrary derived object by a K-flat complex with flat terms.
The scalar/pullback normalization and the tensor comparison give the displayed
square on that representative. Naturality and localization extensionality pass it
to the unbounded derived category; the mate counit equation identifies the
result with the proper projection map.
-/
theorem scalarMate_restrict_eq_projection_unbounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : DerivedCategoryModule A Z) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let T := derivedTensor (ModuleCat.{u + 1} A) Z
  let b := (scalarCoefficientPullbackIso φ f).hom
  have ht := (T.map (adj.counit.app J)).naturality b
  dsimp only [Functor.comp_obj, Functor.id_obj] at ht
  have hp : adj.homEquiv _ _
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J)).app
          (scalarCoefficient φ W) ≫
        (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J))).map b ≫
        (T.flip.obj (scalarCoefficient φ Z)).map (adj.counit.app J)) =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map ((T.obj J).map b) := by
    simp only [Functor.flip_obj_map, Functor.id_obj]
    rw [ht, ← Category.assoc, adj.homEquiv_naturality_right]
    rfl
  have hm := unbounded_restricted_mate_tensor adj
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (scalarExtension φ W) (scalarExtension φ Z)
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ)
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
    (scalarPullbackIso φ f).hom (scalarRestrictionPullbackIso φ f).hom
    ((derivedTensor (ModuleCat.{u + 1} A) W).flip.obj (scalarCoefficient φ W))
    (T.flip.obj (scalarCoefficient φ Z))
    (scalarTensorIso φ W) (scalarTensorIso φ Z)
    (fun C ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app C).app
        (scalarCoefficient φ W) ≫
      (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj C)).map b)
    (unbounded_scalar_tensor_pullback_square φ f) J
  simp only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Category.assoc] at hp hm
  rw [hp] at hm
  simpa only [scalarMate, scalarRestrictionDirectImageMap, adj, T, b,
    TwoSquare.mk, Functor.map_comp,
    Category.assoc] using hm

end AlgebraicGeometry.Etale

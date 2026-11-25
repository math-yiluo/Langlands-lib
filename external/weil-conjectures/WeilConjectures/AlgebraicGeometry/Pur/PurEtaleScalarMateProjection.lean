/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackRepresentativeData
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.CategoryTheory.Etale.EtaleUnboundedRestrictionComparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcActualScalarPullbackSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsFunctorComparisons
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarTensorPullbackNormalization
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoUniqueness

/-!
# Restriction of the derived coefficient mate equals the projection morphism

## References

* Stacks 0GL6
* Stacks Project, Tags 07A4, 0G7E and 07A7
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

private theorem restricted_mate_tensor
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

private def restricted_tensor_comparison
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

private theorem scalar_natTrans_ext
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

/-- The canonical scalar/pullback comparison is uniquely normalized on K-flat models. -/
theorem scalarPullbackIso_existsUnique
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    ∃! c : scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
        L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z,
      ∀ (P : CochainComplex (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ),
      (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P →
      c.hom.app (_root_.DerivedCategory.Q.obj P) ≫
          (scalarExtension φ Z).map (scalarGeometricRepresentative A f P) ≫
          scalarExtensionRepresentative φ Z
            (((upperStar (ModuleCat.{u + 1} A) f).mapHomologicalComplex (.up ℤ)).obj P) =
        L(upperStar (ModuleCat.{u + 1} B) f).map (scalarExtensionRepresentative φ W P) ≫
          scalarGeometricRepresentative B f
            (((ProEtale.etaleSheafExtendScalars φ W).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map ((scalarSheafPullbackComplexIso φ f).hom.app P) := by
  obtain ⟨c, hc⟩ := scalarPullbackIso_exists φ f
  refine ⟨c, hc, ?_⟩
  intro d hd
  exact (scalarPullbackIso_unique φ f (c := c) (d := d) hc hd).symm

/-- The uniquely normalized derived scalar/pullback isomorphism. -/
def scalarPullbackIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    scalarExtension φ W ⋙ L(upperStar (ModuleCat.{u + 1} B) f) ≅
      L(upperStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ Z :=
  (scalarPullbackIso_existsUnique φ f).choose

/-- The B-linear scalar-change mate; its components are precisely the transposes
of the scalar extension of the A-geometric counit after scalarPullbackIso. -/
def scalarMate
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W) :
    R(lowerStar (ModuleCat.{u + 1} A) f) ⋙ scalarExtension φ W ⟶
      scalarExtension φ Z ⋙ R(lowerStar (ModuleCat.{u + 1} B) f) :=
  (mateEquiv (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} B) f)
    (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom))

private theorem scalar_tensor_pullback_square
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
    restricted_tensor_comparison (scalarPullbackIso φ f).hom
      (scalarRestrictionPullbackIso φ f).hom (scalarTensorIso φ Z).hom
  let β : (SW ⋙ UW) ⋙ FA ⟶ FA ⋙ TZ :=
    Functor.whiskerRight (scalarTensorIso φ W).hom FA ≫
      (derivedTensorRightCompLeftDerivedUpperStarIso
        (ModuleCat.{u + 1} A) f (scalarCoefficient φ W)).hom ≫
      Functor.whiskerLeft FA
        ((derivedTensor (ModuleCat.{u + 1} A) Z).flip.map
          (scalarCoefficientPullbackIso φ f).hom)
  have h : α = β := by
    apply scalar_natTrans_ext W
    intro P hP
    have hc := (scalarPullbackIso_existsUnique φ f).choose_spec.1 P hP
    have hm := scalarTensorPullback_normalization_kFlat φ f P hP
      ((scalarPullbackIso φ f).hom.app (_root_.DerivedCategory.Q.obj P))
      hc
    simpa only [α, β, restricted_tensor_comparison, FA, SW, UW, TZ,
      Functor.comp_obj,
      Functor.comp_map, Functor.map_id, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc,
      derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
      leftDerivedUpperStarTensorIso_hom, Functor.flip_map_app] using hm
  have hC := NatTrans.congr_app h C
  simpa only [α, β, restricted_tensor_comparison, FA, SW, UW, TZ,
      Functor.comp_obj,
      Functor.comp_map, Functor.map_id, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc,
    derivedTensorRightCompLeftDerivedUpperStarIso, NatIso.ofComponents_hom_app,
    leftDerivedUpperStarTensorIso_hom, Functor.flip_map_app] using hC

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- After canonical scalar/tensor and restriction/direct-image identifications,
the coefficient mate is the specified projection morphism, naturally in J. -/
theorem scalarMate_restrict_eq_projection
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {Z W : Scheme.{u}} (f : Z ⟶ W)
    (J : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (_hN : ∃ N : _root_.DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} B)),
      N.obj = (scalarExtension φ Z).obj J.obj)
    (_hM : ∃ M : _root_.DerivedCategory.Plus
      (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} B)),
      M.obj = (scalarExtension φ W).obj
        (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj)) :
    (Sheaf.derivedRestrictScalars W.smallEtaleTopology φ).map
        ((scalarMate φ f).app J.obj) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ Z).obj J.obj) =
      (scalarTensorIso φ W).hom.app (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J.obj).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map
          (((derivedTensor (ModuleCat.{u + 1} A) Z).obj J.obj).map
              (scalarCoefficientPullbackIso φ f).hom ≫
            (scalarTensorIso φ Z).inv.app J.obj) := by
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f
  let T := derivedTensor (ModuleCat.{u + 1} A) Z
  let b := (scalarCoefficientPullbackIso φ f).hom
  have ht := (T.map (adj.counit.app J.obj)).naturality b
  dsimp only [Functor.comp_obj, Functor.id_obj] at ht
  have hp : adj.homEquiv _ _
      (((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} A) f).app
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj)).app
          (scalarCoefficient φ W) ≫
        (T.obj (L(upperStar (ModuleCat.{u + 1} A) f).obj
          (R(lowerStar (ModuleCat.{u + 1} A) f).obj J.obj))).map b ≫
        (T.flip.obj (scalarCoefficient φ Z)).map (adj.counit.app J.obj)) =
      ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app J.obj).app
          (scalarCoefficient φ W) ≫
        R(lowerStar (ModuleCat.{u + 1} A) f).map ((T.obj J.obj).map b) := by
    simp only [Functor.flip_obj_map, Functor.id_obj]
    rw [ht, ← Category.assoc, adj.homEquiv_naturality_right]
    rfl
  have hm := restricted_mate_tensor adj
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
    (scalar_tensor_pullback_square φ f) J.obj
  simp only [Functor.flip_obj_obj, Functor.flip_obj_map, Functor.id_obj,
    Category.assoc] at hp hm
  rw [hp] at hm
  simpa only [scalarMate, scalarRestrictionDirectImageMap, adj, T, b,
    TwoSquare.mk, Functor.map_comp,
    Category.assoc] using hm

end AlgebraicGeometry.Etale

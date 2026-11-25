/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData

/-! # Tensor compatibility of the scalar/open restriction comparison

Source: Stacks Project, sites-modules.tex, Tags 03EL and 0E8J;
sites-cohomology.tex, Tags 06YY and 07A4.
(blueprint: lem-coef-etale-open-scalar-restriction-tensor).
-/

@[expose] public section
set_option autoImplicit false
universe u
open scoped CategoryTheory.Functor CategoryTheory.Prod
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Etale

private theorem rotate_square
    {C : Type*} [Category C] {V₁ V₂ V₃ V₄ V₅ V₆ : C}
    (a : V₁ ≅ V₂) (b : V₂ ≅ V₃) (t : V₃ ≅ V₄)
    (d : V₁ ≅ V₅) (e : V₅ ≅ V₆) (f : V₆ ≅ V₄)
    (h : a.hom ≫ b.hom ≫ t.hom = d.hom ≫ e.hom ≫ f.hom) :
    b.inv ≫ a.inv ≫ d.hom = t.hom ≫ f.inv ≫ e.inv := by
  apply (cancel_mono (e.hom ≫ f.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [← h]
  simp only [Iso.inv_hom_id_assoc]

private def transported_tensor
    {C D : Type*} [Category C] [Category D]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    {G₀ G : C ⥤ D} (e : G₀ ≅ G)
    (d : T ⋙ G₀ ≅ G₀.prod G₀ ⋙ S) :
    G.prod G ⋙ S ≅ T ⋙ G :=
  Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) S ≪≫ d.symm ≪≫
    Functor.isoWhiskerLeft T e

private def transported_comparison
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (L : C ⥤ E) (R : D ⥤ F) {G₀ G : C ⥤ D} {H₀ H : E ⥤ F}
    (e : G₀ ≅ G) (f : H₀ ≅ H) (c : L ⋙ H₀ ≅ G₀ ⋙ R) :
    G ⋙ R ≅ L ⋙ H :=
  Functor.isoWhiskerRight e.symm R ≪≫ c.symm ≪≫ Functor.isoWhiskerLeft L f

private theorem transport_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (V : E × E ⥤ E) (W : F × F ⥤ F)
    (L : C ⥤ E) (R : D ⥤ F) {G₀ G : C ⥤ D} {H₀ H : E ⥤ F}
    (e : G₀ ≅ G) (f : H₀ ≅ H) (c : L ⋙ H₀ ≅ G₀ ⋙ R)
    (dG : T ⋙ G₀ ≅ G₀.prod G₀ ⋙ S)
    (dH : V ⋙ H₀ ≅ H₀.prod H₀ ⋙ W)
    (tL : T ⋙ L ≅ L.prod L ⋙ V) (tR : S ⋙ R ≅ R.prod R ⋙ W)
    (K M : C)
    (h : c.hom.app (T.obj (K, M)) ≫ R.map (dG.hom.app (K, M)) ≫
        tR.hom.app (G₀.obj K, G₀.obj M) =
      H₀.map (tL.hom.app (K, M)) ≫ dH.hom.app (L.obj K, L.obj M) ≫
        W.map (c.hom.app K ×ₘ c.hom.app M)) :
    R.map ((transported_tensor T S e dG).hom.app (K, M)) ≫
        (transported_comparison L R e f c).hom.app (T.obj (K, M)) ≫
        H.map (tL.hom.app (K, M)) =
      tR.hom.app (G.obj K, G.obj M) ≫
        W.map ((transported_comparison L R e f c).hom.app K ×ₘ
          (transported_comparison L R e f c).hom.app M) ≫
        (transported_tensor V W f dH).hom.app (L.obj K, L.obj M) := by
  have h₀ := rotate_square (c.app (T.obj (K, M))) (R.mapIso (dG.app (K, M)))
    (tR.app (G₀.obj K, G₀.obj M)) (H₀.mapIso (tL.app (K, M)))
    (dH.app (L.obj K, L.obj M)) (W.mapIso ((c.app K).prod (c.app M))) h
  dsimp only [transported_tensor, transported_comparison, Iso.trans_hom,
    Iso.symm_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatIso.prod_hom, NatTrans.prod, Functor.mapIso_hom, Functor.mapIso_inv,
    Iso.app_hom, Iso.app_inv, Iso.prod_hom, Iso.prod_inv] at *
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (e.hom.app (T.obj (K, M)))
    (e.inv.app (T.obj (K, M))), Iso.hom_inv_id_app, R.map_id, Category.id_comp]
  dsimp only [Iso.prod, Iso.app] at h₀
  rw [← f.hom.naturality, reassoc_of% h₀]
  have ht := tR.hom.naturality (e.inv.app K ×ₘ e.inv.app M)
  dsimp only [Functor.comp_map, Functor.prod_map] at ht
  rw [reassoc_of% ht]
  simp only [← W.map_comp_assoc]
  congr 2
  apply congrArg W.map
  ext <;> dsimp <;> simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

private theorem cancel_square_transport
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (R : C ⥤ D) (S : E ⥤ F) {G G' : D ⥤ F} {H H' : C ⥤ E}
    (e : G ≅ G') (f : H ≅ H') (y : R ⋙ G' ⟶ H' ⋙ S) :
    Functor.whiskerLeft R e.inv ≫
      (Functor.whiskerLeft R e.hom ≫ y ≫ Functor.whiskerRight f.inv S) ≫
        Functor.whiskerRight f.hom S = y := by
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app]
  rw [CategoryTheory.Functor.map_id]
  simpa only [Functor.comp_obj] using Category.comp_id (y.app M)

private theorem restriction_map_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openScalarRestriction φ j).hom =
      Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).inv
          (scalarExtension φ U) ≫
        ProEtale.scalarPullbackReverseEtale φ j ≫
        Functor.whiskerLeft (scalarExtension φ X)
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom := by
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  have hd := derived_square_symm φ j he
  unfold openScalarRestriction
  change openScalarRestrictionMap φ j = _
  unfold openScalarRestrictionMap openDerivedRestrictScalarsIso
  rw [hd]
  let a := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let b := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)
  let x := TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ j).hom
  let e := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j
  let e' := leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j
  have h := inverse_mate_transport a b x e e'
  have heq : TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom =
      TwoSquare.mk _ _ _ _
        (Functor.whiskerLeft (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
          e.inv ≫
          x ≫ Functor.whiskerRight
            e'.hom
            (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ)) := by
    refine NatTrans.ext (funext fun M ↦ ?_)
    simpa only [x, scalarRestrictionPullbackIso, Iso.trans_hom,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] using NatTrans.congr_app (cancel_square_transport
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars U.smallEtaleTopology φ) e e'
      (Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)).hom).symm M
  rw [← heq] at h
  simpa only [a, b, e, e', x, ProEtale.scalarPullbackReverseEtale,
    scalarExtension, ProEtale.pbcFixedScalarExtension] using h

private theorem scalar_tensor_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (K M : DerivedCategoryModule A X) :
    (ExceptionalCoefficients.tensorIso φ X).hom.app (K, M) =
      (etaleHomTensorComparison X φ K M).inv := by
  let δ := ExceptionalCoefficients.tensorIso φ X
  have he : δ = (ExceptionalCoefficients.tensorIso_existsUnique φ X).choose :=
    eq_of_heq (ExceptionalCoefficients.siteTensorIso_existsUnique φ X).choose_spec.1
  have hn := (ExceptionalCoefficients.tensorIso_existsUnique φ X).choose_spec.1
  rw [← he] at hn
  have hc : IsEtaleHomTensorCanonical X φ (fun K M ↦ (δ.app (K, M)).symm) := by
    refine ⟨ExceptionalCoefficients.productIso_natural₁ _ _ _ δ,
      ExceptionalCoefficients.productIso_natural₂ _ _ _ δ, ?_⟩
    exact ExceptionalCoefficients.site_normalization_flat (ModuleCat.{u + 1} A)
      (ModuleCat.{u + 1} B) X (ProEtale.etaleSheafExtendScalars φ X)
      (scalarExtension φ X) (scalarExtensionRepresentative φ X) δ hn
  have h := (etaleHomTensorComparison_existsUnique X φ).unique hc
    (etaleHomTensorComparison_existsUnique X φ).choose_spec.1
  exact congrArg Iso.inv (congrFun (congrFun h K) M)

private noncomputable def restriction_tensor_product
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    Functor.uncurry.obj (derivedTensor C X) ⋙ L(upperStar C j) ≅
      L(upperStar C j).prod L(upperStar C j) ⋙ Functor.uncurry.obj (derivedTensor C U) :=
  NatIso.ofComponents
    (fun p ↦ leftDerivedUpperStarTensorIso C j p.1 p.2)
    (fun h ↦ (ExceptionalCoefficients.productOplaxTensorator
      (derivedTensor C X) (derivedTensor C U) L(upperStar C j)
      (leftDerivedUpperStarTensorComparison C j)).naturality h)

private theorem exact_tensor_eq
    (C : Type*) [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C] [UpperStarPreservesFlat C]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K M : _root_.DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (openExactRestrictionTensor C j K M).hom =
      (transported_tensor (Functor.uncurry.obj (derivedTensor C X))
        (Functor.uncurry.obj (derivedTensor C U))
        (leftDerivedUpperStarIsoMapDerivedCategory C j)
        (restriction_tensor_product C j)).hom.app (K, M) := by
  dsimp [openExactRestrictionTensor, transported_tensor, restriction_tensor_product,
    mapDerivedCategoryUpperStarDerivedTensorIso]
  rw [← ((derivedTensor C U).map
    ((leftDerivedUpperStarIsoMapDerivedCategory C j).inv.app K)).naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory C j).inv.app M)]
  simp only [Category.assoc]
  rfl

private theorem restriction_comparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    openScalarRestriction φ j =
      transported_comparison (scalarExtension φ X) (scalarExtension φ U)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j)
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j)
        (scalarPullbackIso φ j) := by
  have h : ProEtale.scalarPullbackReverseEtale φ j = (scalarPullbackIso φ j).inv := by
    have he := congrArg Iso.inv (scalarPullback_eq φ j)
    simpa only [ProEtale.scalarPullbackEtaleIsoFromMate, Iso.symm_inv, asIso_hom] using he
  apply Iso.ext
  rw [restriction_map_transport, h]
  rfl

/-- The fixed scalar/restriction mate respects the normalized binary tensor comparisons.
Source: the restriction/tensor portion of the proof of
`lem-coef-etale-open-mixed-tensor-scalar`; Stacks Tags 03EL, 0E8J, 06YY and 07A4.

Proof: ordinary restriction of coefficients commutes sectionwise with the direct
image from the open slice site. The identity comparison is monoidal for the lax
coefficient and direct-image tensorators: both composites act on local tensors
by the same balancing map. Conjugating under scalar and geometric adjunctions
therefore makes the ordinary scalar/restriction comparison monoidal for the
canonical oplax structures. The inverse of this comparison is r-zero of the
fixed open comparison data, since both are the left-adjoint comparison for the
same sectionwise identity.

Apply this ordinary equation to each bidegree of two flat K-flat resolutions.
Restriction is exact and preserves flat objects and integer-indexed colimits,
so these resolutions can also compute the derived restriction tensorators.
Ordinary scalar extension takes these resolving complexes to flat K-flat
complexes over the new ring. The scalar representative maps and localization
tensorators on these models are invertible. The scalar-adjunction definition
of r transposes to the localized ordinary scalar unit, so its representative
normalization is exactly the degreewise ordinary scalar/restriction comparison.
The defining normalization of t identifies its inverse with the localized
ordinary oplax tensorator. Substitute these normalizations into the totalized
ordinary monoidality equation and cancel the representative isomorphisms.
This yields the displayed equation on resolving representatives. Naturality
in each argument and the existence of such representatives yield it for all
unbounded K and M. Each map preserves bidegrees, so the signed totalization
introduces no extra sign. Nothing requires a flat coefficient map, a nonempty
open, or a nonzero coefficient ring.
(blueprint: lem-coef-etale-open-scalar-restriction-tensor). -/
theorem etaleOpenScalarRestrictionTensor
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (K M : DerivedCategoryModule A X) :
    (scalarExtension φ U).map
        (openExactRestrictionTensor (ModuleCat.{u + 1} A) j K M).hom ≫
      (openScalarRestriction φ j).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K).obj M) ≫
      (derivedRestriction (A := B) j).map (etaleHomTensorComparison X φ K M).inv =
    (etaleHomTensorComparison U φ
        ((derivedRestriction (A := A) j).obj K)
        ((derivedRestriction (A := A) j).obj M)).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} B) U).map
        ((openScalarRestriction φ j).hom.app K)).app
          ((scalarExtension φ U).obj ((derivedRestriction (A := A) j).obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) U).obj
        ((derivedRestriction (A := B) j).obj ((scalarExtension φ X).obj K))).map
          ((openScalarRestriction φ j).hom.app M) ≫
      (openExactRestrictionTensor (ModuleCat.{u + 1} B) j
        ((scalarExtension φ X).obj K) ((scalarExtension φ X).obj M)).hom := by
  have h := transport_square
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) X))
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} A) U))
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) X))
    (Functor.uncurry.obj (derivedTensor (ModuleCat.{u + 1} B) U))
    (scalarExtension φ X) (scalarExtension φ U)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j)
    (scalarPullbackIso φ j)
    (restriction_tensor_product (ModuleCat.{u + 1} A) j)
    (restriction_tensor_product (ModuleCat.{u + 1} B) j)
    (ExceptionalCoefficients.tensorIso φ X) (ExceptionalCoefficients.tensorIso φ U)
    K M ((etaleScalarPullback_tensor φ j) K M)
  simpa only [← exact_tensor_eq, ← restriction_comparison_eq, scalar_tensor_eq,
    Functor.uncurry_obj_map, Functor.uncurry_obj_obj, Functor.prod_obj,
    Functor.comp_obj, Category.assoc] using h

end AlgebraicGeometry.Etale

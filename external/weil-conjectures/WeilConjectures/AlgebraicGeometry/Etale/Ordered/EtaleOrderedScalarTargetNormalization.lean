/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs
public import WeilConjectures.AlgebraicGeometry.Etale.Hom.EtaleHomComparisonModels
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenScalarRestrictionTensor
import WeilConjectures.AlgebraicGeometry.Derived.DerivedTensorSymmetryInvolutive
import WeilConjectures.AlgebraicGeometry.Etale.EtaleNormalizedScalarSymmetry
import all WeilConjectures.AlgebraicGeometry.Etale.Open.EtaleOpenTensorDefs

/-! # Normalization of one side of the ordered scalar projection square -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] HasDerivedCategory.ofHasKInjectiveResolutions
  HasDerivedCategory.standard Functor.leftAdjoint Functor.rightAdjoint
  Functor.leftDerivedFunctor Functor.mapDerivedCategory upperStar openImmersionLowerShriek
  derivedTensor derivedTensorSymmetry derivedOpenImmersionLowerShriekProjectionIso
  ExceptionalCoefficients.tensorIso ExceptionalCoefficients.openIso
  leftDerivedUpperStarIsoMapDerivedCategory

private theorem open_comparison_eq
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ExceptionalCoefficients.openIso φ j = openScalarExtension φ j := by
  have he : (openRestrictScalarsIso φ j).symm = upperStarRestrictScalarsIsoSheaf φ j :=
    Iso.ext (openRestrictScalarsIso_inv_eq φ j)
  apply Iso.ext
  ext P
  simp [ExceptionalCoefficients.openIso, openScalarExtension, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv, conjugateEquiv_symm_apply_app, scalarRestrictionPullbackIso,
    openDerivedRestrictScalarsIso, ← he]
  rfl

private theorem open_transport_cancel
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    (J : C ⥤ E) (K : D ⥤ F) (S : E ⥤ F) (R : C ⥤ D)
    (q : J ⋙ S ≅ R ⋙ K) {U V W : C} {A B : E}
    (a : A ⟶ B) (p : B ⟶ J.obj U) (s : U ⟶ V) (e : U ⟶ W)
    (γ : J.obj W ⟶ B) (t : K.obj (R.obj V) ⟶ K.obj (R.obj W))
    (ht : K.map (R.map s) ≫ t = K.map (R.map e))
    (hp : p ≫ J.map e ≫ γ = 𝟙 B) :
    S.map (a ≫ p ≫ J.map s) ≫ q.hom.app V ≫ t ≫ q.inv.app W ≫ S.map γ =
      S.map a := by
  simp only [Functor.map_comp, Category.assoc]
  have hq := q.hom.naturality s
  dsimp only [Functor.comp_map] at hq
  rw [reassoc_of% hq]
  rw [reassoc_of% ht]
  have hqe := q.hom.naturality e
  dsimp only [Functor.comp_map] at hqe
  rw [← reassoc_of% hqe]
  simp only [Iso.hom_inv_id_app_assoc]
  have hp' := congrArg S.map hp
  simp only [Functor.map_comp, S.map_id] at hp'
  rw [hp', Category.comp_id]

private theorem tensor_transport_cancel
    {C D : Type*} [Category C] [Category D]
    (T : C ⥤ C ⥤ C) (U : D ⥤ D ⥤ D)
    (χ : T ≅ T.flip) (ψ : U ≅ U.flip) (F : C ⥤ D)
    (μ : ∀ K L : C, (U.obj (F.obj K)).obj (F.obj L) ≅ F.obj ((T.obj K).obj L))
    (M N N' : C) (P Q : D) (f : N ⟶ N')
    (a : F.obj N ⟶ P) (b : P ⟶ Q) (c : Q ⟶ F.obj N')
    (h : a ≫ b ≫ c = F.map f)
    (hb : F.map ((χ.hom.app M).app N) ≫ (μ N M).inv =
      (μ M N).inv ≫ (ψ.hom.app (F.obj M)).app (F.obj N))
    (hs : (ψ.hom.app (F.obj M)).app (F.obj N) ≫
      (ψ.hom.app (F.obj N)).app (F.obj M) = 𝟙 _)
    (hn : (U.obj (F.obj M)).map (F.map f) ≫ (μ M N').hom =
      (μ M N).hom ≫ F.map ((T.obj M).map f)) :
    F.map ((χ.hom.app M).app N) ≫ (μ N M).inv ≫ (U.map a).app (F.obj M) ≫
      (ψ.hom.app P).app (F.obj M) ≫ (U.obj (F.obj M)).map b ≫
      (U.obj (F.obj M)).map c ≫ (μ M N').hom = F.map ((T.obj M).map f) := by
  have hnat := congr_app (ψ.hom.naturality a) (F.obj M)
  change (U.map a).app (F.obj M) ≫ (ψ.hom.app P).app (F.obj M) =
    (ψ.hom.app (F.obj N)).app (F.obj M) ≫ (U.obj (F.obj M)).map a at hnat
  rw [← Category.assoc _ (μ N M).inv, hb]
  simp only [Category.assoc]
  rw [reassoc_of% hnat, reassoc_of% hs]
  have hh := congrArg
    (fun z ↦ (μ M N).inv ≫ (U.obj (F.obj M)).map z ≫ (μ M N').hom) h
  simp only [Functor.map_comp, Category.assoc] at hh
  rw [hh, hn, Iso.inv_hom_id_assoc]

private theorem scalar_braiding
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    (X : Scheme.{u}) (K L : DerivedCategoryModule A X) :
    (scalarExtension φ X).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app K).app L) ≫
      (etaleHomTensorComparison X φ L K).inv =
    (etaleHomTensorComparison X φ K L).inv ≫
      (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
        ((scalarExtension φ X).obj K)).app ((scalarExtension φ X).obj L)) := by
  apply (cancel_epi (etaleHomTensorComparison X φ K L).hom).1
  rw [Iso.hom_inv_id_assoc]
  apply (cancel_mono (etaleHomTensorComparison X φ L K).hom).1
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact (etaleNormalizedScalarSymmetry φ X K L).symm

private theorem local_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule A Z) (M : DerivedCategoryModule A X) :
    (scalarExtension φ X).map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).app
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T)) ≫
      (ExceptionalCoefficients.tensorIso φ X).hom.app
        ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T, M) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).map
        ((scalarPullbackIso φ j).inv.app T)).app ((scalarExtension φ X).obj M) ≫
      (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
        ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
          ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
          ((scalarExtension φ Z).obj T)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((openScalarRestriction φ j).inv.app T) ≫
      (etaleHomTensorComparison X φ M ((derivedRestriction j).obj T)).hom =
    (scalarExtension φ X).map
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).hom.app T)) := by
  rw [scalar_tensor_eq]
  apply tensor_transport_cancel
    (derivedTensor (ModuleCat.{u + 1} A) X) (derivedTensor (ModuleCat.{u + 1} B) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} A) X)
    (derivedTensorSymmetry (ModuleCat.{u + 1} B) X)
    (scalarExtension φ X) (etaleHomTensorComparison X φ)
  · rw [restriction_comparison_eq]
    simp [transported_comparison]
  · exact scalar_braiding φ X M _
  · exact derivedTensorSymmetry_involutive B X _ _
  · exact (etaleHomTensorComparison_existsUnique X φ).choose_spec.1.2.1 M _

/-- Normalize the target-side scalar transport before applying the mixed equation.
Source: Stacks 0E8I, 0GL6 and 07A4; the target normalization in the local open square
(blueprint: lem-pur-ordered-scalar-target-normalization).

Proof: identify the inverse open comparison with openScalarExtension.inv by the
unit-transpose uniqueness of the open adjunction. Identify tensorIso with the inverse
of etaleHomTensorComparison by uniqueness of their flat K-flat normalization.
Transport scalarPullbackIso along the exact/left-derived pullback comparisons to
openScalarRestriction. Naturality moves the open comparison through the final
symmetry. On a flat K-flat pair, ordinary scalar balancing commutes with the signed
swap, since the coefficient scalar has degree zero. Descend that equality through
localization and extend it to all pairs by naturality of resolutions. The two signed
swaps cancel. The remaining exact-pullback comparisons cancel, and the inverse open
projection cancels canonicalGammaExact. The only surviving factor is the image of
the ambient inverse symmetry. All operations are invertible, so zero inputs, the
empty open and zero rings satisfy the same formula. -/
theorem etaleOrderedScalar_targetNormalization
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (T : DerivedCategoryModule A Z) (M : DerivedCategoryModule A X) :
    (((scalarExtension φ Z).map (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)).app
        T ≫
      ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).inv.app
        M).app T ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).app
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T))) ≫
      (ExceptionalCoefficients.openIso φ j).hom.app
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T)).obj M) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        ((ExceptionalCoefficients.tensorIso φ X).hom.app
            ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T, M) ≫
          ((derivedTensor (ModuleCat.{u + 1} B) X).map
            ((scalarPullbackIso φ j).inv.app T)).app ((scalarExtension φ X).obj M))) ≫
      (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M))) ≫
    ((openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
      (((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
          ((scalarExtension φ Z).obj T)))) ≫
    ((derivedExtension (A := B) j).map
          (((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
              ((openScalarRestriction φ j).inv.app T) ≫
            (etaleHomTensorComparison X φ M ((derivedRestriction j).obj T)).hom) ≫
        (openScalarExtension φ j).inv.app
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).obj
            ((derivedRestriction j).obj T)) ≫
        (scalarExtension φ Z).map (canonicalGammaExact (ModuleCat.{u + 1} A) j M T)) =
    (scalarExtension φ Z).map
      (((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).inv.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)).app T)
      := by
  rw [open_comparison_eq]
  let t₀ :=
    (ExceptionalCoefficients.tensorIso φ X).hom.app
          ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T, M) ≫
        ((derivedTensor (ModuleCat.{u + 1} B) X).map
          ((scalarPullbackIso φ j).inv.app T)).app ((scalarExtension φ X).obj M) ≫
      (((derivedTensorSymmetry (ModuleCat.{u + 1} B) X).hom.app
          ((upperStar (ModuleCat.{u + 1} B) j).leftDerivedFunctor.obj
            ((scalarExtension φ Z).obj T))).app ((scalarExtension φ X).obj M)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} B) j).hom.app
          ((scalarExtension φ Z).obj T)) ≫
      ((derivedTensor (ModuleCat.{u + 1} B) X).obj ((scalarExtension φ X).obj M)).map
        ((openScalarRestriction φ j).inv.app T) ≫
      (etaleHomTensorComparison X φ M ((derivedRestriction j).obj T)).hom
  have hcancel := open_transport_cancel
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
    (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory
    (scalarExtension φ Z) (scalarExtension φ X) (openScalarExtension φ j)
    (a := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) Z).inv.app
      ((openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M)).app T)
    (p := ((derivedOpenImmersionLowerShriekProjectionIso (ModuleCat.{u + 1} A) j).inv.app M).app T)
    (s := ((derivedTensorSymmetry (ModuleCat.{u + 1} A) X).hom.app M).app
      ((upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctor.obj T))
    (e := ((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) j).hom.app T))
    (γ := (canonicalGammaExact (ModuleCat.{u + 1} A) j M T))
    (t := (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map t₀)
    (by
      simpa [t₀, Functor.map_comp, Category.assoc] using congrArg
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory.map
        (local_transport φ j T M))
    (by
      let J := (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory
      have hproj : J.map
          (((derivedTensor (ModuleCat.{u + 1} A) X).obj M).map
            ((leftDerivedUpperStarIsoMapDerivedCategory
              (ModuleCat.{u + 1} A) j).hom.app T)) ≫
          canonicalGammaExact (ModuleCat.{u + 1} A) j M T =
          ((derivedOpenImmersionLowerShriekProjectionIso
            (ModuleCat.{u + 1} A) j).hom.app M).app T := by
        rw [canonicalGammaExact, ← J.map_comp_assoc,
          ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id_app,
          CategoryTheory.Functor.map_id, J.map_id, Category.id_comp,
          derivedOpenImmersionLowerShriekProjectionIso_hom]
      rw [hproj, Iso.inv_hom_id_app_app]
      rfl)
  simpa only [t₀, CategoryTheory.Functor.map_comp, Category.assoc, Functor.flip_obj_obj,
    derivedExtension, derivedRestriction] using hcancel

end AlgebraicGeometry.Etale

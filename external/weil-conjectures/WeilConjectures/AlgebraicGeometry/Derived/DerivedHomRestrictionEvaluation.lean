/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Derived.DerivedRestrictionHomPresheaf
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars

/-! # Evaluation commutes with restriction of derived Hom coefficients

Source: Stacks Project, Tags 03DA, 098K and 0F63.
(blueprint: lem-weil-pbc-derived-hom-restriction-evaluation).
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
section Conjugation
variable {P Q R S : Type*} [Category P] [Category Q] [Category R] [Category S]
    (SV : P ⥤ Q) (SW : R ⥤ S) (M : R ⥤ P) (L : S ⥤ Q)
    {Av Dv : P} {Aw Dw : R} {Aq Dq : Q} {As Ds : S}
    (δA : SV.obj Av ≅ Aq) (δD : SV.obj Dv ≅ Dq)
    (εA : SW.obj Aw ≅ As) (εD : SW.obj Dw ≅ Ds)
    (σA : Av ≅ M.obj Aw) (σD : Dv ≅ M.obj Dw)
    (cA : Aq ≅ L.obj As) (cD : Dq ≅ L.obj Ds)
    (α : M ⋙ SV ≅ SW ⋙ L)
    (hA : δA.hom ≫ cA.hom = SV.map σA.hom ≫ α.hom.app Aw ≫ L.map εA.hom)
    (hD : δD.hom ≫ cD.hom = SV.map σD.hom ≫ α.hom.app Dw ≫ L.map εD.hom)
include hA hD in
private theorem conjugation_hom_natural (e : Aw ⟶ Dw) :
    δA.inv ≫ SV.map (σA.hom ≫ M.map e ≫ σD.inv) ≫ δD.hom =
      cA.hom ≫ L.map (εA.inv ≫ SW.map e ≫ εD.hom) ≫ cD.inv := by
  apply (cancel_epi δA.hom).mp
  apply (cancel_mono cD.hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id]
  rw [hD]
  simp only [← SV.map_comp_assoc, Iso.inv_hom_id, SV.map_id, Category.id_comp]
  rw [SV.map_comp, Category.assoc]
  have hn := α.hom.naturality e
  change SV.map (M.map e) ≫ α.hom.app Dw =
    α.hom.app Aw ≫ L.map (SW.map e) at hn
  rw [reassoc_of% hn]
  rw [reassoc_of% hA]
  simp only [← L.map_comp_assoc, Iso.hom_inv_id, L.map_id, Category.id_comp,
    Category.comp_id, Iso.hom_inv_id_assoc]
end Conjugation

private theorem derived_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [Abelian A'] [Abelian B'] [Abelian C'] [Abelian D']
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D] [HasDerivedCategory A'] [HasDerivedCategory B']
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (U : A' ⥤ A) (V : B' ⥤ B) (W : C' ⥤ C) (Z : D' ⥤ D)
    (r : A ⥤ B) (r' : A' ⥤ B') (s : C ⥤ D) (s' : C' ⥤ D')
    (H : A ⥤ C) (H' : A' ⥤ C') (K : B ⥤ D) (K' : B' ⥤ D')
    [U.Additive] [V.Additive] [W.Additive] [Z.Additive]
    [r.Additive] [r'.Additive] [s.Additive] [s'.Additive]
    [H.Additive] [H'.Additive] [K.Additive] [K'.Additive]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    [PreservesFiniteLimits Z] [PreservesFiniteColimits Z]
    [PreservesFiniteLimits r] [PreservesFiniteColimits r]
    [PreservesFiniteLimits r'] [PreservesFiniteColimits r']
    [PreservesFiniteLimits s] [PreservesFiniteColimits s]
    [PreservesFiniteLimits s'] [PreservesFiniteColimits s']
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits H'] [PreservesFiniteColimits H']
    [PreservesFiniteLimits K] [PreservesFiniteColimits K]
    [PreservesFiniteLimits K'] [PreservesFiniteColimits K']
    (t : U ⋙ r ≅ r' ⋙ V) (k : V ⋙ K ≅ K' ⋙ Z)
    (c : U ⋙ H ≅ H' ⋙ W) (q : W ⋙ s ≅ s' ⋙ Z)
    (b : r ⋙ K ≅ H ⋙ s) (b' : r' ⋙ K' ≅ H' ⋙ s')
    (h : ∀ x, K.map (t.hom.app x) ≫ k.hom.app (r'.obj x) ≫ Z.map (b'.hom.app x) =
      b.hom.app (U.obj x) ≫ s.map (c.hom.app x) ≫ q.hom.app (H'.obj x))
    (x : DerivedCategory A') :
    K.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso t).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso k).hom.app (r'.mapDerivedCategory.obj x) ≫
        Z.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso b').hom.app x) =
      (Functor.mapDerivedCategorySquareIso b).hom.app (U.mapDerivedCategory.obj x) ≫
        s.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso c).hom.app x) ≫
        (Functor.mapDerivedCategorySquareIso q).hom.app (H'.mapDerivedCategory.obj x) := by
  let a : U ⋙ (r ⋙ K) ≅ (r' ⋙ K') ⋙ Z :=
    Functor.isoWhiskerRight t K ≪≫ Functor.isoWhiskerLeft r' k
  have h₁ := Functor.mapDerivedCategorySquareIso_hom_app_comp t k a
    (Iso.refl (r ⋙ K)) (Iso.refl (r' ⋙ K')) (fun y ↦ by simp [a]) x
  have h₂ := Functor.mapDerivedCategorySquareIso_hom_app_comp c q a b b'
    (fun y ↦ by simpa [a] using h y) x
  simp only [Functor.mapDerivedCategoryTriangleIso, Functor.mapDerivedCategoryNatIso_refl,
    Iso.trans_hom, Iso.symm_hom, Iso.refl_hom, NatTrans.comp_app,
    NatTrans.id_app, Category.comp_id, CategoryTheory.Functor.map_comp,
    Category.assoc, CategoryTheory.Functor.map_id, Category.id_comp] at h₁ h₂
  rw [← cancel_epi ((Functor.mapDerivedCategoryCompIso r K).inv.app
    (U.mapDerivedCategory.obj x))]
  rw [← cancel_mono (Z.mapDerivedCategory.map
    ((Functor.mapDerivedCategoryCompIso H' s').hom.app x))]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc]
  simp only [Iso.inv_hom_id_app_assoc]
  rw [← reassoc_of% h₁, ← reassoc_of% h₂]
  simp only [← Z.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Iso.inv_hom_id_app_assoc]

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private noncomputable def comparisonSliceCoefficients (V : X.Etale) (q : R →+* S) :=
  normalizationPullbackIso (X.smallEtaleTopology.over V) (Over.post (toProEt X))
    ((ProEt.topology X).over ((toProEt X).obj V)) q

private theorem comparisonSliceCoefficients_eq (V : X.Etale) (q : R →+* S)
    (M : Sheaf (X.smallEtaleTopology.over V) (ModuleCat.{u + 1} S)) :
    (comparisonSliceCoefficients X V q).hom.app M =
      ((comparisonSliceAdjunction X R V).homEquiv _ _).symm
        ((Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
          ((comparisonSliceAdjunction X S V).unit.app M)) := by
  simp only [comparisonSliceCoefficients, normalizationPullbackIso, asIso_hom,
    normalizationPullbackMate, mateEquiv_symm_apply, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Adjunction.homEquiv_counit]
  dsimp only [Functor.comp_obj, Functor.comp_map]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  rfl

private theorem comparison_coefficients_cube (V : X.Etale) (q : R →+* S)
    (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)) :
    (comparisonSliceCoefficients X V q).hom.app (M.over V) ≫
      (Sheaf.restrictScalars ((ProEt.topology X).over ((toProEt X).obj V)) q).map
        ((comparisonSliceBaseIso X S V).hom.app M) =
    (comparisonSliceBaseIso X R V).hom.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      ((ProEt.topology X).overPullback (ModuleCat.{u + 1} R)
        ((toProEt X).obj V)).map
        ((comparisonRestrictScalarsSheafIso X R q).hom.app M) := by
  have hS := ((comparisonSliceAdjunction X S V).homEquiv (M.over V)
    (((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).obj M).over
      ((toProEt X).obj V))).apply_symm_apply
    ((X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} S) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X).unit.app M))
  have hR := ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).homEquiv
    ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M)
    ((Sheaf.restrictScalars (ProEt.topology X) q).obj
      ((ProEtale.comparisonUpperStar (ModuleCat.{u + 1} S) X).obj M))).apply_symm_apply
    ((Sheaf.restrictScalars X.smallEtaleTopology q).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} S) X).unit.app M))
  rw [Adjunction.homEquiv_unit] at hS hR
  apply ((comparisonSliceAdjunction X R V).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, comparisonSliceCoefficients_eq,
    Equiv.apply_symm_apply]
  simp only [comparisonSliceBaseIso, NatIso.ofComponents_hom_app, asIso_hom]
  rw [Adjunction.homEquiv_naturality_right]
  erw [comparisonSliceBaseMap, Equiv.apply_symm_apply]
  change
    (Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
      ((comparisonSliceAdjunction X S V).unit.app (M.over V)) ≫
      (Sheaf.restrictScalars (X.smallEtaleTopology.over V) q).map
        (((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} S)
          (X.smallEtaleTopology.over V)
          ((ProEt.topology X).over ((toProEt X).obj V))).map
          (comparisonSliceBaseMap X S V M)) =
    (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
      ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
        ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M)) ≫
      (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
        ((ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
          (comparisonRestrictScalarsMap X R q M))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  change _ = (X.smallEtaleTopology.overPullback (ModuleCat.{u + 1} R) V).map
    ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        (comparisonRestrictScalarsMap X R q M))
  rw [show (comparisonSliceAdjunction X S V).unit.app (M.over V) ≫
      ((Over.post (toProEt X)).sheafPushforwardContinuous (ModuleCat.{u + 1} S)
        (X.smallEtaleTopology.over V)
        ((ProEt.topology X).over ((toProEt X).obj V))).map
        (comparisonSliceBaseMap X S V M) = _ from hS]
  rw [show (ProEtale.comparisonAdjunction (ModuleCat.{u + 1} R) X).unit.app
      ((Sheaf.restrictScalars X.smallEtaleTopology q).obj M) ≫
      (ProEtale.comparisonLowerStar (ModuleCat.{u + 1} R) X).map
        (comparisonRestrictScalarsMap X R q M) = _ from hR]
  rfl
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme
variable (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S]
private noncomputable def comparisonDerivedSliceCoefficients (V : X.Etale) (q : R →+* S) :=
  Functor.mapDerivedCategorySquareIso (comparisonSliceCoefficients X V q)

private theorem comparison_derived_coefficients_cube (V : X.Etale) (q : R →+* S)
    (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    (comparisonSliceUpperStar X R V).mapDerivedCategory.map
        ((sliceRestrictScalarsIso X.smallEtaleTopology R q V).inv.app M) ≫
      (comparisonDerivedSliceCoefficients X V q).hom.app
        ((derivedSliceRestriction X.smallEtaleTopology S V).obj M) ≫
      (Sheaf.derivedRestrictScalars ((ProEt.topology X).over ((toProEt X).obj V)) q).map
        ((derivedComparisonSliceIso X S V).hom.app M) =
    (derivedComparisonSliceIso X R V).hom.app
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology q).obj M) ≫
      (derivedSliceRestriction (ProEt.topology X) R ((toProEt X).obj V)).map
        ((comparisonRestrictScalarsIso X R q).hom.app M) ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q ((toProEt X).obj V)).inv.app
        ((derivedComparison X S).obj M) := by
  have h := derived_cube _ _ _ _ _ _ _ _ _ _ _ _
    (sliceRestrictScalarsSheafIso X.smallEtaleTopology R q V).symm
    (comparisonSliceCoefficients X V q) (comparisonRestrictScalarsSheafIso X R q)
    (sliceRestrictScalarsSheafIso (ProEt.topology X) R q ((toProEt X).obj V)).symm
    (comparisonSliceBaseIso X R V) (comparisonSliceBaseIso X S V)
    (fun N ↦ by
      dsimp only [sliceRestrictScalarsSheafIso, Iso.symm_hom,
        NatIso.ofComponents_inv_app, Iso.refl_inv]
      erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
      exact comparison_coefficients_cube X V q N) M
  simpa only [comparisonDerivedSliceCoefficients, sliceRestrictScalarsIso,
    comparisonRestrictScalarsIso, derivedComparisonSliceIso,
    Functor.mapDerivedCategorySquareIso, Functor.mapDerivedCategoryNatIso_symm,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, CategoryTheory.Functor.map_comp, Category.assoc] using h
end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme

private theorem comparisonLocalHom_restrict
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)))
    (V : X.Etale)
    (e : (derivedSliceRestriction X.smallEtaleTopology S V).obj A ⟶
      (derivedSliceRestriction X.smallEtaleTopology S V).obj D) :
    derivedComparisonLocalHom X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D) V
        ((derivedRestrictionHomPresheaf X.smallEtaleTopology q A D).app (op V) e) =
      (derivedLocalHomPresheafMap
        ((comparisonRestrictScalarsIso X R q).hom.app A)
        ((comparisonRestrictScalarsIso X R q).inv.app D)).app (op ((toProEt X).obj V))
        ((derivedRestrictionHomPresheaf (ProEt.topology X) q
          ((derivedComparison X S).obj A) ((derivedComparison X S).obj D)).app
            (op ((toProEt X).obj V)) (derivedComparisonLocalHom X S A D V e)) := by
  let W := (toProEt X).obj V
  let c (M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :=
    (derivedSliceRestriction (ProEt.topology X) R W).mapIso
        ((comparisonRestrictScalarsIso X R q).app M) ≪≫
      ((sliceRestrictScalarsIso (ProEt.topology X) R q W).app
        ((derivedComparison X S).obj M)).symm
  have h := conjugation_hom_natural
    (comparisonSliceUpperStar X R V).mapDerivedCategory
    (comparisonSliceUpperStar X S V).mapDerivedCategory
    (normalizationRestrict (X.smallEtaleTopology.over V) q)
    (normalizationRestrict ((ProEt.topology X).over W) q)
    ((derivedComparisonSliceIso X R V).app
      ((normalizationRestrict X.smallEtaleTopology q).obj A))
    ((derivedComparisonSliceIso X R V).app
      ((normalizationRestrict X.smallEtaleTopology q).obj D))
    ((derivedComparisonSliceIso X S V).app A)
    ((derivedComparisonSliceIso X S V).app D)
    ((sliceRestrictScalarsIso X.smallEtaleTopology R q V).app A).symm
    ((sliceRestrictScalarsIso X.smallEtaleTopology R q V).app D).symm
    (c A) (c D) (comparisonDerivedSliceCoefficients X V q)
    (comparison_derived_coefficients_cube X V q A).symm
    (comparison_derived_coefficients_cube X V q D).symm e
  simpa only [c, W, derivedComparisonLocalHom, derivedRestrictionHomPresheaf,
    derivedLocalHomPresheafMap, TypeCat.ofHom_apply, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Functor.map_comp, Category.assoc, Iso.app_hom, Iso.app_inv] using h

private theorem comparisonHom_restrict
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S))) :
    (comparisonSetUpperStar X).map
        ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
          (derivedRestrictionHomPresheaf X.smallEtaleTopology q A D)) ≫
      derivedHomSheafComparison X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D) =
    derivedHomSheafComparison X S A D ≫
      (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
        (derivedRestrictionHomPresheaf (ProEt.topology X) q
          ((derivedComparison X S).obj A) ((derivedComparison X S).obj D) ≫
          derivedLocalHomPresheafMap
            ((comparisonRestrictScalarsIso X R q).hom.app A)
            ((comparisonRestrictScalarsIso X R q).inv.app D)) := by
  let θ := (presheafToSheaf (ProEt.topology X) (Type (u + 1))).map
    (derivedRestrictionHomPresheaf (ProEt.topology X) q
      ((derivedComparison X S).obj A) ((derivedComparison X S).obj D) ≫
      derivedLocalHomPresheafMap
        ((comparisonRestrictScalarsIso X R q).hom.app A)
        ((comparisonRestrictScalarsIso X R q).inv.app D))
  let Rpush := (toProEt X).sheafPushforwardContinuous (Type (u + 1))
    X.smallEtaleTopology (ProEt.topology X)
  have hp : derivedRestrictionHomPresheaf X.smallEtaleTopology q A D ≫
      derivedComparisonHomPresheafMap X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D) =
      derivedComparisonHomPresheafMap X S A D ≫ (Rpush.map θ).hom := by
    ext V e
    have hn := toSheafify_naturality (ProEt.topology X)
      (derivedRestrictionHomPresheaf (ProEt.topology X) q
        ((derivedComparison X S).obj A) ((derivedComparison X S).obj D) ≫
        derivedLocalHomPresheafMap
          ((comparisonRestrictScalarsIso X R q).hom.app A)
          ((comparisonRestrictScalarsIso X R q).inv.app D))
    have hn' := ConcreteCategory.congr_hom
      (congr_app hn (op ((toProEt X).obj V.unop)))
      (derivedComparisonLocalHom X S A D V.unop e)
    exact (congrArg
      ((toSheafify (ProEt.topology X)
        (derivedLocalHomPresheaf (ProEt.topology X) R
          ((derivedComparison X R).obj
            ((normalizationRestrict X.smallEtaleTopology q).obj A))
          ((derivedComparison X R).obj
            ((normalizationRestrict X.smallEtaleTopology q).obj D)))).app
              (op ((toProEt X).obj V.unop)))
      (comparisonLocalHom_restrict X q A D V.unop e)).trans hn'
  have hs := Adjunction.homEquiv_naturality_right_square
    (sheafificationAdjunction X.smallEtaleTopology (Type (u + 1)))
    (derivedRestrictionHomPresheaf X.smallEtaleTopology q A D) _ _ (Rpush.map θ) hp
  exact (proEtaleSiteComparison X).homEquiv_naturality_right_square
    ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
      (derivedRestrictionHomPresheaf X.smallEtaleTopology q A D)) _ _ θ hs

/-- Evaluation of local derived morphisms commutes with coefficient restriction.
Source: Stacks Project, Tags 03DA and 098K (restriction of coefficients and localization),
and 0F63 (the inverse sheafification unit on weakly contractible affines).
(blueprint: lem-weil-pbc-derived-hom-restriction-evaluation).

Proof: Conjugate restriction of scalars on each localized derived category by
sliceRestrictScalarsIso. These conjugations form the specified Hom presheaf map.
The comparison inverse image commutes with them: on etale generators this is the
pasting identity for the coefficient-restriction mate and the comparison localization
isomorphism. Transpose this identity along sheafification and comparison adjunctions.
On the pro-etale site, naturality of the sheafification unit intertwines the same
conjugations. At U this unit is bijective, so cancel it. Expanding the resulting
conjugation and composing with its target coefficient isomorphism gives the square
below. This uses no finiteness, no perfectness, and no universal normalization arrow. -/
theorem derivedHomEvaluation_restrictScalars
    (X : Scheme.{u}) {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S)
    (A D : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} S)))
    (U : X.ProEt) [IsAffine U.left]
    (hw : (ProEt.topology X).IsWeaklyContractible.{u + 1} U)
    (s : ((comparisonSetUpperStar X).obj
      (derivedLocalHomSheaf X.smallEtaleTopology S A D)).obj.obj (op U)) :
    derivedHomEvaluation X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D) U hw
        (((comparisonSetUpperStar X).map
          ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
            (derivedRestrictionHomPresheaf X.smallEtaleTopology q A D))).hom.app
              (op U) s) ≫
      (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app D) ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app
        ((derivedComparison X S).obj D) =
    (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app A) ≫
      (sliceRestrictScalarsIso (ProEt.topology X) R q U).inv.app
        ((derivedComparison X S).obj A) ≫
      (normalizationRestrict ((ProEt.topology X).over U) q).map
        (derivedHomEvaluation X S A D U hw s) := by
  let j := derivedRestrictionHomPresheaf (ProEt.topology X) q
    ((derivedComparison X S).obj A) ((derivedComparison X S).obj D) ≫
      derivedLocalHomPresheafMap
        ((comparisonRestrictScalarsIso X R q).hom.app A)
        ((comparisonRestrictScalarsIso X R q).inv.app D)
  let sR := (((comparisonSetUpperStar X).map
    ((presheafToSheaf X.smallEtaleTopology (Type (u + 1))).map
      (derivedRestrictionHomPresheaf X.smallEtaleTopology q A D))).hom.app (op U) s)
  have h : derivedHomEvaluation X R
      ((normalizationRestrict X.smallEtaleTopology q).obj A)
      ((normalizationRestrict X.smallEtaleTopology q).obj D) U hw sR =
      j.app (op U) (derivedHomEvaluation X S A D U hw s) := by
    apply (proEtaleDerivedUnits_bijective X R
      ((normalizationRestrict X.smallEtaleTopology q).obj A)
      ((normalizationRestrict X.smallEtaleTopology q).obj D) U hw).1.1
    have hc := congrArg (fun k ↦ k.hom.app (op U) s) (comparisonHom_restrict X q A D)
    have hu := (Equiv.ofBijective (proEtaleDerivedHomUnit X S A D U)
      (proEtaleDerivedUnits_bijective X S A D U hw).1).apply_symm_apply
      ((derivedHomSheafComparison X S A D).hom.app (op U) s)
    have hn := ConcreteCategory.congr_hom
      (congr_app (toSheafify_naturality (ProEt.topology X) j) (op U))
      (derivedHomEvaluation X S A D U hw s)
    exact (Equiv.ofBijective (proEtaleDerivedHomUnit X R
      ((normalizationRestrict X.smallEtaleTopology q).obj A)
      ((normalizationRestrict X.smallEtaleTopology q).obj D) U)
      (proEtaleDerivedUnits_bijective X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D) U hw).1).apply_symm_apply
      ((derivedHomSheafComparison X R
        ((normalizationRestrict X.smallEtaleTopology q).obj A)
        ((normalizationRestrict X.smallEtaleTopology q).obj D)).hom.app (op U) sR) |>.trans
      (hc.trans ((congrArg
        (((presheafToSheaf (ProEt.topology X) (Type (u + 1))).map j).hom.app (op U))
        hu.symm).trans hn.symm))
  change derivedHomEvaluation X R _ _ U hw sR ≫ _ = _
  rw [h]
  simp only [j, NatTrans.comp_app, ConcreteCategory.comp_apply,
    derivedRestrictionHomPresheaf, derivedLocalHomPresheafMap, TypeCat.ofHom_apply,
    Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.hom_inv_id_app]
  have hm : (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).inv.app D) ≫
      (derivedSliceRestriction (ProEt.topology X) R U).map
        ((comparisonRestrictScalarsIso X R q).hom.app D) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  simp only [reassoc_of% hm, Category.id_comp, Iso.hom_inv_id_app, Category.comp_id]
  erw [Category.comp_id]

end AlgebraicGeometry.Scheme

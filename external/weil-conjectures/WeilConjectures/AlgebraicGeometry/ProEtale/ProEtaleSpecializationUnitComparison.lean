/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale

public import WeilConjectures.AlgebraicGeometry.ProEtale.ClosedSiteLift
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch

import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedInverseImageEvaluation
import all WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import all WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import all WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import all Mathlib.AlgebraicGeometry.Sites.Proetale
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import all Mathlib.Algebra.Homology.ShortComplex.ShortExact
import all Mathlib.CategoryTheory.Sites.Sheafification
import all WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all Mathlib.CategoryTheory.Monoidal.Ring
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import all WeilConjectures.CategoryTheory.InverseMateEquivalence
import all WeilConjectures.AlgebraicGeometry.ProEtale.Replete
import all WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# The inverse-image unit on sections from an affine closed-site counit

## References

* Stacks Project, Tag 09BL, (2), and Tag 09AC, localization and unit identification

## Implementation details

The affine argument uses the sheafification helpers of `AffineClosedInverseImageEvaluation`.
The weakly etale comparison adapts the site calculation of
`WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale` to the finite-coefficient API,
avoiding its incompatible duplicate upper/lower-star imports.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

namespace AffineProEt

private theorem projectiveEvaluation_of_iso {S : Scheme.{u}} {B C : S.AffineProEt}
    (e : B ≅ C)
    (hB : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) :
    ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op C)) := by
  intro P Q φ hφ y
  obtain ⟨x, hx⟩ := hB P Q φ hφ (Q.obj.map e.hom.op y)
  refine ⟨P.obj.map e.inv.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp]
  simp

private theorem cover_split_of_cover {S : Scheme.{u}} [(topology S).Subcanonical]
    (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V)))
    {W : S.AffineProEt} (q : W ⟶ V)
    (hq : Sieve.generate (Presieve.singleton q) ∈ topology S V) :
    ∃ σ : V ⟶ W, σ ≫ q = 𝟙 V := by
  let J := topology S
  let H := J.uliftYoneda.{u + 1}
  have hepi : Epi (H.map q) := by
    constructor
    intro T a b hab
    apply J.uliftYonedaEquiv.injective
    have hsep := ((isSheaf_iff_isSheaf_of_type J T.obj).mp T.property).isSheafFor
      (Presieve.singleton q) hq |>.isSeparatedFor
    apply hsep.ext
    rintro Y f ⟨⟩
    rw [J.uliftYonedaEquiv_naturality, J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv hab
  obtain ⟨σ, hσ⟩ := hV _ _ (H.map q) hepi (ULift.up (𝟙 V))
  exact ⟨σ.down, congrArg ULift.down hσ⟩

set_option backward.isDefEq.respectTransparency false in
private theorem projectiveEvaluation_closedBaseChange
    (A : Type u) [CommRing A] (I : Ideal A)
    (B : (Spec (.of A)).AffineProEt)
    (hB : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B)))
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (hε : IsIso (adj.counit.app B)) :
    ∀ (P Q : Sheaf (topology (Spec (.of (A ⧸ I)))) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective
        (φ.hom.app (op ((closedSiteBaseChange A I).obj B))) := by
  obtain ⟨_, _, hfull, hfaith, _, _, hcov, _⟩ := affine_closed_site_functor_properties A I
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  have : v.Full := hfull
  have : v.Faithful := hfaith
  have : IsIso (adj.counit.app B) := hε
  have : (topology (Spec (.of A))).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt (Spec (.of A)))
      (topology (Spec (.of A))) (ProEt.topology (Spec (.of A)))
  have hvB := projectiveEvaluation_of_iso (asIso (adj.counit.app B)).symm hB
  intro P Q φ hφ y
  have : Epi φ := hφ
  have hlocal : Sheaf.IsLocallySurjective φ := (Sheaf.isLocallySurjective_iff_epi φ).mpr hφ
  obtain ⟨W, q, hq, x, hx⟩ := (isLocallySurjective_iff φ).mp hlocal (r.obj B) y
  have hpre : Presieve.singleton q ∈ precoverage (r.obj B) := by
    have h := finite_cover_precoverage (fun _ : PUnit.{u + 1} ↦ W)
      (fun _ ↦ q) (fun z ↦ ⟨PUnit.unit, hq.surj z⟩)
    simpa only [Presieve.ofArrows_pUnit] using h
  have hcover : Sieve.generate (Presieve.singleton (v.map q)) ∈ topology _ (v.obj (r.obj B)) := by
    have h := precoverage_cover (hcov (r.obj B) _ hpre)
    simpa only [Presieve.map_singleton] using h
  obtain ⟨t, ht⟩ := cover_split_of_cover (v.obj (r.obj B)) hvB (v.map q) hcover
  let σ : r.obj B ⟶ W := v.preimage t
  have hσ : σ ≫ q = 𝟙 _ := by
    apply v.map_injective
    dsimp only [σ]
    rw [v.map_comp, v.map_preimage, v.map_id]
    exact ht
  refine ⟨P.obj.map σ.op x, ?_⟩
  rw [φ.hom.naturality_apply, hx, ← Q.obj.map_comp_apply, ← op_comp, hσ]
  exact Q.obj.map_id_apply _ y

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_precomposition_toSheafify {S T : Scheme.{u}}
    (v : S.AffineProEt ⥤ T.AffineProEt) {r : T.AffineProEt ⥤ S.AffineProEt}
    (adj : v ⊣ r) [(topology S).Subcanonical]
    (hcov : ∀ (V : S.AffineProEt) (R : Presieve V), R ∈ precoverage V →
      R.map v ∈ precoverage (v.obj V))
    (H : Sheaf (topology T) AddCommGrpCat.{u + 1}) (V : S.AffineProEt)
    (hV : ∀ (P Q : Sheaf (topology S) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op V))) :
    IsIso ((toSheafify (topology S) (v.op ⋙ H.obj)).app (op V)) := by
  let H₀ := (sheafCompose (topology T) (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj H
  have hbij : Function.Bijective
      ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) :=
    ⟨precomposition_unit_injective v hcov H₀ V,
      precomposition_unit_surjective v adj H₀ V hV⟩
  let e := sheafifyComposeIso (topology S)
    (CategoryTheory.forget AddCommGrpCat.{u + 1}) (v.op ⋙ H.obj)
  have hfac := congrArg (fun φ ↦ φ.app (op V))
    (sheafComposeIso_hom_fac (topology S)
      (CategoryTheory.forget AddCommGrpCat.{u + 1}) (v.op ⋙ H.obj))
  have : IsIso ((toSheafify (topology S) (v.op ⋙ H₀.obj)).app (op V)) :=
    (isIso_iff_bijective _).mpr hbij
  apply (ConcreteCategory.isIso_iff_bijective _).2
  change Function.Bijective (ConcreteCategory.hom
    ((Functor.whiskerRight (toSheafify (topology S) (v.op ⋙ H.obj))
      (CategoryTheory.forget AddCommGrpCat.{u + 1})).app (op V)))
  have he := congrArg ConcreteCategory.hom hfac
  have hc : Function.Bijective (ConcreteCategory.hom
      (e.hom.app (op V))) := (isIso_iff_bijective _).mp inferInstance
  rw [← he]
  exact hc.comp hbij

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_affineUnit_sections
    (A : Type u) [CommRing A] (I : Ideal A)
    (B : (Spec (.of A)).AffineProEt)
    (hB : ∀ (P Q : Sheaf (topology (Spec (.of A))) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B)))
    (adj : closedSiteLift A I ⊣ closedSiteBaseChange A I)
    (hε : IsIso (adj.counit.app B))
    (F : Sheaf (ProEt.topology (Spec (.of A))) AddCommGrpCat.{u + 1}) :
    IsIso (((proEtaleSheafAdjunction
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        AddCommGrpCat.{u + 1}).unit.app F).hom.app (op ((toProEt (Spec (.of A))).obj B))) := by
  let X := Spec (.of A)
  let Z := Spec (.of (A ⧸ I))
  let i : Z ⟶ X := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  let v := closedSiteLift A I
  let r := closedSiteBaseChange A I
  obtain ⟨_, _, _, _, hco, _, hcov, _⟩ := affine_closed_site_functor_properties A I
  have : v.IsCocontinuous (topology Z) (topology X) := hco
  have : r.IsContinuous (topology X) (topology Z) :=
    adj.isContinuous_of_isCocontinuous _ _
  have : (topology Z).Subcanonical :=
    GrothendieckTopology.subcanonical_of_full_of_faithful (toProEt Z)
      (topology Z) (ProEt.topology Z)
  let D := AddCommGrpCat.{u + 1}
  let RX := (toProEt X).sheafPushforwardContinuous D (topology X) (ProEt.topology X)
  let RZ := (toProEt Z).sheafPushforwardContinuous D (topology Z) (ProEt.topology Z)
  let L := sheafToPresheaf (topology X) D ⋙
    (Functor.whiskeringLeft _ _ D).obj v.op ⋙ presheafToSheaf (topology Z) D
  let R := r.sheafPushforwardContinuous D (topology X) (topology Z)
  let a : L ⊣ R :=
    ((adj.op.whiskerLeft D).comp (sheafificationAdjunction (topology Z) D)).restrictFullyFaithful
      (Functor.FullyFaithful.ofFullyFaithful (sheafToPresheaf (topology X) D))
      (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _)
  have t : r ⋙ toProEt Z ≅ toProEt X ⋙ proEtaleBaseChange i := Iso.refl _
  have : (toProEt X ⋙ proEtaleBaseChange i).IsContinuous
      (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (ProEt.topology X) (ProEt.topology Z)
  have : (r ⋙ toProEt Z).IsContinuous (topology X) (ProEt.topology Z) :=
    Functor.isContinuous_comp _ _ (topology X) (topology Z) (ProEt.topology Z)
  let beta : proEtaleSheafDirectImage i D ⋙ RX ≅ RZ ⋙ R :=
    Functor.sheafPushforwardContinuousComp (toProEt X) (proEtaleBaseChange i)
      D (topology X) (ProEt.topology X) (ProEt.topology Z) ≪≫
    Functor.sheafPushforwardContinuousIso t.symm D (topology X) (ProEt.topology Z) ≪≫
    (Functor.sheafPushforwardContinuousComp r (toProEt Z) D
      (topology X) (topology Z) (ProEt.topology Z)).symm
  let alpha := ((mateEquiv (proEtaleSheafAdjunction i D) a).symm beta.hom)
  have : IsIso alpha := isIso_inverseMate_of_equivalences (proEtaleSheafAdjunction i D) a beta
  have hp := projectiveEvaluation_closedBaseChange A I B hB adj hε
  have hη : IsIso ((a.unit.app (RX.obj F)).hom.app (op B)) := by
    have heq : (a.unit.app (RX.obj F)).hom.app (op B) =
        (RX.obj F).obj.map (adj.counit.app B).op ≫
          (toSheafify (topology Z) (v.op ⋙ (RX.obj F).obj)).app (op (r.obj B)) := by
      dsimp [a]
      rw [← sheafToPresheaf_map, Adjunction.map_restrictFullyFaithful_unit_app]
      simp only [Adjunction.comp_unit_app, sheafificationAdjunction_unit_app,
        Functor.comp_map, Iso.refl_hom, NatTrans.id_app]
      rfl
    rw [heq]
    have : IsIso (adj.counit.app B) := hε
    have := isIso_precomposition_toSheafify v adj hcov (RX.obj F) (r.obj B) hp
    infer_instance
  have hu := unit_mateEquiv_symm (proEtaleSheafAdjunction i D) a beta.hom F
  have hu' := congrArg (fun f ↦ f.hom.app (op B)) hu
  change ((proEtaleSheafAdjunction i D).unit.app F).hom.app (op ((toProEt X).obj B)) ≫
    (beta.hom.app _).hom.app (op B) =
      (a.unit.app (RX.obj F)).hom.app (op B) ≫
        (R.map (alpha.app F)).hom.app (op B) at hu'
  have : IsIso (((proEtaleSheafAdjunction i D).unit.app F).hom.app
      (op ((toProEt X).obj B)) ≫ (beta.hom.app _).hom.app (op B)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.hom.app _).hom.app (op B))

end AffineProEt

section Localization
universe u'
open AlgebraicGeometry MorphismProperty AlgebraicGeometry.ProEtale CategoryTheory.Category
variable (A : Type u') [Category.{u + 1} A]

variable {U' U Z' Z : Scheme.{u}} {g' : U' ⟶ U} {j' : U' ⟶ Z'} {j : U ⟶ Z} {g'' : Z' ⟶ Z}

variable [WeaklyEtale j] [WeaklyEtale j']

local instance : (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
    MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
 instIsContinuousOverSchemeWeaklyEtaleTopMorphismPropertyCompPullbackMapTopology_weilConjectures.{u}
    (g' := g') (j' := j')

local instance : (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
    MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
      (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z') :=
 instIsContinuousOverSchemeWeaklyEtaleTopMorphismPropertyCompMapPullbackTopology_weilConjectures.{u}
    (j := j) (g'' := g'')

/-- The base change map `g''_* ⋙ j^* ⟶ j'^* ⋙ g'_*` on pro-étale sheaves, with the pullbacks
along the weakly étale morphisms `j` and `j'` computed as restrictions along the localization
functors: the map induced by `CategoryTheory.MorphismProperty.Over.pullbackMapComparison`. -/
private noncomputable def localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    (g'')_*[A] ⋙ ProEtale.localizationRestriction A j inferInstance ⟶
      ProEtale.localizationRestriction A j' inferInstance ⋙ (g')_*[A] :=
  Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') sq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')

/-- If the square is cartesian, the base change map on restrictions is an isomorphism, being
induced by an isomorphism of site functors. -/
private lemma isIso_localRestrictionBaseChangeMap_of_isPullback
    (hsq : IsPullback g' j' j g'') :
    IsIso (localRestrictionBaseChangeMap A hsq.toCommSq) :=
  have := MorphismProperty.Over.isIso_pullbackMapComparison_of_isPullback
    (inferInstance : @WeaklyEtale _ _ j) (inferInstance : @WeaklyEtale _ _ j') hsq
  inferInstanceAs (IsIso (Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.pullbackMapComparison (inferInstance : @WeaklyEtale _ _ j)
      (inferInstance : @WeaklyEtale _ _ j') hsq.toCommSq) A
    (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')))

private noncomputable def siteMate (sq : CommSq g' j' j g'') :=
  (mateEquiv
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j (inferInstance : WeaklyEtale j) trivial)
    (MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ j'
      (inferInstance : WeaklyEtale j') trivial)
    (TwoSquare.mk _ _ _ _ (MorphismProperty.Over.pullbackMapComparison
      (inferInstance : WeaklyEtale j) (inferInstance : WeaklyEtale j') sq)))
private theorem siteMate_eq (sq : CommSq g' j' j g'') :
    siteMate sq = (MorphismProperty.Over.pullbackComp g' j).inv ≫
      (MorphismProperty.Over.pullbackCongr (P := @WeaklyEtale) (Q := ⊤) sq.w).hom ≫
      (MorphismProperty.Over.pullbackComp j' g'').hom := by
  ext b
  dsimp [siteMate, mateEquiv]
  set_option backward.defeqAttrib.useBackward true in
  apply pullback.hom_ext
  · apply pullback.hom_ext <;>
      simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk]
  · simp [MorphismProperty.Over.pullbackCongr, MorphismProperty.Over.pullback,
      MorphismProperty.Over.mk]

private lemma isIso_mate_localRestrictionBaseChangeMap (sq : CommSq g' j' j g'') :
    IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  have hs : IsIso (siteMate sq) := by rw [siteMate_eq]; infer_instance
  have h (F : Sheaf (ProEt.topology U') A) (b : Z.ProEt) :
      ((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app
          (op b) = F.obj.map ((siteMate sq).app b).op := by
    simp only [Functor.comp_obj, mateEquiv, ProEtale.localizationRestrictionLowerStarAdjunction,
      Adjunction.sheafPushforwardContinuous, Functor.id_obj,
      localRestrictionBaseChangeMap, Functor.sheafPushforwardContinuousNatTrans,
      ObjectProperty.ι_obj, Equiv.coe_fn_mk, NatTrans.comp_app, Functor.rightUnitor_inv_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app, comp_id, id_comp,
      ObjectProperty.FullSubcategory.comp_hom, Adjunction.whiskerLeft_unit_app_app,
      Functor.op_obj, Adjunction.op_unit_app, NatTrans.op_app,
      Adjunction.whiskerLeft_counit_app_app, Adjunction.op_counit_app,
      ProEtale.lowerStar_map_hom_app]
    change F.obj.map _ ≫ F.obj.map _ ≫ F.obj.map _ = _
    simp only [← Functor.map_comp]
    dsimp [siteMate, mateEquiv]
    simp only [id_comp, comp_id, ← Functor.map_comp, ← op_comp]
    simp only [Functor.map_comp, op_comp, Category.assoc]
  have hF (F : Sheaf (ProEt.topology U') A) : IsIso ((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F) := by
    have hB : ∀ b : Z.ProEtᵒᵖ, IsIso (((mateEquiv
        (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
        (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom.app b) :=
      fun b ↦ by rw [h F b.unop]; infer_instance
    apply (isIso_iff_of_reflects_iso _ (sheafToPresheaf _ A)).mp
    change IsIso (((mateEquiv
      (ProEtale.localizationRestrictionLowerStarAdjunction A j' inferInstance)
      (ProEtale.localizationRestrictionLowerStarAdjunction A j inferInstance)
      (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq))).app F).hom)
    exact NatIso.isIso_of_isIso_app _
  exact NatIso.isIso_of_isIso_app _

variable [Abelian A] [IsGrothendieckAbelian.{u + 1} A]

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_inverseMate_localRestrictionBaseChange (sq : CommSq g' j' j g'') :
    IsIso (((mateEquiv (proEtaleSheafAdjunction g'' A)
      (proEtaleSheafAdjunction g' A)).symm
        (TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let aj := localizationRestrictionLowerStarAdjunction A j inferInstance
  let ab := localizationRestrictionLowerStarAdjunction A j' inferInstance
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A sq)
  let alpha := (mateEquiv ai ak).symm beta
  have hm : mateEquiv ai ak alpha = beta := (mateEquiv ai ak).apply_symm_apply beta
  have h := iterated_mateEquiv_conjugateEquiv ai ak aj ab alpha
  rw [hm] at h
  have hc : IsIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha) := by
    rw [← h]
    exact isIso_mate_localRestrictionBaseChangeMap A sq
  have := hc
  let e := (conjugateIsoEquiv (ai.comp ab) (aj.comp ak)).symm
    (asIso (conjugateEquiv (ai.comp ab) (aj.comp ak) alpha))
  have he : e.hom = alpha :=
    (conjugateEquiv (ai.comp ab) (aj.comp ak)).symm_apply_apply alpha
  change IsIso alpha
  rw [← he]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem isIso_unit_sections_of_localization
    (hsq : IsPullback g' j' j g'') (W : U.ProEt)
    (F : Sheaf (ProEt.topology Z) A)
    (hη : IsIso (((proEtaleSheafAdjunction g' A).unit.app
      ((localizationRestriction A j inferInstance).obj F)).hom.app (op W))) :
    IsIso (((proEtaleSheafAdjunction g'' A).unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) := by
  let ai := proEtaleSheafAdjunction g'' A
  let ak := proEtaleSheafAdjunction g' A
  let G := localizationRestriction A j inferInstance
  let R := proEtaleSheafDirectImage g' A
  let beta := TwoSquare.mk _ _ _ _ (localRestrictionBaseChangeMap A hsq.toCommSq)
  let alpha := (mateEquiv ai ak).symm beta
  have : IsIso alpha := isIso_inverseMate_localRestrictionBaseChange A hsq.toCommSq
  have : IsIso beta := isIso_localRestrictionBaseChangeMap_of_isPullback A hsq
  have hu := unit_mateEquiv_symm ai ak beta F
  have hu' := congrArg (fun f ↦ f.hom.app (op W)) hu
  change ((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W) =
    (ak.unit.app (G.obj F)).hom.app (op W) ≫
      (R.map (alpha.app F)).hom.app (op W) at hu'
  have : IsIso ((ak.unit.app (G.obj F)).hom.app (op W)) := hη
  have : IsIso (((ai.unit.app F).hom.app
      (op ((MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)).obj W))) ≫
      (beta.app _).hom.app (op W)) := by
    rw [hu']
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((beta.app _).hom.app (op W))

end Localization

set_option backward.isDefEq.respectTransparency false in
private theorem affine_closed_coordinates {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left] :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    ∃ e : pullback V.hom i ≅ Spec (.of (A ⧸ I)),
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        pullback.fst V.hom i ≫ V.left.isoSpec.hom := by
  let T := pullback V.hom i
  let f : T ⟶ V.left := pullback.fst V.hom i
  obtain ⟨hT, hf⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine f
  have : IsAffine T := hT
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker f.appTop.hom
  let E := RingHom.quotientKerEquivOfSurjective hf
  let e : T ≅ Spec (.of (A ⧸ I)) :=
    T.isoSpec ≪≫ Scheme.Spec.mapIso E.toCommRingCatIso.op
  refine ⟨e, ?_⟩
  change T.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom E.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) = f ≫ V.left.isoSpec.hom
  rw [← Spec.map_comp]
  have he : CommRingCat.ofHom (Ideal.Quotient.mk I) ≫
      CommRingCat.ofHom E.toRingHom = f.appTop := by
    ext a
    exact RingHom.quotientKerEquivOfSurjective_apply_mk hf a
  rw [he]
  exact Scheme.isoSpec_hom_naturality f

set_option backward.isDefEq.respectTransparency false in
private theorem affine_closed_square {X Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] (V : X.ProEt) [IsAffine V.left] :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    ∃ b : Spec (.of (A ⧸ I)) ⟶ Z,
      WeaklyEtale b ∧ IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))
        b (V.left.isoSpec.inv ≫ V.hom) i := by
  obtain ⟨e, he⟩ := affine_closed_coordinates i V
  let b := e.inv ≫ pullback.snd V.hom i
  have hb : WeaklyEtale b := by
    dsimp [b]
    infer_instance
  refine ⟨b, hb, ?_⟩
  apply (IsPullback.of_hasPullback V.hom i).of_iso e V.left.isoSpec
    (Iso.refl Z) (Iso.refl X)
  · exact he.symm
  · simp [b]
  · simp
  · simp

/-- For affine `V`, if evaluation at the identity object is projective and the counit of the
affine closed-site lift adjunction is invertible there, then the inverse-image unit is an
isomorphism on sections over `V`. -/
theorem isIso_proEtaleUnit_sections_of_closedSiteCounit
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (V : X.ProEt) [IsAffine V.left]
 :
    let A := Γ(V.left, ⊤)
    let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
    let B := AffineProEt.ofEtale (𝟙 (Spec A))
    (∀ (P Q : Sheaf (AffineProEt.topology (Spec A)) (Type (u + 1))) (φ : P ⟶ Q),
      Epi φ → Function.Surjective (φ.hom.app (op B))) →
    ∀ adj : AffineProEt.closedSiteLift A I ⊣ AffineProEt.closedSiteBaseChange A I,
      IsIso (adj.counit.app B) →
      IsIso (Functor.whiskerRight (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
        ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))) := by
  dsimp only
  intro hB adj hε
  let A := Γ(V.left, ⊤)
  let I := RingHom.ker (pullback.fst V.hom i).appTop.hom
  let a : Spec A ⟶ X := V.left.isoSpec.inv ≫ V.hom
  have : WeaklyEtale a := by dsimp [a]; infer_instance
  obtain ⟨b, hb, hsq⟩ := affine_closed_square i V
  have : WeaklyEtale b := hb
  let W : (Spec A).ProEt := ProEt.mk (𝟙 (Spec A))
  let e : (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale a)).obj W ≅ V :=
    MorphismProperty.Over.isoMk V.left.isoSpec.symm (by
      change a = (𝟙 (Spec A)) ≫ a
      exact (Category.id_comp a).symm)
  have hη (F : Sheaf (ProEt.topology X) AddCommGrpCat.{u + 1}) :
      IsIso (((proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit.app F).hom.app
        (op V)) := by
    have hf := AffineProEt.isIso_affineUnit_sections A I
      (AffineProEt.ofEtale (𝟙 (Spec A))) hB adj hε
      ((AlgebraicGeometry.ProEtale.localizationRestriction AddCommGrpCat.{u + 1}
        a inferInstance).obj F)
    have hl := isIso_unit_sections_of_localization AddCommGrpCat.{u + 1} hsq W F hf
    exact (NatTrans.isIso_app_iff_of_iso _ e.op).mpr hl
  have : ∀ F, IsIso ((Functor.whiskerRight
      (proEtaleSheafAdjunction i AddCommGrpCat.{u + 1}).unit
      ((sheafSections (ProEt.topology X) AddCommGrpCat.{u + 1}).obj (op V))).app F) := hη
  exact NatIso.isIso_of_isIso_app _

end AlgebraicGeometry.Scheme

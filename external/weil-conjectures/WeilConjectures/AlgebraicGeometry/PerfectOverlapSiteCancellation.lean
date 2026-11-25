/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The return map becomes the counit after moving back to the scheme site.
The defining composition comparison of `openSiteReturnIso` inserts the
equivalence unit; the triangle identity for the site equivalence cancels it. -/
theorem openSiteReturn_counit_app
    (X : Scheme.{u}) (W : X.Opens) (E : schemeDerivedCategory X) :
    let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let R := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
    let PU := (schemeOpenRestriction X W).mapDerivedCategory
    e.mapDerivedCategory.functor.map ((openSiteReturnIso X W).hom.app E) ≫
      (Functor.mapDerivedCategoryCompIso R e.functor).hom.app E =
      e.mapDerivedCategory.counitIso.hom.app (PU.obj E) := by
  intro e R PU
  unfold openSiteReturnIso
  simp only [Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Functor.rightUnitor_hom_app,
    Category.id_comp, Functor.map_comp, Category.assoc]
  exact equivalence_return_cancel e.mapDerivedCategory (R.mapDerivedCategory.obj E)
    (PU.obj E) ((Functor.mapDerivedCategoryCompIso R e.functor).symm.app E)

/-- The apex equivalence maps the open-site return and composition maps to
the site counit on the overlap scheme. This is the component form used in
the canonical overlap object pin. -/
theorem perfectOverlapApex_siteReturn_comp
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (E : schemeDerivedCategory X) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let e : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let Rw := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    (perfectOverlapApexEquivalence g pX pY b hg U V).functor.map
        ((openSiteReturnIso X W).hom.app E) ≫
      cart.functor.map ((Functor.mapDerivedCategoryCompIso Rw e.functor).hom.app E) =
        cart.functor.map (e.mapDerivedCategory.counitIso.hom.app
          ((schemeOpenRestriction X W).mapDerivedCategory.obj E)) := by
  intro W e Rw cart
  have h := congrArg cart.functor.map (openSiteReturn_counit_app X W E)
  simp only [Functor.map_comp] at h
  exact h

/-- The overlap return triangle and the apex counit paste to a single
component equation. This is independent of the later-stage comparison data. -/
theorem perfectOverlapApex_overlapReturn_comp
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (E : schemeDerivedCategory X) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let PU := (schemeOpenRestriction X P).mapDerivedCategory
    let LW := (overlapSiteInverse (P ⊓ Q)).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory
    let τ : RU ⋙ SP ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let Rw := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) (P ⊓ Q)
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map (SP.map ((openSiteReturnIso X P).hom.app E)) ≫
        apex.functor.map (τ.hom.app E) ≫
          cart.functor.map ((Functor.mapDerivedCategoryCompIso Rw eW.functor).hom.app E) =
      apex.functor.map ((openSiteOverlapIso X i).hom.app (PU.obj E)) ≫
        apex.functor.map (LW.map ((schemeDerivedOpenRestrictionCompIso X i).hom.app E)) ≫
          cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
            ((schemeOpenRestriction X (P ⊓ Q)).mapDerivedCategory.obj E)) := by
  intro P Q i PU LW SP RU τ eW Rw cart apex
  have hTri := congrArg apex.functor.map (openSiteReturn_overlap_triangle_app X i E)
  simp only [Functor.map_comp] at hTri
  have hCancel := perfectOverlapApex_siteReturn_comp g pX pY b hg U V E
  exact paste_return_triangle hTri hCancel

/-- The same return calculation for either restriction of the fixed overlap.
The proof uses only the inclusion of `U ⊓ V` in the chosen open. -/
theorem perfectOverlapApex_overlapReturn_comp_for
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (E : schemeDerivedCategory X) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let Q := g ⁻¹ᵁ L
    let i : W ⟶ Q := homOfLE (fun _ hx ↦ hWL hx)
    let PQ := (schemeOpenRestriction X Q).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let RQ := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory
    let τ : RQ ⋙ SQ ≅
        (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W).mapDerivedCategory :=
      Functor.mapDerivedCategoryCompIso _ _ ≪≫
        Functor.mapDerivedCategoryNatIso
          (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let Rw := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) W
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map (SQ.map ((openSiteReturnIso X Q).hom.app E)) ≫
        apex.functor.map (τ.hom.app E) ≫
          cart.functor.map ((Functor.mapDerivedCategoryCompIso Rw eW.functor).hom.app E) =
      apex.functor.map ((openSiteOverlapIso X i).hom.app (PQ.obj E)) ≫
        apex.functor.map (LW.map ((schemeDerivedOpenRestrictionCompIso X i).hom.app E)) ≫
          cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
            ((schemeOpenRestriction X W).mapDerivedCategory.obj E)) := by
  intro W Q i PQ LW SQ RQ τ eW Rw cart apex
  have hTri := congrArg apex.functor.map (openSiteReturn_overlap_triangle_app X i E)
  simp only [Functor.map_comp] at hTri
  have hCancel := perfectOverlapApex_siteReturn_comp g pX pY b hg U V E
  exact paste_return_triangle hTri hCancel

/-- Nested restriction followed by the site counit and its inverse comparison
reduces to the counit on the directly restricted object. Source: Stacks
Project, Tags 08BT and 08BV. Apply naturality of the equivalence counit to
the nested restriction isomorphism and cancel its inverse. -/
theorem perfectOverlapApex_nestedCounit_cancel_for
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (E : schemeDerivedCategory X) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let Q := g ⁻¹ᵁ L
    let i : W ⟶ Q := homOfLE (fun _ hx ↦ hWL hx)
    let PQ := (schemeOpenRestriction X Q).mapDerivedCategory
    let SQ := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let PW := (schemeOpenRestriction X W).mapDerivedCategory
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let LW := eW.inverse.mapDerivedCategory
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map (LW.map (σ.hom.app E)) ≫
        cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (PW.obj E)) ≫
          cart.functor.map (σ.inv.app E) =
      cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
        (SQ.obj (PQ.obj E))) := by
  intro W Q i PQ SQ PW σ eW LW cart apex
  have hc := congrArg cart.functor.map
    (equivalence_counit_transport_cancel eW.mapDerivedCategory (σ.app E))
  simp only [Functor.map_comp] at hc
  exact hc

/-- The first-open form uses the same inclusion and projection terms as the
canonical object comparison. It is the specialization of the general counit
transport equation to `inf_le_left`. -/
theorem perfectOverlapApex_nestedCounit_cancel_U
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (E : schemeDerivedCategory X) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let PU := (schemeOpenRestriction X P).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let PW := (schemeOpenRestriction X (P ⊓ Q)).mapDerivedCategory
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let LW := eW.inverse.mapDerivedCategory
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map (LW.map (σ.hom.app E)) ≫
        cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (PW.obj E)) ≫
          cart.functor.map (σ.inv.app E) =
      cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app
        (SU.obj (PU.obj E))) := by
  exact perfectOverlapApex_nestedCounit_cancel_for g pX pY b hg
    U V U inf_le_left E

/-- The local identification cancels across the open-site comparison and
counit. Source: Stacks Project, Tags 08BT and 08BV. Naturality of the
comparison moves the local isomorphism through the overlap restriction;
naturality of the equivalence counit then cancels its inverse. -/
theorem perfectOverlapApex_localIso_cancel_for
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (a : schemeDerivedCategory (g ⁻¹ᵁ L).toScheme)
    (E : schemeDerivedCategory X)
    (φ : a ≅ (schemeOpenRestriction X (g ⁻¹ᵁ L)).mapDerivedCategory.obj E) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let Q := g ⁻¹ᵁ L
    let i : W ⟶ Q := homOfLE (fun _ hx ↦ hWL hx)
    let PQ := (schemeOpenRestriction X Q).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let LU := (overlapSiteInverse Q).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let ω := openSiteOverlapIso X i
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map ((LU ⋙ SP).map φ.hom) ≫
        apex.functor.map (ω.hom.app (PQ.obj E)) ≫
          cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (SU.obj (PQ.obj E))) ≫
            cart.functor.map (SU.map φ.inv) =
      apex.functor.map (ω.hom.app a) ≫
        cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (SU.obj a)) := by
  intro W Q i PQ SU LU SP ω eW cart apex
  exact equivalence_comparison_counit_transport eW.mapDerivedCategory
    cart.functor (LU ⋙ SP) SU ω φ

/-- The site part of a canonical overlap object comparison is the comparison
at the pulled-back local object. Source: Stacks Project, Tags 08BT and 08BV.
First use naturality of the site counit to cancel the nested restriction
isomorphism. Then use the local-isomorphism triangle to move `φ` through the
open-site comparison and cancel its inverse. -/
theorem perfectOverlapApex_siteTail_cancel_for
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (a : schemeDerivedCategory (g ⁻¹ᵁ L).toScheme)
    (E : schemeDerivedCategory X)
    (φ : a ≅ (schemeOpenRestriction X (g ⁻¹ᵁ L)).mapDerivedCategory.obj E) :
    let W := g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V
    let Q := g ⁻¹ᵁ L
    let i : W ⟶ Q := homOfLE (fun _ hx ↦ hWL hx)
    let PQ := (schemeOpenRestriction X Q).mapDerivedCategory
    let SU := (schemeOpenOverlapRestriction X i).mapDerivedCategory
    let PW := (schemeOpenRestriction X W).mapDerivedCategory
    let LU := (overlapSiteInverse Q).mapDerivedCategory
    let LW := (overlapSiteInverse W).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let ω := openSiteOverlapIso X i
    let σ := schemeDerivedOpenRestrictionCompIso X i
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over W) ≌
      SheafOfModules.{u} (moduleRings W.toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv W
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    apex.functor.map ((LU ⋙ SP).map φ.hom) ≫
      apex.functor.map (ω.hom.app (PQ.obj E)) ≫
      apex.functor.map (LW.map (σ.hom.app E)) ≫
      cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (PW.obj E)) ≫
      cart.functor.map (σ.inv.app E) ≫
      cart.functor.map (SU.map φ.inv) =
        apex.functor.map (ω.hom.app a) ≫
          cart.functor.map (eW.mapDerivedCategory.counitIso.hom.app (SU.obj a)) := by
  intro W Q i PQ SU PW LU LW SP ω σ eW cart apex
  have hn := perfectOverlapApex_nestedCounit_cancel_for g pX pY b hg U V L hWL E
  have hl := perfectOverlapApex_localIso_cancel_for g pX pY b hg U V L hWL a E φ
  dsimp only at hn hl
  exact paste_middle_three hn hl

end AlgebraicGeometry

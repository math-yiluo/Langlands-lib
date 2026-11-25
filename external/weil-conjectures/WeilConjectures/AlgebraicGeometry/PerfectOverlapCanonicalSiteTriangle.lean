/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellation
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapSiteCancellationAbstract

/-! # Canonical local-object site triangle

Source: Stacks Project, Tags 08BT, 08BV and 08DW.
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
  schemeOpenRestriction_additive schemeOpenRestriction_preservesFiniteLimits
  schemeOpenRestriction_preservesFiniteColimits

private theorem paste_return_six_with_edges
    {C₀ : Type*} [Category* C₀]
    {A B C D E F G H I J K L : C₀}
    {p : A ⟶ B} {a : B ⟶ C} {r : C ⟶ D} {t : D ⟶ E}
    {c : E ⟶ F} {d : F ⟶ G} {f : G ⟶ H} {q : H ⟶ J}
    {x : C ⟶ K} {y : K ⟶ L} {z : L ⟶ F} {s : B ⟶ I} {v : I ⟶ H}
    (hreturn : r ≫ t ≫ c = x ≫ y ≫ z)
    (htail : a ≫ x ≫ y ≫ z ≫ d ≫ f = s ≫ v) :
    p ≫ a ≫ r ≫ t ≫ c ≫ d ≫ f ≫ q = p ≫ s ≫ v ≫ q := by
  have h := congrArg (fun k ↦ p ≫ a ≫ k ≫ d ≫ f ≫ q) hreturn
  simp only [Category.assoc] at h
  exact h.trans (paste_six_with_edges htail)

variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

-- The statement elaborates two derived site categories and their equivalence.
/-- A local comparison transported to the overlap agrees with the fixed
scheme comparison after returning from the open site. Expand the prescribed
theta map into kappa, the local object isomorphism and the return unit. The
overlap-return triangle replaces the return unit and site restriction by the
open-site comparison. The nested counit and local-isomorphism triangles then
cancel the two transported inverses, leaving the fixed stage object map. 
(blueprint: lem-pc-perfect-overlap-canonical-site-triangle)
-/
theorem perfectOverlapCanonicalSiteTriangleU
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (A : schemeDerivedCategory U.toScheme)
    (E : schemeDerivedCategory X)
    (φ : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let i : P ⊓ Q ⟶ P := homOfLE inf_le_left
    let RU := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) P).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
    let SP := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let LU := (overlapSiteInverse P).mapDerivedCategory
    let τ : RU ⋙ SP ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    ∀ (M : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over P)))
      (κ : M ≅ LU.obj ((derivedPullback (g ∣_ U)).obj A))
      (θ : M ≅ RU.obj E),
      θ = κ ≪≫ LU.mapIso φ ≪≫ (openSiteReturnIso X P).app E →
      apex.functor.map (SP.map θ.hom) ≫ apex.functor.map (τ.hom.app E) ≫
          (perfectOverlapApexObjectIso g pX pY b hg U V U inf_le_left A E φ).hom =
        apex.functor.map (SP.map κ.hom) ≫
          apex.functor.map ((openSiteOverlapIso X i).hom.app
            ((derivedPullback (g ∣_ U)).obj A)) ≫
          cart.functor.map
            (eW.mapDerivedCategory.counitIso.hom.app
              ((schemeOpenOverlapRestriction X i).mapDerivedCategory.obj
                ((derivedPullback (g ∣_ U)).obj A))) ≫
          ((perfectOverlapStageObjectIso g pX pY b hg U V U inf_le_left).app A).hom := by
  intro P Q i RU RW SP LU τ eW apex cart M κ θ hθ
  rw [hθ]
  unfold perfectOverlapApexObjectIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [id, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  simpa only [Functor.comp_map, Category.assoc, Iso.symm_hom] using
    (paste_return_six_with_edges
      (perfectOverlapApex_overlapReturn_comp g pX pY b hg U V E)
      (perfectOverlapApex_siteTail_cancel_for g pX pY b hg U V U inf_le_left
        ((derivedPullback (g ∣_ U)).obj A) E φ))

-- The second statement also elaborates two derived site categories.
/-- The second-open site triangle follows by the same return, nested-counit,
and local-isomorphism pasting, using the inclusion `U ⊓ V ≤ V`. 
(blueprint: lem-pc-perfect-overlap-canonical-site-triangle)
-/
theorem perfectOverlapCanonicalSiteTriangleV
    {X Y S T : Scheme.{u}} (g : X ⟶ Y) (pX : X ⟶ T)
    (pY : Y ⟶ S) (b : T ⟶ S) (hg : IsPullback g pX pY b)
    (U V : Y.Opens) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φ : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
    let P := g ⁻¹ᵁ U
    let Q := g ⁻¹ᵁ V
    let i : P ⊓ Q ⟶ Q := homOfLE inf_le_right
    let RV := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) Q).mapDerivedCategory
    let RW := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (P ⊓ Q)).mapDerivedCategory
    let SQ := (SheafOfModules.overMap.{u} (moduleRings X.toRingedSpace) i).mapDerivedCategory
    let LV := (overlapSiteInverse Q).mapDerivedCategory
    let τ : RV ⋙ SQ ≅ RW := Functor.mapDerivedCategoryCompIso _ _ ≪≫
      Functor.mapDerivedCategoryNatIso
        (SheafOfModules.overFunctorMap.{u} (moduleRings X.toRingedSpace) i)
    let eW : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (P ⊓ Q)) ≌
      SheafOfModules.{u} (moduleRings (P ⊓ Q).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv (P ⊓ Q)
    let apex := perfectOverlapApexEquivalence g pX pY b hg U V
    let cart := perfectOverlapStageEquivalence g pX pY b hg U V
    ∀ (M : DerivedCategory (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over Q)))
      (κ : M ≅ LV.obj ((derivedPullback (g ∣_ V)).obj B))
      (θ : M ≅ RV.obj E),
      θ = κ ≪≫ LV.mapIso φ ≪≫ (openSiteReturnIso X Q).app E →
      apex.functor.map (SQ.map θ.hom) ≫ apex.functor.map (τ.hom.app E) ≫
          (perfectOverlapApexObjectIso g pX pY b hg U V V inf_le_right B E φ).hom =
        apex.functor.map (SQ.map κ.hom) ≫
          apex.functor.map ((openSiteOverlapIso X i).hom.app
            ((derivedPullback (g ∣_ V)).obj B)) ≫
          cart.functor.map
            (eW.mapDerivedCategory.counitIso.hom.app
              ((schemeOpenOverlapRestriction X i).mapDerivedCategory.obj
                ((derivedPullback (g ∣_ V)).obj B))) ≫
          ((perfectOverlapStageObjectIso g pX pY b hg U V V inf_le_right).app B).hom := by
  intro P Q i RV RW SQ LV τ eW apex cart M κ θ hθ
  rw [hθ]
  unfold perfectOverlapApexObjectIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  simp only [id, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc, Iso.app_hom]
  simpa only [Functor.comp_map, Category.assoc, Iso.symm_hom] using
    (paste_return_six_with_edges
      (perfectOverlapApex_overlapReturn_comp_for g pX pY b hg U V V inf_le_right E)
      (perfectOverlapApex_siteTail_cancel_for g pX pY b hg U V V inf_le_right
        ((derivedPullback (g ∣_ V)).obj B) E φ))

end AlgebraicGeometry

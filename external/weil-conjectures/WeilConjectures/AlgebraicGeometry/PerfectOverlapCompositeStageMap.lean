/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare

/-! # The constructed cartesian stage map for a composite overlap -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local irreducible] perfectHomComposition
attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian
variable [∀ Z : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
variable [∀ (Z : Scheme.{u}) (U : Z.Opens),
  HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]

/-- The site counit followed by the nested-square, local composition and stage-object maps.
Source: Stacks Project, Tags 08DW and 0D5S. Each factor is explicitly constructed.
(blueprint: def-pc-perfect-overlap-composite-stage-map). -/
@[irreducible] noncomputable def perfectOverlapCompositeStageMapAt
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S) (b : C ⟶ S)
    (hg : IsPullback g pX pY b) (U V L : Y.Opens) (hWL : U ⊓ V ≤ L)
    (A : schemeDerivedCategory L.toScheme) :
    let W := U ⊓ V
    let hP : g ⁻¹ᵁ L ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ L) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let hT : g ⁻¹ᵁ W ≤ gk ⁻¹ᵁ (f ⁻¹ᵁ W) := by
      rw [← Scheme.Hom.comp_preimage, hgf]
    let iX : g ⁻¹ᵁ W ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let iK : f ⁻¹ᵁ W ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
    let _ξ := perfectOverlapNestedPullbackSquare gk iK iX hP hT
    let _κ := perfectOverlapCompositeLocalIso f gk g hgf L
    let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hT
    let _site : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ W)) ≌
        SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ W).toScheme.toRingedSpace) :=
      Scheme.Modules.overEquiv _
    (perfectOverlapApexEquivalence g pX pY b hg U V).functor.obj
        ((overlapSiteInverse (g ⁻¹ᵁ W)).mapDerivedCategory.obj
          ((derivedPullback r).obj ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
            ((derivedPullback (f ∣_ L)).obj A)))) ⟶
      (derivedPullback (pullback.fst (W.ι ≫ pY) b)).obj
        ((derivedPullback (Y.homOfLE hWL)).obj A) := by
  intro W hP hT iX iK ξ κ r site
  exact (perfectOverlapStageEquivalence g pX pY b hg U V).functor.map
        (site.mapDerivedCategory.counitIso.hom.app
          ((derivedPullback r).obj ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
            ((derivedPullback (f ∣_ L)).obj A)))) ≫
      (perfectOverlapStageEquivalence g pX pY b hg U V).functor.map
        (ξ.inv.app ((derivedPullback (f ∣_ L)).obj A) ≫
          (schemeOpenOverlapRestriction X iX).mapDerivedCategory.map (κ.hom.app A)) ≫
      (perfectOverlapStageObjectIso g pX pY b hg U V L hWL).hom.app A

/-- The site counit, nested restricted-square map, local composition comparison,
and fixed stage-object comparison, in that order. This is a real construction.
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: def-pc-perfect-overlap-composite-stage-map). -/
@[no_expose] noncomputable def perfectOverlapCompositeStageMap
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S)
    (b : C ⟶ S)
    (hg : IsPullback g pX pY b)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let W := U ⊓ V
  let _r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W)
    (by rw [← Scheme.Hom.comp_preimage, hgf])
  let data := transportDataOfComposite f gk g hgf U V A B E φU φV
  let F : Bool → schemeDerivedCategory (f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V).toScheme := fun a ↦
    if a then
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_right : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ V))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ V)).obj B)
    else
      (schemeOpenOverlapRestriction K
        (homOfLE (inf_le_left : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ≤ f ⁻¹ᵁ U))).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ U)).obj A)
  let apex := perfectOverlapApexEquivalence g pX pY b hg U V
  let _eW : SheafOfModules.{u}
      ((moduleRings X.toRingedSpace).over (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V)) ≌
      SheafOfModules.{u} (moduleRings (g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V).toScheme.toRingedSpace) :=
    Scheme.Modules.overEquiv _
  ∀ a : Bool, apex.functor.obj (data.d.toDiagram.HW.obj (F a)) ⟶
    (derivedPullback (pullback.fst (W.ι ≫ pY) b)).obj
      (if a then (derivedPullback (Y.homOfLE (inf_le_right : W ≤ V))).obj B
      else (derivedPullback (Y.homOfLE (inf_le_left : W ≤ U))).obj A) := by
  intro W r data F apex eW a
  cases a
  · exact perfectOverlapCompositeStageMapAt f gk g hgf pX pY b hg U V U inf_le_left A
  · exact perfectOverlapCompositeStageMapAt f gk g hgf pX pY b hg U V V inf_le_right B

/-- The site counit followed by the nested-square, local composition and stage-object maps.
Source: Stacks Project, Tags 08DW and 0D5S. Each factor is explicitly constructed.
(blueprint: def-pc-perfect-overlap-composite-stage-map). -/
theorem perfectOverlapCompositeStageMap_false
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S)
    (b : C ⟶ S)
    (hg : IsPullback g pX pY b)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let _W := U ⊓ V
  perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV false =
    perfectOverlapCompositeStageMapAt f gk g hgf pX pY b hg U V U inf_le_left A := by
  intro W
  rfl

/-- The site counit followed by the nested-square, local composition and stage-object maps.
Source: Stacks Project, Tags 08DW and 0D5S. Each factor is explicitly constructed.
(blueprint: def-pc-perfect-overlap-composite-stage-map). -/
theorem perfectOverlapCompositeStageMap_true
    {X Y K C S : Scheme.{u}}
    (f : K ⟶ Y) (gk : X ⟶ K) (g : X ⟶ Y) (hgf : gk ≫ f = g)
    (pX : X ⟶ C) (pY : Y ⟶ S)
    (b : C ⟶ S)
    (hg : IsPullback g pX pY b)
    (U V : Y.Opens)
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (E : schemeDerivedCategory X)
    (φU : (derivedPullback (g ∣_ U)).obj A ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ U)).mapDerivedCategory.obj E)
    (φV : (derivedPullback (g ∣_ V)).obj B ≅
      (schemeOpenRestriction X (g ⁻¹ᵁ V)).mapDerivedCategory.obj E) :
  let _W := U ⊓ V
  perfectOverlapCompositeStageMap f gk g hgf pX pY b hg U V A B E φU φV true =
    perfectOverlapCompositeStageMapAt f gk g hgf pX pY b hg U V V inf_le_right B := by
  intro W
  rfl

end AlgebraicGeometry

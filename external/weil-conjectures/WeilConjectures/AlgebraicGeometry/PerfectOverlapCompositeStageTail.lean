/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectOverlapCompositeStageMap

/-! # The tail after the composite stage-map counit -/

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

/-- The nested-square comparison, local composition and stage-object comparison,
without the site counit. Source: Stacks Project, Tags 08DW and 0D5S.
This is the explicit last three factors of the constructed stage map; the
intersection of inverse-image opens is used in its source interface.
(blueprint: def-pc-perfect-overlap-composite-stage-tail). -/
@[irreducible] noncomputable def perfectOverlapCompositeStageTailAt
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
  let iX : g ⁻¹ᵁ U ⊓ g ⁻¹ᵁ V ⟶ g ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let iK : f ⁻¹ᵁ U ⊓ f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ L := homOfLE (fun _ hx ↦ hWL hx)
  let _ξ := perfectOverlapNestedPullbackSquare gk iK iX hP hT
  let _κ := perfectOverlapCompositeLocalIso f gk g hgf L
  let r := gk.resLE (f ⁻¹ᵁ W) (g ⁻¹ᵁ W) hT
  (perfectOverlapStageEquivalence g pX pY b hg U V).functor.obj
      ((derivedPullback r).obj ((schemeOpenOverlapRestriction K iK).mapDerivedCategory.obj
        ((derivedPullback (f ∣_ L)).obj A))) ⟶
    (derivedPullback (pullback.fst (W.ι ≫ pY) b)).obj
      ((derivedPullback (Y.homOfLE hWL)).obj A) := by
  intro W hP hT iX iK ξ κ r
  exact (perfectOverlapStageEquivalence g pX pY b hg U V).functor.map
      (ξ.inv.app ((derivedPullback (f ∣_ L)).obj A) ≫
        (schemeOpenOverlapRestriction X iX).mapDerivedCategory.map (κ.hom.app A)) ≫
    (perfectOverlapStageObjectIso g pX pY b hg U V L hWL).hom.app A

end AlgebraicGeometry

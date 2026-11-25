/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Affine transitions between fibre products

Source: Stacks Project, Morphisms, Tags 01SD and 01SC, and Schemes, Tag 01KR
(blueprint: lem-weil-pbc-fibre-product-affine-transition).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The map between fibre products induced by three compatible affine comparison morphisms
is affine (Stacks Project, Tags 01SD, 01SC, 01KR).
(blueprint: lem-weil-pbc-fibre-product-affine-transition)

Proof:
1. The affine base comparison `h` is separated, by
   `lem-weil-pbc-affine-morphism-permanence` (Tag 01S7).
2. Factor the induced map through the fibre product of `X'` and `T'` over `S`.
   The first factor is a base change of the diagonal of `h`, hence a closed immersion by
   `lem-weil-pbc-fibre-product-change-of-base-closed-immersion` (Tag 01KR). It is affine by
   `lem-weil-pbc-closed-immersion-integral-separated-uc` (Tag 01SE).
3. The second factor is the product of `a` and `c` over `S`. It is a composite of base
   changes of these affine maps, hence affine by `lem-weil-pbc-fibre-product-map-affine`
   (Tags 01SD and 01SC).
4. The composite has the prescribed two projection maps, so the universal property
   `def-pc-fibre-product` identifies it with `pullback.map`. Affine composition
   `lem-weil-pbc-affine-composition` (Tag 01SC) gives the conclusion. -/
theorem isAffineHom_pullback_map
    {X' S' T' X S T : Scheme.{u}}
    (f' : X' ⟶ S') (g' : T' ⟶ S') (f : X ⟶ S) (g : T ⟶ S)
    (a : X' ⟶ X) (h : S' ⟶ S) (c : T' ⟶ T)
    (ha : f' ≫ h = a ≫ f) (hc : g' ≫ h = c ≫ g)
    [IsAffineHom a] [IsAffineHom h] [IsAffineHom c] :
    IsAffineHom (pullback.map f' g' f g a c h ha hc) := by
  let k := pullback.map (f' ≫ h) (g' ≫ h) f g a c (𝟙 S)
    ((Category.comp_id _).trans ha) ((Category.comp_id _).trans hc)
  have : IsAffineHom k :=
    MorphismProperty.pullbackMap (P := @IsAffineHom) inferInstance inferInstance ha hc
  have heq : pullback.map f' g' f g a c h ha hc = pullback.mapDesc f' g' h ≫ k := by
    ext <;> simp [k, pullback.mapDesc, pullback.map]
  rw [heq]
  infer_instance

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.Differentials

@[expose] public section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- The universal derivation gives a linear map from affine Kähler differentials to
sections of relative differentials.  The affine comparison constructs this map.
Source: Stacks Project, Tag 01UT; the map part of the affine calculation.
(blueprint: lem-sc-relative-differentials-affine-sections-map).
-/
theorem relativeDifferentials_affine_sections_map (f : X ⟶ S)
    (U : X.affineOpens) (V : S.affineOpens) (hUV : U.1 ≤ f ⁻¹ᵁ V.1) :
    ∃ e : CommRingCat.KaehlerDifferential (f.appLE V.1 U.1 hUV) →ₗ[Γ(X, U.1)]
        Γ(f.relativeDifferentials, U.1),
      ∀ a : Γ(X, U.1), e (CommRingCat.KaehlerDifferential.d a) =
        f.relativeDifferentialsDerivation.d (X := op U.1) a := by
  let D : (f.relativeDifferentials.val.obj (op U.1)).Derivation
      (f.appLE V.1 U.1 hUV) :=
    ModuleCat.Derivation.mk
      (fun a ↦ f.relativeDifferentialsDerivation.d (X := op U.1) a)
      (fun a b ↦ map_add _ a b)
      (fun a b ↦ f.relativeDifferentialsDerivation.d_mul a b)
      (fun a ↦ by
        rw [Scheme.Hom.appLE_eq_pullbackPresheafToPresheaf_app]
        exact PresheafOfModulesOfCommRing.Derivation'.d_app _ _)
  exact ⟨D.desc.hom, fun a ↦ D.desc_d a⟩

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData

/-! Degree-zero unit part of the normalized scalar-extension twist laws.

## References

* Stacks Project, Constructions, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

/-- The degree-zero fraction formula is the structural pullback map. -/
theorem scalarExtension_twist_unit
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    ∀ (U : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)),
      scalarExtensionTwistSection r θ 0 U
        (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) U s) =
        Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (r.app U s) := by
  intro U s
  let e := tensorPullbackSectionAdjunction r
  let φ : Scheme.Modules.unit (Proj 𝒜) ⟶ (pushforward r).obj (twist ℬ 0) :=
    unitToTwistZero ≫ e.unit.app (twist 𝒜 0) ≫ (pushforward r).map (θ 0).hom
  have hφ (t : Γ(Proj 𝒜, U)) :
      φ.app U t = scalarExtensionTwistSection r θ 0 U
        (Hom.app (unitToTwistZero (𝒜 := 𝒜)) U t) := by
    have he : (e.unit.app (twist 𝒜 0)).app U
        (Hom.app (unitToTwistZero (𝒜 := 𝒜)) U t) =
          tensorPullbackSection r (twist 𝒜 0) U
            (Hom.app (unitToTwistZero (𝒜 := 𝒜)) U t) :=
      (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction r)).1 _ _ _
    exact congrArg ((θ 0).hom.app (r ⁻¹ᵁ U)) he
  have h1 : scalarExtensionTwistSection r θ 0 U
      (Hom.app (unitToTwistZero (𝒜 := 𝒜)) U (1 : Γ(Proj 𝒜, U))) =
        Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (1 : Γ(Proj ℬ, r ⁻¹ᵁ U)) := by
    have hs : ∀ y : U,
        ((Hom.app (unitToTwistZero (𝒜 := 𝒜)) U (1 : Γ(Proj 𝒜, U))).1 y :
          Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) * Localization.mk (1 : A) 1 =
            Localization.mk (1 : A) 1 := by
      intro y
      simp [val_unitToTwistZero_app_apply,
        HomogeneousLocalization.degreePart.coe_zeroEquiv_apply,
        Localization.mk_one_eq_algebraMap]
    apply Subtype.ext
    funext x
    apply Subtype.ext
    have hx := hθ 0 0 0 1 1 (SetLike.one_mem_graded 𝒜)
      (SetLike.one_mem_graded 𝒜) (by simp) U (by simp) _ hs 1 x
    simpa [one_smul, val_unitToTwistZero_app_apply,
      HomogeneousLocalization.degreePart.coe_zeroEquiv_apply,
      Localization.mk_one_eq_algebraMap] using hx
  have hsource : (s • (1 : Γ(Proj 𝒜, U)) :
      Γ(Scheme.Modules.unit (Proj 𝒜), U)) = s := mul_one s
  have hlin := Hom.app_smul φ s (1 : Γ(Proj 𝒜, U))
  rw [hsource, hφ, hφ, h1] at hlin
  refine hlin.trans ?_
  change r.app U s • Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U)
    (1 : Γ(Proj ℬ, r ⁻¹ᵁ U)) = _
  rw [← Hom.app_smul]
  congr 1
  exact mul_one (r.app U s)

end AlgebraicGeometry.Proj

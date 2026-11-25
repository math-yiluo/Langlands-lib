/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistChartInjective
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistChartSurjective
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
/-! # The scalar-extension twist map on a complete standard chart

## References

* Stacks Project, Tag 01N2, clause (3), standard-open proof
* Tag 01MY, the map on localized graded modules
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The prescribed scalar-extension twist map is bijective on the whole standard chart. -/
theorem scalarExtension_twistMap_chart_bijective
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map ψ
      (HomogeneousIdeal.irrelevant 𝒜))
    (j : ℤ)
    (η : (tensorPullback (map ψ hψ)).obj (twist 𝒜 j) ⟶ twist ℬ j)
    (hη : ∀ (U : (Proj 𝒜).Opens) (s : Γ(twist 𝒜 j, U))
      (x : map ψ hψ ⁻¹ᵁ U),
      ((η.app (map ψ hψ ⁻¹ᵁ U)
        (tensorPullbackSection (map ψ hψ) (twist 𝒜 j) U s)).1 x :
          Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
        Localization.localRingHom _ _ ψ.toRingHom rfl (s.1 ⟨_, x.2⟩).val)
    (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n) :
    Function.Bijective (η.app (basicOpen ℬ (ψ f))) := by
  exact ⟨scalarExtension_twistMap_chart_injective 𝒜 ℬ β ψ hβψ hgraded hψ j η hη n f hf hn,
    scalarExtension_twistMap_chart_surjective 𝒜 ℬ β ψ hβψ hgraded hψ j η hη n f hf hn⟩

end AlgebraicGeometry.Proj

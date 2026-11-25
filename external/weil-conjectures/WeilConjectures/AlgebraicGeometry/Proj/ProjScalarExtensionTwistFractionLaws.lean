/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistIdentity
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistMultiplication
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistUniqueness
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistUnit

/-! # ProjScalarExtensionTwistFractionLaws

## References

* Stacks Project, Constructions, Tags 01N2, 01MY and 01MZ
* Stacks Project, Constructions, Tags 01MY, 01N2 and 01MZ
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- A normalized comparison has the uniqueness, product, unit and identity laws.
The homogeneous-section law is proved directly in the importing item, using denominator one. -/
theorem scalarExtension_twist_fraction_laws
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    (∀ θ' : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
        IsScalarExtensionTwistComparison ψ r θ' → θ' = θ) ∧
      (∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
        (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
        (v : Γ(twist 𝒜 (i + j), U)),
        (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
        ∀ x : r ⁻¹ᵁ U,
          ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          ((scalarExtensionTwistSection r θ i U s).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
          (scalarExtensionTwistSection r θ j U t).1 x) ∧
      (∀ (U : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)),
        scalarExtensionTwistSection r θ 0 U
          (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) U s) =
          Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (r.app U s)) ∧
(∀ ι : ∀ j : ℤ, (tensorPullback (𝟙 (Proj 𝒜))).obj (twist 𝒜 j) ≅ twist 𝒜 j,
        IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜)) ι →
        ∀ j : ℤ, ι j = (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) := by
  have huniq := scalarExtension_twist_uniqueness ψ r θ hθ
  have hmul := scalarExtension_twist_multiplication ψ r θ hθ
  have hunit := scalarExtension_twist_unit ψ r θ hθ
  have hid := scalarExtension_twist_identity (𝒜 := 𝒜)
  exact ⟨huniq, hmul, hunit, hid⟩

end AlgebraicGeometry.Proj

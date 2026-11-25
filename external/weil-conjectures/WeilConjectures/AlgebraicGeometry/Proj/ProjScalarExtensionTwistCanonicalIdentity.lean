/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistCanonicalSection

/-! Canonical identity normalization for Proj twisting sheaves.

## References

* Stacks Project, Tags 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/-- The section-normalized identity pullback comparison obeys the identity fraction rule. -/
theorem scalarExtension_twist_canonical_identity
    {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] :
    IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜))
      (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) := by
  intro j i k a b ha hb hik U hU s hs c x
  have hsec := scalarExtension_twist_canonical_section
    (𝒜 := 𝒜) j U s x
  have hden := hs ⟨x.1, x.2⟩
  change ((c • scalarExtensionTwistSection (𝟙 (Proj 𝒜))
      (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) j U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * Localization.mk b 1 =
    (c.1 x).val * Localization.mk a 1
  rw [show ((c • scalarExtensionTwistSection (𝟙 (Proj 𝒜))
      (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) j U s).1 x :
      Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
      (c.1 x).val * (s.1 ⟨x.1, x.2⟩ : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) by
        change (c.1 x).val *
          (scalarExtensionTwistSection (𝟙 (Proj 𝒜))
            (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) j U s).1 x = _
        rw [hsec]]
  rw [mul_assoc, hden]

end AlgebraicGeometry.Proj

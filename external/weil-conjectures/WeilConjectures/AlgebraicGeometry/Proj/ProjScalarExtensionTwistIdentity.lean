/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistUniqueness
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistCanonicalIdentity

/-! Identity part of the normalized scalar-extension twist laws. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

/- The identity comparison is fixed by its normalized fraction formula. -/
theorem scalarExtension_twist_identity
    {A : Type u} [CommRing A]
    {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] :
    ∀ ι : ∀ j : ℤ, (tensorPullback (𝟙 (Proj 𝒜))).obj (twist 𝒜 j) ≅ twist 𝒜 j,
      IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜)) ι →
      ∀ j : ℤ, ι j = (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j) := by
  intro ι hι j
  have h := scalarExtension_twist_uniqueness
    (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜)) ι hι
  have hc := h (fun j ↦ (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j))
    (scalarExtension_twist_canonical_identity (𝒜 := 𝒜))
  exact congrFun hc.symm j

end AlgebraicGeometry.Proj

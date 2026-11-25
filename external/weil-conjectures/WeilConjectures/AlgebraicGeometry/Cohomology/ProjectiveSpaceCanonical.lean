/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveSpaceTwist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical

/-!
# The top cohomology of the canonical module of projective space

Let `A` be a commutative ring and `ℙᵈ_A = ℙ(n; Spec A)` with `Fintype.card n = d + 1`, `d ≥ 1`.
The canonical module `ω = ⋀ᵈ Ω¹_{ℙ/A}` is isomorphic to `𝒪(-d-1)`
(`AlgebraicGeometry.ProjectiveSpace.canonicalModuleIsoTwist`), hence `Hᵈ(ℙᵈ_A, ω) ≅ A`.

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`)
-/

@[expose] public section

universe u

open CategoryTheory

noncomputable section

namespace AlgebraicGeometry.ProjectiveSpace

open Scheme.Modules

variable {n : Type u}

/-- **`Hᵈ(ℙᵈ_A, ω) ≅ A`**: for `d ≥ 1`, the top cohomology of the canonical module
`ω = ⋀ᵈ Ω¹_{ℙ/A}` of `ℙᵈ_A` is free of rank one over `A`, since `ω ≅ 𝒪(-d-1)`
(`canonicalModuleIsoTwist`) and `Hᵈ(ℙᵈ_A, 𝒪(-d-1)) ≅ A`
(`nonempty_H_twist_top_linearEquiv_self`).

(blueprint: `theorem-riemann-roch-coherent-serre-duality--2`) -/
theorem nonempty_H_canonicalModule_top_linearEquiv (A : Type u) [CommRing A] [Fintype n]
    {d : ℕ} (hn : Fintype.card n = d + 1) (hd : d ≠ 0) :
    letI := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
      (canonicalModule n (Spec (.of A)) d) d
    Nonempty ((canonicalModule n (Spec (.of A)) d).H d ≃ₗ[A] A) := by
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    (canonicalModule n (Spec (.of A)) d) d
  let := moduleHOfSpec (ℙ(n; Spec (.of A)) ↘ Spec (.of A))
    (twist n (Spec (.of A)) (-(d : ℤ) - 1)) d
  obtain ⟨f⟩ := nonempty_H_twist_top_linearEquiv_self (n := n) A hn hd
  let φ := H.mapLinearEquiv (canonicalModuleIsoTwist A (Fintype.equivFinOfCardEq hn)) d
  exact ⟨{ φ.toAddEquiv with map_smul' := fun a x ↦ φ.map_smul _ x } ≪≫ₗ f⟩

end AlgebraicGeometry.ProjectiveSpace

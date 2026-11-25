/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport

/-!
# Perfectness of compactly supported cohomology with finite coefficients

`AlgebraicGeometry.Etale.isPerfect_compactlySupportedGlobalSections`: for a finite ring `Λ` whose
exponent is invertible in the separably closed field `k` and `K ∈ Dctf(X, Λ)`, the complex
`RΓ_c(X, K)` is perfect. The point perfectness results built on it are in
`WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Finite

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {k : Type u} [Field k] [IsSepClosed k]
  [HasInvertibleExponent Λ (Spec (.of k))]
  {X : Scheme.{u}} (aX : X ⟶ Spec (.of k)) [LocallyOfFiniteType aX]
  [HasCompactification aX]

/-- Blueprint `lemma-perfect-complexes-geometric-point`: Finiteness: the global sections are perfect
at the point. This is also blueprint `lemma-perfect-complexes-geometric-point` (Point perfectness of
global sections), at the finite stage.

Also blueprint `lemma-perfect-complexes-geometric-point`: Compact-support perfectness (compactly
supported cohomology).

**`RΓ_c(X, K)` is perfect.** Let `Λ` be a finite ring whose exponent is invertible in the
separably closed field `k`, `X` separated of finite type over `k` and `K ∈ Dctf(X, Λ)`. Then
`RΓ_c(X, K)` is a perfect complex of `Λ`-modules: it is bounded with finite cohomology modules
and of finite Tor amplitude (`lemma-perfect-complexes-geometric-point`), hence perfect over the
Noetherian ring `Λ`. -/
theorem isPerfect_compactlySupportedGlobalSections
    (K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) :
    ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) aX).obj K).IsPerfect := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) aX
  obtain ⟨a, b, hab⟩ := isZero_compactlySupportedCohomology_of_lt Λ aX K hK
  refine _root_.DerivedCategory.isPerfect_of_finiteTorAmplitude ⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩
    (finite_compactlySupportedCohomology Λ aX K hK)
    (finiteTorAmplitude_compactlySupportedGlobalSections Λ aX K hK)
  · change _root_.DerivedCategory.IsGE _ a
    rw [_root_.DerivedCategory.isGE_iff]
    exact fun q hq ↦ hab q (Or.inl hq)
  · change _root_.DerivedCategory.IsLE _ b
    rw [_root_.DerivedCategory.isLE_iff]
    exact fun q hq ↦ hab q (Or.inr hq)

end Finite

end Etale

end AlgebraicGeometry

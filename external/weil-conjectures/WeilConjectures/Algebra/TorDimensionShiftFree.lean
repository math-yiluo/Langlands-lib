/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.Algebra.TorDimensionShiftNatural

/-!
# Dimension shifting for Tor along a free presentation

Source: Stacks Project, Algebra, proof of Tag 00S2, and Tags 00LY and 00LZ
(blueprint: lem-weil-pbc-tor-dimension-shift-free).
-/

@[expose] public section

universe u

namespace CategoryTheory

/-- Dimension shifting for Tor along `0 → K → F → M → 0`, with `F` free.
The objects `S.X₁`, `S.X₂`, `S.X₃` represent `K`, `F`, `M`, respectively,
and `S.f`, `S.g` represent the maps `j`, `p`. Tor is derived in its first variable.

Source: Stacks Project, Algebra, proof of Tag 00S2, and Tags 00LY and 00LZ
(blueprint: lem-weil-pbc-tor-dimension-shift-free).

1. Apply `theorem-finite-etale-covers-proper-henselian--2` to `0 → K → K → 0 → 0`
   with identity first map, obtaining an augmented free resolution `G` of `K`.
2. Splice this resolution with the given presentation: take `P₀ = F`,
   `Pₙ₊₁ = Gₙ`, first differential `jη`, and augmentation `p : F → M`.
   All terms are free (`def-weil-pbc-free-module`). Surjectivity of `η`
   gives `image (jη) = image j = kernel p`; injectivity of `j` gives
   `kernel (jη) = kernel η = image e₁`. All higher exactness conditions
   come from `G` (`def-weil-pbc-exact-sequence`). Thus `P` resolves `M`.
3. Compute Tor by these resolutions (`def-weil-pbc-tor-modules`, Tags 00LY,
   00LZ). For `i ≥ 1`, the terms and differentials around degree `i+1`
   of `P ⊗ N` agree with those around degree `i` of `G ⊗ N`:
   `Gᵢ₊₁ ⊗ N → Gᵢ ⊗ N → Gᵢ₋₁ ⊗ N`. Their cycles and boundaries,
   hence their homology modules, agree. Compose with the canonical resolution
   identifications to obtain the isomorphism. At `i = 1`, this identifies
   `Tor₂(M,N)` and `Tor₁(K,N)`, so one vanishes if and only if the other does.
   The comparison does not hold at `i = 0`, where the first differential is `jη`.
-/
theorem tor_dimension_shift_free
    {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    [Module.Free R S.X₂] (N : ModuleCat.{u} R) :
    (∀ (i : ℕ), 1 ≤ i →
      Nonempty ((((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N))) ∧
    (Limits.IsZero (((Tor' (ModuleCat.{u} R) 2).obj S.X₃).obj N) ↔
      Limits.IsZero (((Tor' (ModuleCat.{u} R) 1).obj S.X₁).obj N)) := by
  have hshift : ∀ i : ℕ, 1 ≤ i →
      Nonempty ((((Tor' (ModuleCat.{u} R) (i + 1)).obj S.X₃).obj N) ≅
        (((Tor' (ModuleCat.{u} R) i).obj S.X₁).obj N)) := by
    intro i hi
    obtain ⟨θ, _⟩ := tor_dimension_shift_natural S hS i hi
    exact ⟨θ N⟩
  refine ⟨hshift, ?_⟩
  obtain ⟨e⟩ := hshift 1 (by decide)
  exact ⟨fun h ↦ h.of_iso e.symm, fun h ↦ h.of_iso e⟩

end CategoryTheory

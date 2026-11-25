/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
public import Mathlib.CategoryTheory.Monoidal.Tor
import WeilConjectures.Algebra.TorDimensionShiftNatural

/-!
# Two-step dimension shifting for Tor

Source: blueprint, `theorem-riemann-roch-coherent-serre-duality`, proof; Stacks Project,
Algebra, proof of Lemma Tag 00S2 and Section Tag 00LY
(blueprint: lem-sc-p1-tor-dimension-shifting).
-/

@[expose] public section

universe u

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

/--
Two-step dimension shifting for Tor. The short exact sequence `E₀` is
`0 → K₁ → F₀ → M → 0` and `E₁` is `0 → K₂ → F₁ → K₁ → 0`, glued along
`hK₁ : E₁.X₃ = E₀.X₁`. The first clause is the isomorphism
`θ k : Tor₁(K₂,k) ≅ Tor₃(M,k)` of a family natural in the second module;
the second is the vanishing when `M` has projective dimension at most two.

Source: blueprint, `theorem-riemann-roch-coherent-serre-duality`, proof; Stacks Project, Algebra,
proof of Lemma Tag 00S2 (dimension shifting), and Section Tag 00LY (Tor).

Step 1. Apply `lem-sc-p1-tor-dimension-shift-natural` to `E₁` (`F₁` free)
with `i = 1`: isomorphisms `Tor₂(K₁,N) ≅ Tor₁(K₂,N)`, natural in `N`.
Step 2. Apply the same lemma to `E₀` (`F₀` free) with `i = 2`: isomorphisms
`Tor₃(M,N) ≅ Tor₂(K₁,N)`, natural in `N`. Compose the inverse of the Step 1
isomorphism with the inverse of this one (transporting along `hK₁`) to obtain
`θ N : Tor₁(K₂,N) ≅ Tor₃(M,N)`; inverses and composites of natural
isomorphisms are natural, which gives the naturality equation. Take `N = k`.
Step 3. If `M` has a projective resolution of length at most two, choose one
concentrated in degrees 0, 1, and 2. By `def-weil-pbc-tor-modules`, `Tor₃(M,k)`
is its third homology after tensoring with `k`; the degree-3 and degree-4 terms
vanish, so this homology is zero. Transport the vanishing across `θ k`.
(blueprint: lem-sc-p1-tor-dimension-shifting)
-/
theorem tor_dimension_shifting
    {S : Type u} [CommRing S] (k : ModuleCat.{u} S)
    (E₀ E₁ : ShortComplex (ModuleCat.{u} S))
    (hE₀ : E₀.ShortExact) (hE₁ : E₁.ShortExact) (hK₁ : E₁.X₃ = E₀.X₁)
    [Module.Free S E₀.X₂] [Module.Free S E₁.X₂] :
    (∃ θ : ∀ N : ModuleCat.{u} S,
        (((Tor' (ModuleCat.{u} S) 1).obj E₁.X₁).obj N) ≅
          (((Tor' (ModuleCat.{u} S) 3).obj E₀.X₃).obj N),
      ∀ (N N' : ModuleCat.{u} S) (g : N ⟶ N'),
        ((Tor' (ModuleCat.{u} S) 1).obj E₁.X₁).map g ≫ (θ N').hom =
          (θ N).hom ≫ ((Tor' (ModuleCat.{u} S) 3).obj E₀.X₃).map g) ∧
    (HasProjectiveDimensionLE E₀.X₃ 2 →
      IsZero (((Tor' (ModuleCat.{u} S) 1).obj E₁.X₁).obj k)) := by
  have h₁ := tor_dimension_shift_natural E₁ hE₁ 1 (by omega)
  rw [hK₁] at h₁
  obtain ⟨θ₁, hθ₁⟩ := h₁
  obtain ⟨θ₂, hθ₂⟩ := tor_dimension_shift_natural E₀ hE₀ 2 (by omega)
  let e₁ := NatIso.ofComponents θ₁ (fun {N N'} g ↦ hθ₁ N N' g)
  let e₂ := NatIso.ofComponents θ₂ (fun {N N'} g ↦ hθ₂ N N' g)
  let e := e₁.symm ≪≫ e₂.symm
  refine ⟨⟨(fun N ↦ e.app N), ?_⟩, ?_⟩
  · intro N N' g
    exact e.hom.naturality g
  · intro hpd
    have hpd₁ : HasProjectiveDimensionLT E₀.X₁ 2 :=
      hE₀.hasProjectiveDimensionLT_X₁ 2 inferInstance hpd
    have hpd₁' : HasProjectiveDimensionLT E₁.X₃ 2 := by
      rw [hK₁]
      exact hpd₁
    have hpd₂ : HasProjectiveDimensionLT E₁.X₁ 1 :=
      hE₁.hasProjectiveDimensionLT_X₁ 1 inferInstance hpd₁'
    let := hpd₂
    exact isZero_Tor'_succ_of_projective (ModuleCat.{u} S) E₁.X₁ k 0

end CategoryTheory

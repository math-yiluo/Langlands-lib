/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionHomologyInjective
import WeilConjectures.AlgebraicGeometry.DerivedTotalResolutionHomologySurjective

/-!
# Quasi-isomorphism from a good total resolution

Source: Stacks Project, `literature/stacks-project/homology.tex`,
Lemma 12.19.4 (Tag 09IZ), statement (blueprint: lem-pc-derived-total-resolution-quasi-iso).
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

namespace WeilConjectures

namespace DerivedTotalResolution

variable {R : Type u} [Ring R]

set_option linter.unusedVariables false in
/-- The total complex of an exact augmented resolution of cochain complexes is
quasi-isomorphic to the resolved complex (Stacks, Tag 09IZ).

The nonpositive horizontal columns of `K` are the resolution, with column
`-i` representing `Aᵢ`. Positive columns vanish. The component of `ε` on
column zero is the augmentation; its components on negative columns vanish.
Both augmented rows of terms and augmented rows of cycles are exact.
(blueprint: lem-pc-derived-total-resolution-quasi-iso)

Proof.
1. For every cochain degree `q`, splice the short exact sequences
   `0 → Ker(d^q_{Aᵢ}) → Aᵢ^q → Im(d^q_{Aᵢ}) → 0` with the exact augmented rows and the
   exact rows of cycles: the row `⋯ → Im(d^q_{A₁}) → Im(d^q_{A₀}) → Im(d^q_M) → 0` is
   exact. Splicing once more with `0 → Im(d^{q-1}_{Aᵢ}) → Ker(d^q_{Aᵢ}) → H^q(Aᵢ) → 0`
   gives the exact cohomology row `⋯ → H^q(A₁) → H^q(A₀) → H^q(M) → 0`.
2. On `Aᵢ^q` (column `-i`) the total differential is the horizontal map plus `(-1)^i`
   times the cochain differential. Write a total cocycle of degree `0` as a finite sum
   `x = xₙ + ⋯ + x₀` with `xᵢ ∈ Aᵢ^i`, `n` maximal. If `n > 0`, the cocycle equation
   makes `xₙ` a cycle whose class in `H^n(A_{n-1})` is zero; by step 1 it lifts to the
   class of a cycle `y ∈ Ker(d^n_{A_{n+1}})`. Subtracting the total boundary of `y`
   makes `xₙ = d z` with `z ∈ Aₙ^{n-1}`, and subtracting `±` the total boundary of `z`
   makes `xₙ = 0`. By finite support this terminates with `x = x₀`; every degree is
   alike, so `ε` is surjective on cohomology.
3. If two such cocycles `x₀, x₀' ∈ Ker(d^0_{A₀})` have images differing by `d_M m`,
   lift `m` to `a ∈ A₀^{-1}`; then `x₀ - x₀' - d a` is a cycle mapping to `0` in
   `Ker(d^0_M)`, hence the image of some `b ∈ Ker(d^0_{A₁})` by exactness of the row
   of cycles, and `x₀ - x₀'` is the total boundary of `b ± a`. So `ε` is injective on
   cohomology in every degree, i.e. `QuasiIso ε`.
-/
theorem total_resolution_quasiIso
    (M : CochainComplex (ModuleCat R) ℤ)
    (K : HomologicalComplex₂ (ModuleCat R) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ))
    [K.HasTotal (ComplexShape.up ℤ)]
    (ε : K.total (ComplexShape.up ℤ) ⟶ M)
    (a : K.X 0 ⟶ M)
    [∀ i, (K.total (ComplexShape.up ℤ)).HasHomology i]
    [∀ i, M.HasHomology i]
    [∀ p q, (K.X p).HasHomology q]
    (h_positive : ∀ p : ℤ, 0 < p → IsZero (K.X p))
    (h_augmentation_zero : ∀ q : ℤ,
      K.ιTotal (ComplexShape.up ℤ) 0 q q (by simp) ≫ ε.f q = a.f q)
    (h_augmentation : ∀ (p q n : ℤ)
      (hp : p < 0) (h : ComplexShape.π (ComplexShape.up ℤ)
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = n),
      K.ιTotal (ComplexShape.up ℤ) p q n h ≫ ε.f n = 0)
    (h_exact : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        ((K.d p (p + 1)).f q).hom
        ((K.d (p + 1) (p + 2)).f q).hom)
    (h_exact_zero : ∀ q : ℤ, Function.Exact
      ((K.d (-1) 0).f q).hom
      (a.f q).hom)
    (h_surjective : ∀ q : ℤ, Function.Surjective
      (a.f q).hom)
    (h_cycles : ∀ (p q : ℤ), p < -1 →
      Function.Exact
        (HomologicalComplex.cyclesMap (K.d p (p + 1)) q).hom
        (HomologicalComplex.cyclesMap (K.d (p + 1) (p + 2)) q).hom)
    (h_cycles_zero : ∀ q : ℤ, Function.Exact
      (HomologicalComplex.cyclesMap (K.d (-1) 0) q).hom
      (HomologicalComplex.cyclesMap a q).hom)
    (h_cycles_surjective : ∀ q : ℤ, Function.Surjective
      (HomologicalComplex.cyclesMap a q).hom) :
    QuasiIso ε := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ConcreteCategory.isIso_iff_bijective]
  exact ⟨total_resolution_homology_injective M K ε a n h_positive h_augmentation_zero
    h_augmentation h_exact h_exact_zero h_surjective h_cycles h_cycles_zero
    h_cycles_surjective,
    total_resolution_homology_surjective M K ε a n h_positive h_augmentation_zero
      h_cycles_surjective⟩

end DerivedTotalResolution

end WeilConjectures

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Localization.Away.Basic

import WeilConjectures.AlgebraicGeometry.EtaleAwayOfLocalizedCotangentVanishing
import WeilConjectures.AlgebraicGeometry.SmoothSectionDifferentialBasis
import WeilConjectures.RingTheory.SectionDifferentialBasisQuotient

/-! # Étale neighbourhoods along a smooth algebra section

Source: Stacks Project, More on Algebra, Tag 07M7, proof up to the final
idempotent localization.
(blueprint: lem-weil-pbc-smooth-section-etale-neighbourhoods).
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A section factors through an algebra that is étale near every prime containing
the section kernel. No global étale localization or quotient equivalence is asserted.
Source: Stacks Project, Tag 07M7, first paragraph and second paragraph up to
`C_f/JC_f = A/I` (with the source's kernel ideal denoted `N` here).
(blueprint: lem-weil-pbc-smooth-section-etale-neighbourhoods)

Proof:
1. Set `N = ker σ`. Every element of `A/J` comes from `A`, so `σ` is surjective
and `JB ≤ N`. The smooth conormal sequence identifies `P = N/(N² + JB)` with
`Ω[B/A] ⊗[B] (A/J)`, a finite projective `A/J`-module. For the image calculation,
write each `b` modulo `N` as the image of some `a ∈ A`; then
`bj - aj ∈ N²` for every `j ∈ J`.
2. Choose a finite projective complement `Kbar` with `P ⊕ Kbar` finite free.
Lift `Kbar` over an étale neighbourhood `A₁` inducing `A/J ≅ A₁/JA₁` by Tag 07M5.
Base change `B` and the section to `A₁`, and replace the result by its tensor product
with `Sym_{A₁}(K)`, where `K` is the lifted finite projective module. This algebra
is smooth by Tag 07M6, base change and composition. The augmentation retracts it
onto the base-changed original algebra. The new conormal module is `P ⊕ Kbar`:
the augmentation ideal modulo its square is the degree-one part `K`, and tensoring
with the quotient gives `Kbar`. Thus the new conormal module is finite free.
3. Lift its basis to `f₁,...,fₙ` in the section kernel and quotient by their generated
ideal to obtain a finitely presented algebra `E`. The section factors through `E`.
The smooth Jacobi-Zariski sequence identifies the kernel and cokernel of the conormal
map with `H₁(L_{E/A₁})` and `Ω[E/A₁]`. At primes containing the section kernel, the
localized differentials before quotienting have rank `n`, since their reduction has
the chosen basis. Nakayama makes the conormal map surjective. A surjection from the
free module of rank `n` onto its source, followed by that map and an identification
of its target with a free module of rank `n`, is a surjective endomorphism of a finite
module, hence bijective. The conormal map is therefore bijective at these primes,
so both cotangent obstructions vanish.
4. Set `C = E`. Precompose the quotient map with `B → B₁ → B₁ ⊗ Sym(K)`
and transport the section along `A₁/JA₁ ≅ A/J`; this gives `j` and `τ` with `τ ∘ j = σ`.
At every prime containing `ker τ`, step 3 and the cotangent criterion give a principal
localization of `C` étale over `A₁`. Composing with the étale map `A → A₁` makes
that same localization étale over `A`. No global localization has yet been chosen. -/
theorem exists_etale_neighbourhoods_of_smooth_section
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (σ : B →ₐ[A] A ⧸ J)
    (hB : Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    ∃ (C : CommAlgCat.{u} A) (j : B →ₐ[A] C) (τ : C →ₐ[A] A ⧸ J),
      τ.comp j = σ ∧
      ∀ q : PrimeSpectrum C, RingHom.ker τ.toRingHom ≤ q.asIdeal →
        ∃ s : C, s ∉ q.asIdeal ∧
          Etale (Spec.map (CommRingCat.ofHom
            ((algebraMap C (Localization.Away s)).comp (algebraMap A C)))) := by
  classical
  have : Algebra.Smooth A B := by
    exact RingHom.smooth_algebraMap.mp
      ((HasRingHomProperty.Spec_iff (P := @Smooth)).mp hB)
  obtain ⟨A₁, hA₁, D, instAD, instTower, hD, j, τ, hτj, hπ, n, f, hf, hb⟩ :=
    exists_smooth_section_differential_basis A B J σ
  let : Algebra A₁ D := instAD
  let : IsScalarTower A A₁ D := instTower
  let : Algebra.Smooth A₁ D := hD
  let η := τ.toRingHom.comp (algebraMap A₁ D)
  let : Algebra A₁ (A ⧸ J) := η.toAlgebra
  let σ₁ : D →ₐ[A₁] A ⧸ J :=
    { τ.toRingHom with commutes' := fun _ ↦ rfl }
  let a : Ideal D := Ideal.span (Set.range f)
  have ha : a ≤ RingHom.ker τ.toRingHom := by
    apply Ideal.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact hf i
  let C := D ⧸ a
  let τC : C →ₐ[A] A ⧸ J := Ideal.Quotient.liftₐ a τ (fun x hx ↦ ha hx)
  let jC : B →ₐ[A] C := (Ideal.Quotient.mkₐ A a).comp j
  have hτC : τC.toRingHom.comp (Ideal.Quotient.mk a) = σ₁.toRingHom := by
    rfl
  have : Algebra.FinitePresentation A₁ C :=
    Algebra.FinitePresentation.quotient (Submodule.fg_span (Set.finite_range f))
  refine ⟨CommAlgCat.of A C, jC, τC, ?_, ?_⟩
  · change τC.comp ((Ideal.Quotient.mkₐ A a).comp j) = σ
    rw [← AlgHom.comp_assoc]
    exact hτj
  · intro q hq
    obtain ⟨hH, hΩ⟩ :=
      Algebra.localized_cotangent_vanishes_of_section_differential_basis
        A₁ D (A ⧸ J) σ₁ hπ n f hf hb τC.toRingHom hτC q hq
    obtain ⟨s, hs, hEt⟩ :=
      exists_etale_away_of_localized_cotangent_vanishing (A := A₁) q.asIdeal hH hΩ
    refine ⟨s, hs, ?_⟩
    have : Etale (Spec.map (CommRingCat.ofHom (algebraMap A A₁))) := hA₁
    have : Etale (Spec.map
        (CommRingCat.ofHom (algebraMap A₁ (Localization.Away s)))) := hEt
    have hcomp := Etale.etale_comp
      (Spec.map (CommRingCat.ofHom (algebraMap A A₁)))
      (f := Spec.map (CommRingCat.ofHom (algebraMap A₁ (Localization.Away s))))
    convert hcomp using 1
    rw [← Spec.map_comp]
    congr 2
    ext x
    change algebraMap C (Localization.Away s) (algebraMap A C x) =
      algebraMap A₁ (Localization.Away s) (algebraMap A A₁ x)
    rw [← IsScalarTower.algebraMap_apply A C (Localization.Away s),
      ← IsScalarTower.algebraMap_apply A A₁ (Localization.Away s)]


end AlgebraicGeometry

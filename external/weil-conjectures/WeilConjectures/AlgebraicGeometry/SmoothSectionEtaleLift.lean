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
import WeilConjectures.AlgebraicGeometry.SmoothSectionEtaleNeighbourhoods
import WeilConjectures.AlgebraicGeometry.EtaleLocalizeUpstairs
import WeilConjectures.AlgebraicGeometry.EtaleSectionQuotientCutout

/-! # Sections of smooth algebras modulo an ideal lift over an étale neighbourhood

Source: Stacks Project, More on Algebra, Lemma Tag 07M7
(blueprint: lem-weil-pbc-smooth-section-etale-lift).
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-smooth-section-etale-lift)
Let `A` be a commutative ring, `J` an ideal, and `B` a smooth `A`-algebra.
Every `A`-algebra section of `B` to `A/J` lifts after an étale neighbourhood
of `A` inducing an isomorphism on the quotient.
Proof: Stacks Project, More on Algebra, Tag 07M7.
1. `exists_etale_neighbourhoods_of_smooth_section` performs the conormal, projective
   complement, symmetric algebra and basis quotient construction. It gives a
   factorization through an algebra étale near all primes of the section kernel.
2. `exists_isUnit_mk_and_etale_away` chooses a global étale localization
   with denominator invertible modulo that kernel. Map the unit through `kerLift`
   and use the localization universal property to extend the section.
3. `exists_localization_quotient_equiv_of_etale_section` cuts out the section by
   an idempotent after reduction modulo `J`. It gives a second localization `D`
   and an equivalence `t : D/JD ≃ₐ[A] A/J` extending the section.
4. The second localization is étale by composition. Take `α = t.symm` and compose
   `B → C → D`. Apply the injectivity of `t` to check the displayed lift equation.
The first construction is left as a named intermediate theorem; the localization,
quotient equivalence and compatibility argument here are fully proved.
-/
theorem exists_etale_lift_of_smooth
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (σ : B →ₐ[A] A ⧸ J)
    (hB : Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    ∃ (A' : CommAlgCat.{u} A),
      Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A A')).op) ∧
      ∃ (α : A ⧸ J →ₐ[A]
          A' ⧸ (J.map (algebraMap A A'))),
        Function.Bijective α ∧
        ∃ (tildeσ : B →ₐ[A] A'),
          Ideal.Quotient.mk (J.map (algebraMap A A')) ∘ tildeσ =
            α.toRingHom ∘ σ.toRingHom := by
  obtain ⟨E, jE, τE, hτE, hE⟩ := exists_etale_neighbourhoods_of_smooth_section A B J σ hB
  obtain ⟨h, hh, hEt⟩ := exists_isUnit_mk_and_etale_away
    (algebraMap A E) (RingHom.ker τE.toRingHom) hE
  have hhτ : IsUnit (τE h) := by
    exact hh.map (RingHom.kerLift τE.toRingHom)
  let C := Localization.Away h
  let τ : C →ₐ[A] A ⧸ J := IsLocalization.Away.liftAlgHom h hhτ
  let j : B →ₐ[A] C := (IsScalarTower.toAlgHom A E C).comp jE
  have hτ : τ.comp j = σ := by
    ext b
    change IsLocalization.Away.lift h hhτ (algebraMap E C (jE b)) = σ b
    rw [IsLocalization.Away.lift_eq]
    exact DFunLike.congr_fun hτE b
  have hC : Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op) := by
    rw [IsScalarTower.algebraMap_eq A E C]
    exact hEt
  obtain ⟨g, t, ht⟩ := exists_localization_quotient_equiv_of_etale_section A C J τ hC
  let D := Localization.Away g
  have : Algebra.Etale A C :=
    (RingHom.etale_algebraMap).mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hC)
  have : Algebra.Etale A D := Algebra.Etale.comp A C D
  have hD : Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A D)).op) :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let tildeσ : B →ₐ[A] D := (IsScalarTower.toAlgHom A C D).comp j
  refine ⟨CommAlgCat.of A D, hD, t.symm.toAlgHom, t.symm.bijective, tildeσ, ?_⟩
  funext b
  apply t.injective
  change t (Ideal.Quotient.mk _ (algebraMap C D (j b))) = t (t.symm (σ b))
  rw [ht, t.apply_symm_apply]
  exact DFunLike.congr_fun hτ b

end AlgebraicGeometry

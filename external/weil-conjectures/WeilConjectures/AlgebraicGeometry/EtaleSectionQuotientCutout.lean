/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.EtaleSectionIdempotentSplitting

/-! # Cutting out a section modulo an ideal from an étale algebra

Source: Stacks Project, More on Algebra, Tag 07M7, last paragraph;
Algebra, Tags 00U7 and 00U8.
(blueprint: lem-weil-pbc-etale-section-quotient-cutout).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- An étale algebra mapping to `A/J` has a principal localization whose quotient
is `A/J`, with the equivalence extending the given map.
Source: Stacks Project, Tag 07M7, last paragraph, with Tags 00U7 and 00U8.
(blueprint: lem-weil-pbc-etale-section-quotient-cutout)

Proof: put `I = JC` and `S = C/I`. The map `τ` kills `I`, hence descends to an
`A/J`-algebra section `s`. Base change preserves étaleness, so `S` is étale over
`A/J`. Apply the idempotent splitting theorem to obtain `e` and an equivalence
`S[1/e] ≃ A/J` extending `s`. Choose a preimage `g` of `e` in `C`.
The quotient of `C[1/g]` by `IC[1/g]` is a localization of `S` at `e`, since
localization commutes with quotients. Uniqueness of localization identifies it
with `S[1/e]`. Compose that equivalence with the section equivalence. Finally
`IC[1/g] = JC[1/g]` by transitivity of ideal extension. The composite on each
`c ∈ C` is `s(c mod I) = τ(c)`, as required. -/
theorem exists_localization_quotient_equiv_of_etale_section
    (A C : Type u) [CommRing A] [CommRing C] [Algebra A C]
    (J : Ideal A) (τ : C →ₐ[A] A ⧸ J)
    (hC : Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A C)).op)) :
    ∃ (g : C) (t :
      (Localization.Away g ⧸ (J.map (algebraMap A (Localization.Away g)))) ≃ₐ[A] (A ⧸ J)),
      ∀ c : C, t (Ideal.Quotient.mk _
        (algebraMap C (Localization.Away g) c)) = τ c := by
  have : Algebra.Etale A C :=
    (RingHom.etale_algebraMap).mp
      ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hC)
  let I := J.map (algebraMap A C)
  let S := C ⧸ I
  have hI : ∀ c ∈ I, τ c = 0 := by
    intro c hc
    have h : J ≤ (RingHom.ker τ.toRingHom).comap (algebraMap A C) := by
      intro a ha
      change τ (algebraMap A C a) = 0
      rw [τ.commutes]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr ha
    exact (Ideal.map_le_iff_le_comap.mpr h) hc
  let sA : S →ₐ[A] A ⧸ J := Ideal.Quotient.liftₐ I τ hI
  let s : S →ₐ[A ⧸ J] A ⧸ J :=
    AlgHom.extendScalarsOfSurjective Ideal.Quotient.mk_surjective sA
  have : Algebra.Etale (A ⧸ J) S :=
    Algebra.Etale.of_equiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J).symm
  obtain ⟨e, he, hse, hker, hprod, ψ, hψ⟩ :=
    Algebra.Etale.exists_idempotent_splitting_of_algHom s
  obtain ⟨g, hg⟩ := Ideal.Quotient.mk_surjective e
  let D := Localization.Away g
  let T := D ⧸ I.map (algebraMap C D)
  have : IsLocalization.Away e T := by
    subst e
    change IsLocalization (Submonoid.powers ((algebraMap C S) g)) T
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization
        (Algebra.algebraMapSubmonoid S (Submonoid.powers g)) T)
  have : IsScalarTower A S T := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let E := (IsLocalization.algEquiv (Submonoid.powers e) T
    (Localization.Away e)).restrictScalars A
  let t := E.trans (ψ.restrictScalars A)
  have hK : I.map (algebraMap C D) = J.map (algebraMap A D) := by
    dsimp [I]
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq A C D]
  let t' := (Ideal.quotientEquivAlgOfEq A hK.symm).trans t
  refine ⟨g, t', ?_⟩
  intro c
  change t (Ideal.quotientEquivAlgOfEq A hK.symm
    (Ideal.Quotient.mk _ (algebraMap C D c))) = τ c
  rw [Ideal.quotientEquivAlgOfEq_mk]
  change ψ (E (algebraMap S T (Ideal.Quotient.mk I c))) = τ c
  change ψ ((IsLocalization.algEquiv (Submonoid.powers e) T
    (Localization.Away e)) (algebraMap S T (Ideal.Quotient.mk I c))) = τ c
  rw [(IsLocalization.algEquiv (Submonoid.powers e) T
    (Localization.Away e)).commutes]
  exact hψ (Ideal.Quotient.mk I c)

end AlgebraicGeometry

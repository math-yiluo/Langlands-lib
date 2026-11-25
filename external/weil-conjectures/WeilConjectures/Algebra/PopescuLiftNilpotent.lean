/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.Algebra.IndSmoothQuotientCompatibility
import WeilConjectures.RingTheory.FilteredColimitOfFactorization
import WeilConjectures.RingTheory.PopescuLiftOnce
import WeilConjectures.RingTheory.PopescuLiftTwice

/-!
# Lifting ind-smoothness across nilpotent thickenings

Source: Stacks Project, Smoothing Ring Maps, Proposition Tag 07CM
(blueprint: lem-weil-pbc-popescu-lift-nilpotent).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace Algebra

private theorem lift_square_zero
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : I ^ 2 = ⊥)
    (hΛ : ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
      (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ)) :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} R ↦ Smooth R C) (CommAlgCat.of R Λ) := by
  classical
  let E : Set (CommAlgCat.{max u v} R) := {B | Smooth R B}
  have hfp : ∀ B ∈ E, FinitePresentation R B := by
    intro B hB
    let : Smooth R B := hB
    infer_instance
  have hfactor : ∀ (A : CommAlgCat.{max u v} R), FinitePresentation R A →
      ∀ (φ : A ⟶ CommAlgCat.of R Λ), ∃ B ∈ E,
        ∃ (ψ : A ⟶ B) (χ : B ⟶ CommAlgCat.of R Λ), ψ ≫ χ = φ := by
    intro A hA φ
    let := hA
    obtain ⟨B, hB, aB, hsB, J, hJfg, hJI, ψ, χ, hχψ⟩ :=
      exists_smooth_quotient_factorization R Λ I hI hΛ A φ.hom
    let := hB
    let := aB
    let := hsB
    let q := Ideal.Quotient.mkₐ R J
    have hχJ : J ≤ RingHom.ker (χ.comp q) := by
      intro x hx
      change χ (q x) = 0
      have hx0 : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
      rw [hx0, map_zero]
    obtain ⟨B', hB', aB', hsB', α, β, hαJ, hβα⟩ :=
      exists_smooth_factorization_killing_ideal R Λ I hI hΛ hflat B
        (χ.comp q) J hJfg hJI hχJ
    let := hB'
    let := aB'
    let αbar : B ⧸ J →ₐ[R] B' := Ideal.Quotient.liftₐ J α (fun x hx ↦ hαJ hx)
    have hβαbar : β.comp αbar = χ := by
      apply Ideal.Quotient.algHom_ext
      simpa only [αbar, q, AlgHom.comp_assoc, Ideal.Quotient.liftₐ_comp] using hβα
    refine ⟨CommAlgCat.of R B', hsB', CommAlgCat.ofHom (αbar.comp ψ),
      CommAlgCat.ofHom β, ?_⟩
    apply CommAlgCat.hom_ext
    change β.comp (αbar.comp ψ) = φ.hom
    rw [← AlgHom.comp_assoc, hβαbar, hχψ]
  obtain ⟨J, cJ, fJ, D, ι, hD, ⟨hc⟩⟩ :=
    CommAlgCat.exists_filtered_colimit_of_factorization R (CommAlgCat.of R Λ) E hfp hfactor
  exact ⟨J, cJ, fJ, ⟨D, ι, hc⟩, hD⟩

/-- If `R → Λ` is flat, `I ⊆ R` is nilpotent and `Λ / IΛ` is a filtered colimit of smooth
`R / I`-algebras, then `Λ` is a filtered colimit of smooth `R`-algebras.

Source: Stacks Project, Smoothing Ring Maps, Proposition Tag 07CM
(blueprint: lem-weil-pbc-popescu-lift-nilpotent).

Proof (the four steps of the node):
1. Square-zero case, criterion: for an ideal `K` with `K² = 0`, `Λ / KΛ` ind-smooth over
   `R / K` and `R → Λ` flat, by lem-weil-pbc-factorization-criterion-filtered-colimit
   (Algebra 07C3) applied to the set of smooth `R`-algebras that are quotients of finite
   polynomial rings, it suffices to factor every map `φ : A → Λ` from a finitely presented
   `R`-algebra through a smooth `R`-algebra.
2. Square-zero case, lift once: lem-weil-pbc-popescu-lift-once (07CK) factors `φ` as
   `A → B / J → Λ` with `B` smooth and `J ⊆ KB` finitely generated.
3. Square-zero case, lift twice: lem-weil-pbc-popescu-lift-twice (07CL), using flatness,
   gives `α : B → B'`, `β : B' → Λ` with `B'` smooth, `α(J) = 0` and `β ∘ α = (B → Λ)`;
   `α` factors through `B / J`, and `A → B / J → B' → Λ` is `φ`.
4. Induction on `n` with `I ^ n = 0`: `n = 1` is hypothesis (2); for `n ≥ 2` put
   `K = I ^ (n - 1)` (square zero); `R / K → Λ / KΛ` is flat by
   lem-weil-pbc-tensor-quotient-base-change and lem-weil-pbc-flat-module-base-change, its
   reduction by `I / K` is `Λ / IΛ`, so by induction `Λ / KΛ` is ind-smooth over `R / K`,
   and steps 1-3 for `K` conclude. -/
theorem popescu_lift_nilpotent
    (R : Type u) [CommRing R] (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ]
    (I : Ideal R) (hI : ∃ n : ℕ, 1 ≤ n ∧ I ^ n = ⊥)
    (hΛ :
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))))
    (hflat : RingHom.Flat (algebraMap R Λ)) :
    ObjectProperty.ind.{max u v}
      (fun C : CommAlgCat.{max u v} R ↦ Smooth R C) (CommAlgCat.of R Λ) := by
  obtain ⟨n, hn, hIn⟩ := hI
  have lift_power : ∀ (n : ℕ) (R : Type u) [CommRing R]
      (Λ : Type (max u v)) [CommRing Λ] [Algebra R Λ] (I : Ideal R),
      1 ≤ n → I ^ n = ⊥ →
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} (R ⧸ I) ↦ Smooth (R ⧸ I) C)
        (CommAlgCat.of (R ⧸ I) (Λ ⧸ I.map (algebraMap R Λ))) →
      RingHom.Flat (algebraMap R Λ) →
      ObjectProperty.ind.{max u v}
        (fun C : CommAlgCat.{max u v} R ↦ Smooth R C) (CommAlgCat.of R Λ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R _ Λ _ _ I hn hIn hΛ hflat
      by_cases hsmall : n ≤ 2
      · have hI2 : I ^ 2 = ⊥ := by
          apply le_bot_iff.mp
          exact (Ideal.pow_le_pow_right hsmall).trans (le_of_eq hIn)
        exact lift_square_zero R Λ I hI2 hΛ hflat
      · let m := n - 1
        have hm : 1 ≤ m := by omega
        have hmn : m < n := by omega
        let K := I ^ m
        have hKI : K ≤ I := Ideal.pow_le_self (by omega)
        have hK2 : K ^ 2 = ⊥ := by
          apply le_bot_iff.mp
          rw [show K ^ 2 = I ^ (m * 2) from (pow_mul I m 2).symm]
          exact (Ideal.pow_le_pow_right (by omega : n ≤ m * 2)).trans (le_of_eq hIn)
        let R' := R ⧸ K
        let Λ' := Λ ⧸ K.map (algebraMap R Λ)
        let I' : Ideal R' := I.map (Ideal.Quotient.mk K)
        have hI' : I' ^ m = ⊥ := by
          rw [← Ideal.map_pow]
          exact (Ideal.map_eq_bot_iff_le_ker _).mpr (by
            rw [Ideal.mk_ker])
        have hΛ' := ind_smooth_quotient_compatibility R Λ I K hKI hΛ
        have hflat' : RingHom.Flat (algebraMap R' Λ') := by
          have : Module.Flat R Λ := RingHom.flat_algebraMap_iff.mp hflat
          exact RingHom.flat_algebraMap_iff.mpr
            (Module.Flat.of_linearEquiv
              (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Λ K).toLinearEquiv)
        have hquot := ih m hmn R' Λ' I' hm hI' hΛ' hflat'
        exact lift_square_zero R Λ K hK2 hquot hflat
  exact lift_power n R Λ I hn hIn hΛ hflat

end Algebra

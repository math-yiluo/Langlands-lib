/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.RingHom.Finite
import WeilConjectures.FieldTheory.PowerInBaseAfterLocalization
import WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism

/-!
# Spreading purely inseparable factors

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
Stacks Project, Tags 00GQ, 0BR5, 01S4 and 04DF
(blueprint: lem-weil-pbc-spread-purely-inseparable-factors).
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry

-- The tensor map is the localization of the finite injective map A' → E.
private theorem localized_integral_injective
    (A A' E : Type u) [CommRing A] [CommRing A'] [CommRing E]
    [Algebra A A'] [Algebra A' E] [Algebra A E] [IsScalarTower A A' E]
    [Module.Finite A' E] (s : A) (hinj : Function.Injective (algebraMap A' E)) :
    let f := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
      (AlgHom.id A (Localization.Away s))).toRingHom
    f.IsIntegral ∧ Function.Injective f := by
  let B := Localization.Away s
  let f := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
    (AlgHom.id A B)).toRingHom
  have : IsLocalization.Away ((algebraMap A' E) (algebraMap A A' s))
      (E ⊗[A] B) := by
    rw [← IsScalarTower.algebraMap_apply]
    infer_instance
  have hf : f = IsLocalization.Away.map (A' ⊗[A] B) (E ⊗[A] B)
      (algebraMap A' E) (algebraMap A A' s) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A A' s))
    ext a
    simp [f, IsLocalization.Away.map]
  have hfin := RingHom.localization_away_map_finite A' E (A' ⊗[A] B) (E ⊗[A] B)
    (algebraMap A' E) (algebraMap A A' s) (RingHom.finite_algebraMap.mpr inferInstance)
  change f.IsIntegral ∧ Function.Injective f
  refine ⟨hf ▸ hfin.to_isIntegral, ?_⟩
  rw [hf]
  exact IsLocalization.map_injective_of_injective
    (Submonoid.powers (algebraMap A A' s)) (A' ⊗[A] B) (E ⊗[A] B) hinj

-- Test universal injectivity on field-valued points. The denominator t is already a unit
-- after inverting s, so the two field points extend to E ⊗[A'] A'[1/t].
private theorem universallyInjective_of_localized_powers
    (A A' E : Type u) (K' : Type v)
    [CommRing A] [CommRing A'] [IsDomain A'] [CommRing E]
    [Algebra A A'] [Algebra A' E] [Algebra A E] [IsScalarTower A A' E]
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    (s : A) (t : A') (hdvd : t ∣ algebraMap A A' s)
    (hzero : CharZero K' → Function.Surjective
      (Algebra.TensorProduct.includeRight (R := A') (A := E)
        (B := Localization.Away t)))
    (hpos : ∀ p : ℕ, Nat.Prime p → CharP K' p →
      ∀ x : E ⊗[A'] Localization.Away t, ∃ n : ℕ, ∃ a : Localization.Away t,
        Algebra.TensorProduct.includeRight (R := A') (A := E) a = x ^ (p ^ n)) :
    UniversallyInjective (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
        (AlgHom.id A (Localization.Away s))).toRingHom)) := by
  let B := Localization.Away s
  let R := A' ⊗[A] B
  let S := E ⊗[A] B
  let f : R →+* S := (Algebra.TensorProduct.map
    (IsScalarTower.toAlgHom A A' E) (AlgHom.id A B)).toRingHom
  have ht : IsUnit (algebraMap A' R t) :=
    IsLocalization.Away.isUnit_of_dvd (algebraMap A A' s) hdvd
  refine ((tfae_universallyInjective _).out 2 1).mp ?_
  intro Ω _ g₁ g₂ hg
  rw [← Spec.map_preimage g₁, ← Spec.map_preimage g₂] at hg ⊢
  simp only [← Spec.map_comp] at hg
  have h := congrArg CommRingCat.Hom.hom (Spec.map_injective hg)
  let a₁ : S →+* Ω := (Spec.preimage g₁).hom
  let a₂ : S →+* Ω := (Spec.preimage g₂).hom
  have heq : a₁.comp f = a₂.comp f := h
  have hf (x : A') : f (algebraMap A' R x) =
      algebraMap E S (algebraMap A' E x) := by
    change f (x ⊗ₜ[A] 1) = algebraMap A' E x ⊗ₜ[A] 1
    rfl
  have hu₁ : IsUnit ((a₁.comp (algebraMap E S)) (algebraMap A' E t)) := by
    simpa only [RingHom.comp_apply, ← hf] using ht.map (a₁.comp f)
  have hu₂ : IsUnit ((a₂.comp (algebraMap E S)) (algebraMap A' E t)) := by
    simpa only [RingHom.comp_apply, ← hf] using ht.map (a₂.comp f)
  let b₁ : E ⊗[A'] Localization.Away t →+* Ω :=
    IsLocalization.Away.lift (algebraMap A' E t) hu₁
  let b₂ : E ⊗[A'] Localization.Away t →+* Ω :=
    IsLocalization.Away.lift (algebraMap A' E t) hu₂
  let inc : Localization.Away t →+* E ⊗[A'] Localization.Away t :=
    Algebra.TensorProduct.includeRight.toRingHom
  have hb : b₁.comp inc = b₂.comp inc := by
    apply IsLocalization.ringHom_ext (Submonoid.powers t)
    ext x
    have hh := congrArg (fun k : R →+* Ω ↦ k (algebraMap A' R x)) heq
    change b₁ (1 ⊗ₜ[A'] algebraMap A' (Localization.Away t) x) =
      b₂ (1 ⊗ₜ[A'] algebraMap A' (Localization.Away t) x)
    rw [← Algebra.TensorProduct.algebraMap_apply']
    change b₁ (algebraMap E _ (algebraMap A' E x)) =
      b₂ (algebraMap E _ (algebraMap A' E x))
    dsimp only [b₁, b₂]
    rw [IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq]
    simpa only [RingHom.comp_apply, hf] using hh
  have hbb : b₁ = b₂ := by
    rcases CharP.exists K' with ⟨p, hp⟩
    let : CharP K' p := hp
    rcases CharP.char_is_prime_or_zero K' p with hpprime | rfl
    · have : CharP A' p := (algebraMap A' K').charP
        (IsFractionRing.injective A' K') p
      have : CharP Ω p := CharP.of_ringHom_of_ne_zero
        ((a₁.comp (algebraMap E S)).comp (algebraMap A' E)) p hpprime.ne_zero
      have : Fact (Nat.Prime p) := ⟨hpprime⟩
      have : ExpChar Ω p := inferInstance
      apply RingHom.ext
      intro x
      obtain ⟨n, a, ha⟩ := hpos p hpprime hp x
      have hh := congrArg (fun k : Localization.Away t →+* Ω ↦ k a) hb
      apply iterateFrobenius_inj Ω p n
      change b₁ (Algebra.TensorProduct.includeRight a) =
        b₂ (Algebra.TensorProduct.includeRight a) at hh
      simpa only [ha, map_pow, iterateFrobenius_def] using hh
    · have : CharZero K' := CharP.charP_to_charZero K'
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := hzero inferInstance x
      exact congrArg (fun k : Localization.Away t →+* Ω ↦ k a) hb
  have ha : a₁ = a₂ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (algebraMap A E s))
    ext x
    have hh := congrArg (fun k : E ⊗[A'] Localization.Away t →+* Ω ↦
      k (algebraMap E _ x)) hbb
    simpa only [b₁, b₂, IsLocalization.Away.lift_eq, RingHom.comp_apply] using hh
  congr 1
  exact CommRingCat.hom_ext ha

/-- A finite domain algebra with a finite purely inseparable extension of fraction fields
becomes surjective and radicial, hence a universal homeomorphism, after a principal localization
of the original base. The tensor-product map is induced by `A' → E` and the identity of `A[1/s]`.
The scalar towers express that the extension of fraction fields is the induced one.

Source: smooth purity blueprint, `sk-prop-sf-cbc`, proof of
`lem-weil-pbc-finite-pushforward-generic-constructible`, finite-algebra calculation;
Stacks Project, Tags 00GQ, 0BR5, 01S4 and 04DF
(blueprint: lem-weil-pbc-spread-purely-inseparable-factors).

Proof:
1. Finiteness makes `E` integral over `A'`. The compatible fraction-field maps make
   `A' → E` injective. After localization, lying over
   (`lem-weil-pbc-integral-injective-lying-over`, Tag 00GQ) proves surjectivity on spectra.
2. The finite algebra `A'` is Noetherian. Apply
   `lem-weil-pbc-power-in-base-after-localization` to obtain a nonzero `s' : A'`.
   Choose a monic equation for `s'` over `A` of minimal degree. Its constant term `s`
   is nonzero, since `A'` is a domain, and is divisible by `s'` in `A'`.
   Thus localizing at `s : A` also inverts `s'`, and the power property persists.
   In characteristic zero the localized rings coincide. In characteristic `p > 0`,
   each element has a `p^n`-th power in the base. Two primes over the same base prime
   therefore coincide, and quotients of ring elements in the residue fields also have
   a `p^n`-th power in the base residue field. The residue extensions are purely inseparable.
   Hence the map is radicial, equivalently universally injective
   (`def-weil-radicial-morphism`, Tag 01S4).
3. The localized map is integral, radicial and surjective. Apply
   `lem-pc-integral-radicial-surjective-universal-homeomorphism` (Tag 04DF)
   to obtain the universal-homeomorphism conclusion. -/
theorem exists_spread_purely_inseparable_factors
    (A A' E : Type u) (K : Type v) (K' : Type w) (L : Type z)
    [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [CommRing A'] [IsDomain A'] [Algebra A A'] [Module.Finite A A']
    [Etale (Spec.map (CommRingCat.ofHom (algebraMap A A')))]
    [CommRing E] [IsDomain E] [Algebra A' E] [Module.Finite A' E]
    [Algebra A E] [IsScalarTower A A' E]
    [Field K] [Algebra A K] [IsFractionRing A K]
    [Field K'] [Algebra A' K'] [IsFractionRing A' K']
    [Field L] [Algebra E L] [IsFractionRing E L]
    [Algebra K' L] [Algebra A' L]
    [IsScalarTower A' E L] [IsScalarTower A' K' L]
    [Module.Finite K' L] [IsPurelyInseparable K' L] :
    ∃ s : A, s ≠ 0 ∧
      Surjective (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) ∧
      UniversallyInjective (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) ∧
      (topologically IsHomeomorph).universally (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
          (AlgHom.id A (Localization.Away s))).toRingHom)) := by
  have : IsNoetherianRing A' := IsNoetherianRing.of_finite A A'
  obtain ⟨t, ht, hzero, hpos⟩ := RingTheory.power_in_base_after_localization A' K' E L
  obtain ⟨s, hs, hdvd⟩ :=
    (Algebra.IsIntegral.isIntegral (R := A) t).isAlgebraic.exists_nonzero_dvd
      (mem_nonZeroDivisors_iff_ne_zero.mpr ht)
  have hinj : Function.Injective (algebraMap A' E) := by
    intro x y hxy
    apply IsFractionRing.injective A' K'
    apply (algebraMap K' L).injective
    simpa only [← IsScalarTower.algebraMap_apply] using congrArg (algebraMap E L) hxy
  let f := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom A A' E)
      (AlgHom.id A (Localization.Away s))).toRingHom)
  obtain ⟨hi, hinj'⟩ := localized_integral_injective A A' E s hinj
  have : IsIntegralHom f := IsIntegralHom.SpecMap_iff.mpr hi
  have hsurj : Surjective f := ⟨hi.comap_surjective hinj'⟩
  have huinj : UniversallyInjective f :=
    universallyInjective_of_localized_powers A A' E K' s t hdvd hzero hpos
  have : IsUniversalHomeomorphism f := ⟨⟩
  refine ⟨s, hs, hsurj, huinj, ?_⟩
  exact @isUniversalHomeomorphism_le_universally_isHomeomorph _ _ f inferInstance

end AlgebraicGeometry

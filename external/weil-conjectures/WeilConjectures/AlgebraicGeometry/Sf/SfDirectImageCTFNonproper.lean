/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.DirectImage

/-!
# Direct image and finite Tor amplitude without properness
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Etale

attribute [local irreducible] derivedTensor

private theorem hasTorAmplitudeIn_iff_torAmplitudeIn
    (Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u}) (a b : ℤ)
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    DerivedCategory.hasTorAmplitudeIn Λ T a b K ↔
      DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} Λ) T a b K := by
  constructor
  · intro h F
    constructor
    · apply (_root_.DerivedCategory.isGE_iff _ a).2
      intro q hq
      simpa only [derivedTensor, MonoidalCategory.curriedTensor_obj_obj] using h F q (.inl hq)
    · apply (_root_.DerivedCategory.isLE_iff _ b).2
      intro q hq
      simpa only [derivedTensor, MonoidalCategory.curriedTensor_obj_obj] using h F q (.inr hq)
  · intro h F q hq
    rcases hq with hq | hq
    · simpa only [derivedTensor, MonoidalCategory.curriedTensor_obj_obj] using
        (_root_.DerivedCategory.isGE_iff _ a).1 (h F).1 q hq
    · simpa only [derivedTensor, MonoidalCategory.curriedTensor_obj_obj] using
        (_root_.DerivedCategory.isLE_iff _ b).1 (h F).2 q hq

/-- For finite coefficients over the fixed algebraic closure of a finite field, a separated
finite-type direct image preserves bounded constructibility and increases a Tor interval by at
most twice the source dimension.  No properness or compactification is assumed.
-/
theorem directImageCTFNonproper
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E]
    (n : ℕ) (hn : 1 ≤ n)
    {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of D.k))]
    [Y.Over (Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of D.k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of D.k))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of D.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    (a b : ℤ)
    {K : DerivedCategory
      (Sheaf X.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))))}
    (hK : DerivedCategory.boundedConstructible
      (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) X K)
    (hTor : DerivedCategory.hasTorAmplitudeIn
      (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) X a b K) :
    DerivedCategory.boundedConstructible
        (ModuleCat.{u + 1} (ULift.{u + 1} (Padic.coefficientExtensionRing l E n))) Y
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) f).rightDerivedFunctor.obj K) ∧
      DerivedCategory.hasTorAmplitudeIn
        (ULift.{u + 1} (Padic.coefficientExtensionRing l E n)) Y a
        (b + 2 * (d : ℤ))
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1}
          (Padic.coefficientExtensionRing l E n))) f).rightDerivedFunctor.obj K) := by
  classical
  let A := ULift.{u + 1} (Padic.coefficientExtensionRing l E n)
  have : Finite (Padic.coefficientExtensionRing l E n) :=
    Padic.finite_coefficientExtensionRing l E n hn
  have : Finite A := Equiv.ulift.finite_iff.mpr inferInstance
  have : IsNoetherianRing A := isNoetherian_of_finite A A
  have hchar0 : ringChar D.k₀ = D.p := by
    let : Fact D.p.Prime := ⟨D.prime⟩
    let : Fintype D.k₀ := Fintype.ofFinite D.k₀
    have : CharP D.k₀ D.p := charP_of_card_eq_prime_pow
      (by simpa only [Nat.card_eq_fintype_card] using D.card_base.trans D.cardinality_eq)
    exact ringChar.eq D.k₀ D.p
  have hchar : ringChar D.k = D.p :=
    (Algebra.ringChar_eq D.k₀ D.k).symm.trans hchar0
  have h := (Padic.coefficientExtensionIntegers_dvr l E).choose_spec
  have habv : Padic.coefficientExtensionAbsoluteValue l E (l : E) < 1 := by
    calc
      Padic.coefficientExtensionAbsoluteValue l E (l : E) = ‖(l : Padic l)‖ := by
        change spectralNorm (Padic l) E (l : E) = ‖(l : Padic l)‖
        simpa only [map_natCast] using
          (spectralNorm_extends (K := Padic l) (L := E) (l : Padic l))
      _ < 1 := Padic.norm_p_lt_one
  have hlm : (l : Padic.coefficientExtensionIntegers l E) ∈
      Padic.coefficientExtensionMaximalIdeal l E :=
    (h.2.1 _).2 (by simpa only [SubringClass.coe_natCast] using habv)
  have hgen : Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) =
      Padic.coefficientExtensionMaximalIdeal l E :=
    h.2.2.2.2.2.2.2.2.2.2.2.2.2.1.choose_spec
  have hpow : (l : Padic.coefficientExtensionIntegers l E) ^ n ∈
      Padic.coefficientExtensionIdeal l E n := by
    change _ ∈ Ideal.span ({Padic.coefficientExtensionUniformizer l E} :
      Set (Padic.coefficientExtensionIntegers l E)) ^ n
    rw [hgen]
    exact Ideal.pow_mem_pow hlm n
  have hkill : ((l ^ n : ℕ) : Padic.coefficientExtensionRing l E n) = 0 := by
    change ((l ^ n : ℕ) :
      Padic.coefficientExtensionIntegers l E ⧸ Padic.coefficientExtensionIdeal l E n) = 0
    rw [← map_natCast (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E n)),
      Ideal.Quotient.eq_zero_iff_mem]
    simpa only [Nat.cast_pow] using hpow
  have hkillA : ((l ^ n : ℕ) : A) = 0 := by
    apply ULift.down_injective
    exact hkill
  have hlk : (l : D.k) ≠ 0 := by
    intro hz
    exact hl ((CharP.ringChar_of_prime_eq_zero (Fact.out : l.Prime) hz).symm.trans hchar)
  have hu : IsUnit ((l ^ n : ℕ) : D.k) := by
    rw [Nat.cast_pow]
    exact (isUnit_iff_ne_zero.mpr hlk).pow n
  have : HasInvertibleExponent A (Spec (CommRingCat.of D.k)) :=
    ⟨l ^ n, pow_pos (Fact.out : l.Prime).pos n, hkillA,
      by simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom⟩
  have hf : f ≫ (Y ↘ Spec (CommRingCat.of D.k)) =
      (X ↘ Spec (CommRingCat.of D.k)) := CategoryTheory.comp_over f _
  refine ⟨boundedConstructible_rightDerivedLowerStar_of_locallyOfFiniteType A f
    (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) hf K hK, ?_⟩
  have hta := (hasTorAmplitudeIn_iff_torAmplitudeIn A X a b K).mp hTor
  have : NeZero (l ^ n) := ⟨(pow_pos (Fact.out : l.Prime).pos n).ne'⟩
  have hspec : IsUnit ((l ^ n : ℕ) : Γ(Spec (CommRingCat.of D.k), ⊤)) := by
    simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of D.k)).inv.hom
  have hNY : IsUnit ((l ^ n : ℕ) : Γ(Y, ⊤)) := by
    simpa only [map_natCast] using hspec.map
      (Y ↘ Spec (CommRingCat.of D.k)).appTop.hom
  have hR := torAmplitudeIn_rightDerivedLowerStar _
    (X ↘ Spec (CommRingCat.of D.k)) (Y ↘ Spec (CommRingCat.of D.k)) f hf d hd a b
    (l ^ n) (nsmul_id_eq_zero_of_natCast_eq_zero hkillA K) hNY hK hta
  exact (hasTorAmplitudeIn_iff_torAmplitudeIn A Y a (b + 2 * (d : ℤ)) _).mpr hR

end AlgebraicGeometry.Etale

end

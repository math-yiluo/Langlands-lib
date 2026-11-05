import Langlands.Global.CurvePlaceIntegralClosure
import Langlands.Global.CurvePlaceCompletedIntegersExtension
import Langlands.Global.CurvePlaceCompletedProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-! # Integral-closure primes and all actual upper curve places -/

noncomputable section

universe u

open IsDedekindDomain AlgebraicCurve
open scoped Langlands.Global.CurvePlaceCompletionExtension
  Langlands.Global.CurvePlaceIntegralClosure

namespace Langlands.Global.CurvePlaceIntegralPrimes

variable {k K L : Type u} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L]
  (p : Place k K) (q : CurvePlacesAbove k L p)

/-- Every element of the actual integral closure belongs to every actual upper valuation ring. -/
theorem integralClosure_le :
    (integralClosure p.toValuationSubring L).toSubring ≤ q.1.toValuationSubring.toSubring := by
  intro x hx
  obtain ⟨a, ha⟩ := (isIntegrallyClosed_iff L).mp
    (inferInstance : IsIntegrallyClosed q.1.toValuationSubring)
    (hx.tower_top : IsIntegral q.1.toValuationSubring x)
  exact ha ▸ a.property

/-- The original inclusion of the integral closure into an actual upper valuation ring. -/
def integersMap : curvePlaceIntegralClosure L p →ₐ[p.toValuationSubring] q.1.toValuationSubring :=
  { toFun := fun x => ⟨x.val, integralClosure_le p q x.property⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl
    commutes' := fun _ => rfl }

scoped instance (priority := 50) :
    Algebra (curvePlaceIntegralClosure L p) q.1.toValuationSubring :=
  (integersMap p q).toRingHom.toAlgebra

scoped instance :
    IsScalarTower p.toValuationSubring (curvePlaceIntegralClosure L p) q.1.toValuationSubring :=
  .of_algebraMap_eq fun _ => rfl

scoped instance :
    IsScalarTower (curvePlaceIntegralClosure L p) q.1.toValuationSubring L :=
  .of_algebraMap_eq fun _ => rfl

scoped instance : Module.IsTorsionFree (curvePlaceIntegralClosure L p) q.1.toValuationSubring :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr fun x y h => by
    apply Subtype.ext
    exact congrArg (fun z : q.1.toValuationSubring => (z : L)) h

/-- The actual center of an upper valuation ring on the integral closure. -/
def center : Ideal (curvePlaceIntegralClosure L p) :=
  q.1.heightOneSpectrum.asIdeal.comap (integersMap p q)

instance : q.1.heightOneSpectrum.asIdeal.LiesOver (center p q) := ⟨rfl⟩

instance : (center p q).IsPrime :=
  Ideal.comap_isPrime _ _

instance : (center p q).LiesOver p.heightOneSpectrum.asIdeal :=
  Ideal.comap_liesOver _ _ (integersMap p q)

/-- The center is among all primes over the original lower maximal ideal. -/
def centerAbove :
    p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p) :=
  Ideal.primesOver.mk p.heightOneSpectrum.asIdeal (center p q)

variable [FiniteDimensional K L]
  [Finite k] [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]

/-- The nonzero height-one prime represented by an integral-closure prime above the place. -/
def heightOne
    (P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p)) :
    HeightOneSpectrum (curvePlaceIntegralClosure L p) :=
  ⟨P.1, inferInstance, Ideal.ne_bot_of_mem_primesOver p.heightOneSpectrum.ne_bot P.2⟩

variable [IsScalarTower k K L]

instance constantTower : IsScalarTower k p.toValuationSubring L :=
  .of_algebraMap_eq fun a => by
    change algebraMap k L a = algebraMap K L (algebraMap k K a)
    exact IsScalarTower.algebraMap_apply k K L a

/-- An integral-closure prime gives its original curve place, with exact restriction. -/
def upperPlace
    (P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p)) :
    CurvePlacesAbove k L p := by
  let Q := heightOne p P
  let : Q.asIdeal.LiesOver p.heightOneSpectrum.asIdeal := P.property.2
  refine ⟨Place.ofHeightOneSpectrum (K := k) Q, ?_⟩
  ext x
  change Q.valuation L (algebraMap K L x) ≤ 1 ↔ x ∈ p.toValuationSubring
  rw [← HeightOneSpectrum.valuation_liesOver L p.heightOneSpectrum Q]
  have he : p.heightOneSpectrum.asIdeal.ramificationIdx' Q.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver _ p.heightOneSpectrum.ne_bot
  rw [pow_le_one_iff_of_nonneg zero_le he]
  exact (p.mem_iff_adicValuation_le_one).symm

omit [IsScalarTower k K L] in
private theorem localization_le (q : CurvePlacesAbove k L p) :
    HeightOneSpectrum.valuationSubringAtPrime L (heightOne p (centerAbove p q)) ≤
      q.1.toValuationSubring := by
  intro x hx
  obtain ⟨a, b, hb, rfl⟩ := hx
  apply q.1.toValuationSubring.mem_of_valuation_le_one _
  have hb' : IsUnit (integersMap p q b) := by
    change integersMap p q b ∉ IsLocalRing.maximalIdeal q.1.toValuationSubring at hb
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hb
  change q.1.toValuationSubring.valuation
    ((a : L) * (b : L)⁻¹) ≤ 1
  rw [map_mul, map_inv₀,
    show q.1.toValuationSubring.valuation (b : L) = 1 from
      (q.1.toValuationSubring.valuation_eq_one_iff _).mp hb',
    inv_one, mul_one]
  exact q.1.toValuationSubring.valuation_le_one (integersMap p q a)

omit [IsScalarTower k K L] in
/-- Localizing at the actual center recovers the original upper valuation subring. -/
theorem valuationSubringAtCenter (q : CurvePlacesAbove k L p) :
    HeightOneSpectrum.valuationSubringAtPrime L (heightOne p (centerAbove p q)) =
      q.1.toValuationSubring :=
  ValuationSubring.eq_of_le_of_ne_top _ (localization_le p q) q.1.ne_top'

omit [IsScalarTower k K L] in
/-- The original upper valuation ring is the localization at its actual center. -/
scoped instance localizationAtCenter (q : CurvePlacesAbove k L p) :
    IsLocalization (center p q).primeCompl q.1.toValuationSubring := by
  let e : HeightOneSpectrum.valuationSubringAtPrime L (heightOne p (centerAbove p q)) ≃ₐ[
      curvePlaceIntegralClosure L p] q.1.toValuationSubring :=
    { toRingEquiv := RingEquiv.subringCongr
        (congrArg ValuationSubring.toSubring (valuationSubringAtCenter p q))
      commutes' x := by apply Subtype.ext; rfl }
  let : IsLocalization (center p q).primeCompl
      (HeightOneSpectrum.valuationSubringAtPrime L (heightOne p (centerAbove p q))) :=
    inferInstanceAs (IsLocalization (heightOne p (centerAbove p q)).asIdeal.primeCompl
      (HeightOneSpectrum.valuationSubringAtPrime L (heightOne p (centerAbove p q))))
  exact IsLocalization.isLocalization_of_algEquiv (center p q).primeCompl e

/-- The original prime-to-place construction recovers every actual upper place. -/
theorem upperPlace_center (q : CurvePlacesAbove k L p) :
    upperPlace p (centerAbove p q) = q := by
  apply Subtype.ext
  apply Place.ext
  change ((heightOne p (centerAbove p q)).valuation L).valuationSubring = _
  rw [← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtCenter p q

/-- All primes over the lower maximal ideal correspond to all actual upper curve places. -/
def primeEquivUpperPlaces :
    p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p) ≃
      CurvePlacesAbove k L p :=
  Equiv.ofBijective (upperPlace p)
    ⟨by
      intro P P' h
      apply Subtype.ext
      exact congrArg HeightOneSpectrum.asIdeal
        (Place.ofHeightOneSpectrum_injective (congrArg Subtype.val h)),
      fun q => ⟨centerAbove p q, upperPlace_center p q⟩⟩

@[simp]
theorem primeEquivUpperPlaces_apply
    (P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p)) :
    (primeEquivUpperPlaces p P).val = Place.ofHeightOneSpectrum (K := k) (heightOne p P) := rfl

@[simp]
theorem primeEquivUpperPlaces_symm_apply (q : CurvePlacesAbove k L p) :
    (primeEquivUpperPlaces p).symm q = centerAbove p q := by
  apply (primeEquivUpperPlaces p).injective
  exact ((primeEquivUpperPlaces p).apply_symm_apply q).trans (upperPlace_center p q).symm

@[simp]
theorem centerAbove_upperPlace
    (P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p)) :
    centerAbove p (upperPlace p P) = P := by
  apply (primeEquivUpperPlaces p).injective
  exact upperPlace_center p (upperPlace p P)

omit [IsScalarTower k K L] in
/-- The ramification index of the localization itself is one. -/
theorem localization_ramificationIdx (q : CurvePlacesAbove k L p) :
    q.1.heightOneSpectrum.asIdeal.ramificationIdx (curvePlaceIntegralClosure L p) = 1 := by
  have hm : (center p q).map (algebraMap (curvePlaceIntegralClosure L p) q.1.toValuationSubring) =
      q.1.heightOneSpectrum.asIdeal :=
    IsLocalization.AtPrime.map_eq_maximalIdeal (center p q) q.1.toValuationSubring
  have hn : center p q ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot p.heightOneSpectrum.ne_bot _
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (center p q)
    q.1.heightOneSpectrum.asIdeal hn]
  rw [← hm]
  exact Ideal.ramificationIdx'_map_self_eq_one
    (by rw [hm]; exact q.1.heightOneSpectrum.isPrime.ne_top)
    (by rw [hm]; exact q.1.heightOneSpectrum.ne_bot)

omit [IsScalarTower k K L] in
/-- Ramification at an actual upper place equals ramification at its actual center. -/
theorem ramificationIdx_center (q : CurvePlacesAbove k L p) :
    q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring =
      (center p q).ramificationIdx p.toValuationSubring := by
  rw [Ideal.ramificationIdx_tower (R := p.toValuationSubring) (center p q)
    q.1.heightOneSpectrum.asIdeal, localization_ramificationIdx p q, mul_one]

omit [IsScalarTower k K L] in
/-- The inertia degree of the localization itself is one. -/
theorem localization_inertiaDeg (q : CurvePlacesAbove k L p) :
    q.1.heightOneSpectrum.asIdeal.inertiaDeg (curvePlaceIntegralClosure L p) = 1 := by
  let := Localization.AtPrime.algebraOfLiesOver (center p q) q.1.heightOneSpectrum.asIdeal
  rw [Ideal.inertiaDeg_eq (center p q) q.1.heightOneSpectrum.asIdeal]
  apply Module.finrank_of_bijective_algebraMap
    (R := (center p q).ResidueField) (S := q.1.heightOneSpectrum.asIdeal.ResidueField)
  exact (RingHom.surjectiveOnStalks_of_isLocalization
    (center p q).primeCompl q.1.toValuationSubring).residueFieldMap_bijective
    (center p q) q.1.heightOneSpectrum.asIdeal rfl

omit [IsScalarTower k K L] in
/-- Inertia at an actual upper place equals inertia at its actual center. -/
theorem inertiaDeg_center (q : CurvePlacesAbove k L p) :
    q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring =
      (center p q).inertiaDeg p.toValuationSubring := by
  rw [Ideal.inertiaDeg_tower (R := p.toValuationSubring) (center p q)
    q.1.heightOneSpectrum.asIdeal, localization_inertiaDeg p q, mul_one]

/-- The fundamental degree identity is indexed by every actual upper curve place. -/
theorem sum_ramification_inertia :
    (∑ q : CurvePlacesAbove k L p,
      q.1.heightOneSpectrum.asIdeal.ramificationIdx p.toValuationSubring *
        q.1.heightOneSpectrum.asIdeal.inertiaDeg p.toValuationSubring) =
      Module.finrank K L := by
  let := Fintype.ofFinite (p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p))
  calc
    _ = ∑ P : p.heightOneSpectrum.asIdeal.primesOver (curvePlaceIntegralClosure L p),
        P.1.ramificationIdx p.toValuationSubring *
          P.1.inertiaDeg p.toValuationSubring := by
      apply Fintype.sum_equiv (primeEquivUpperPlaces p).symm
      intro q
      rw [primeEquivUpperPlaces_symm_apply]
      exact congrArg₂ (· * ·) (ramificationIdx_center p q) (inertiaDeg_center p q)
    _ = _ := CurvePlaceIntegralClosure.sum_ramification_inertia p

end Langlands.Global.CurvePlaceIntegralPrimes

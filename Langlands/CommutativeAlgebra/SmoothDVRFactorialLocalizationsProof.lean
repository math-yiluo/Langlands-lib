import Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsStatement
import Langlands.CommutativeAlgebra.RegularLocalFactorialProof
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-! # Regularity and factoriality of smooth algebras over DVRs -/

universe u v

namespace Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsProof

open IsLocalRing

/-- A flat, essentially finite type, unramified local algebra over a regular
local ring is regular local. -/
lemma regularLocal_of_flat_unramified (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    [Algebra.EssFiniteType R S] [Algebra.FormallyUnramified R S] :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hspan : (maximalIdeal S).spanFinrank ≤ (maximalIdeal R).spanFinrank := by
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S)]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
  have hdim : ringKrullDim R ≤ ringKrullDim S := by
    rw [← maximalIdeal_height_eq_ringKrullDim, ← maximalIdeal_height_eq_ringKrullDim]
    apply WithBot.coe_le_coe.mpr
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (maximalIdeal R) (maximalIdeal S)]
    exact le_self_add
  exact (Nat.cast_le.mpr hspan).trans
    (IsRegularLocalRing.spanFinrank_maximalIdeal.trans_le hdim)

/-- Etale algebras over regular rings have regular prime localizations. -/
lemma regularLocal_localization_of_etale (R : Type u) (S : Type v)
    [CommRing R] [CommRing S] [Algebra R S] [IsRegularRing R]
    [Algebra.Etale R S] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  have : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let p := q.under R
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Algebra.FormallyUnramified R (Localization.AtPrime q) :=
    .comp R S (Localization.AtPrime q)
  have : Algebra.EssFiniteType R (Localization.AtPrime q) :=
    .comp R S (Localization.AtPrime q)
  have : Algebra.FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_restrictScalars R _ _
  have : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp R _ _
  exact regularLocal_of_flat_unramified (Localization.AtPrime p) (Localization.AtPrime q)

/-- Smooth algebras over regular rings have regular prime localizations. -/
lemma regularLocal_localization_of_smooth (R : Type u) (A : Type v)
    [CommRing R] [CommRing A] [Algebra R A] [IsRegularRing R]
    [Algebra.Smooth R A] (p : Ideal A) [p.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hf, n, hAlg, hTower, hEtale⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := R) (p := p)
  let := hAlg
  let := hTower
  let := hEtale
  have hd : Disjoint (Submonoid.powers f : Set A) (p : Set A) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q : Ideal (Localization.Away f) := p.map (algebraMap A (Localization.Away f))
  have : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers f) (Localization.Away f) p
      inferInstance hd
  have hc : q.comap (algebraMap A (Localization.Away f)) = p :=
    IsLocalization.under_map_of_isPrime_disjoint (.powers f) (Localization.Away f)
      inferInstance hd
  have : IsRegularLocalRing (Localization.AtPrime q) :=
    regularLocal_localization_of_etale (MvPolynomial (Fin n) R) (Localization.Away f) q
  let e := IsLocalization.localizationLocalizationAtPrimeIsoLocalization (.powers f) q
  have hreg : IsRegularLocalRing (Localization.AtPrime
      (q.comap (algebraMap A (Localization.Away f)))) :=
    IsRegularLocalRing.of_ringEquiv e.toRingEquiv.symm
  have transport (r : Ideal A) [r.IsPrime] (hr : r = p)
      (h : IsRegularLocalRing (Localization.AtPrime r)) :
      IsRegularLocalRing (Localization.AtPrime p) := by
    subst r
    exact h
  exact transport _ hc hreg

end Langlands.CommutativeAlgebra.SmoothDVRFactorialLocalizationsProof

namespace Langlands.CommutativeAlgebra

/-- Every prime localization of every smooth algebra over a DVR is factorial. -/
theorem smoothDVRFactorialLocalizations :
    SmoothDVRFactorialLocalizationsStatement.{u} := by
  intro R _ _ _ A _ _ hSmooth p hp
  let := hSmooth
  exact regularLocalFactorial (Localization.AtPrime p)
    (SmoothDVRFactorialLocalizationsProof.regularLocal_localization_of_smooth R A p)

end Langlands.CommutativeAlgebra

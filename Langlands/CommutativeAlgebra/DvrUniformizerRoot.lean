import Langlands.CommutativeAlgebra.DvrCompletion
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.DedekindDomain.Basic

/-! # Adjoining a root of a DVR uniformizer -/

noncomputable section

open IsLocalRing Polynomial

namespace Langlands.CommutativeAlgebra.DvrUniformizerRoot

variable {R : Type*} [CommRing R] (a : R) (n : ℕ)

/-- The algebra obtained by adjoining a root of `X ^ n - C a`. -/
abbrev RootAlgebra := AdjoinRoot (X ^ n - C a)

/-- The defining equation for the distinguished root of the binomial. -/
theorem root_pow : (AdjoinRoot.root (X ^ n - C a)) ^ n =
    algebraMap R (RootAlgebra a n) a := by
  change _ = AdjoinRoot.of (X ^ n - C a) a
  have h := AdjoinRoot.eval₂_root (X ^ n - C a)
  simpa only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] using h

variable [IsDomain R] [IsDiscreteValuationRing R] {π : R} {n : ℕ}

local notation "T" => RootAlgebra π n
local notation "t" => AdjoinRoot.root (X ^ n - C π)

/-- Killing the distinguished root identifies the quotient with the original residue field. -/
def quotientRootEquivResidueField (hπ : Irreducible π) (hn : n ≠ 0) :
    T ⧸ Ideal.span {t} ≃+* ResidueField R := by
  let I : Ideal T := Ideal.span {t}
  have hπ₀ : residue R π = 0 := by
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    rw [hπ.maximalIdeal_eq]
    exact Ideal.mem_span_singleton_self π
  have hEval : eval₂ (residue R) 0 (X ^ n - C π) = 0 := by simp [hn, hπ₀]
  let f : T →+* ResidueField R := AdjoinRoot.lift (residue R) 0 hEval
  have hf : f t = 0 := AdjoinRoot.lift_root hEval
  let g : T ⧸ I →+* ResidueField R := Ideal.Quotient.lift I f (fun x hx => by
    obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hf, mul_zero])
  let j : R →+* T ⧸ I := (Ideal.Quotient.mk I).comp (algebraMap R T)
  have ht₀ : Ideal.Quotient.mk I t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
  have hj : j π = 0 := by
    change (Ideal.Quotient.mk I) (algebraMap R T π) = 0
    rw [← root_pow π n, map_pow, ht₀, zero_pow hn]
  let k : ResidueField R →+* T ⧸ I :=
    Ideal.Quotient.lift (maximalIdeal R) j (fun x hx => by
      rw [hπ.maximalIdeal_eq] at hx
      obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.mp hx
      rw [map_mul, hj, mul_zero])
  refine RingEquiv.ofRingHom g k ?_ ?_
  · apply Ideal.Quotient.ringHom_ext
    ext x
    change f (AdjoinRoot.of (X ^ n - C π) x) = residue R x
    exact AdjoinRoot.lift_of hEval
  · apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext x
      change k (f (AdjoinRoot.of (X ^ n - C π) x)) = j x
      rw [show f (AdjoinRoot.of (X ^ n - C π) x) = residue R x from
        AdjoinRoot.lift_of hEval]
      rfl
    · change k (f t) = Ideal.Quotient.mk I t
      rw [hf, map_zero, ht₀]

/-- The binomial algebra for a uniformizer is a DVR whose distinguished root is a uniformizer. -/
theorem isDiscreteValuationRing_adjoinRoot (hπ : Irreducible π) (hn : n ≠ 0) :
    ∃ (_ : IsDomain T) (_ : IsDiscreteValuationRing T), Irreducible t := by
  let I : Ideal T := Ideal.span {t}
  have hI : I.IsMaximal := Ideal.Quotient.maximal_of_isField I
    ((quotientRootEquivResidueField hπ hn).toMulEquiv.isField (Field.toIsField _))
  have hm : (X ^ n - C π).Monic := monic_X_pow_sub_C _ hn
  have : IsLocalRing T := IsLocalRing.of_unique_max_ideal ⟨I, hI, fun J hJ => by
    have : Algebra.IsIntegral R T := AdjoinRoot.isIntegral_of_monic hm
    have hJ₀ : J.under R = maximalIdeal R :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal J)
    have hpow : t ^ n ∈ J := by
      rw [root_pow]
      change π ∈ J.under R
      rw [hJ₀, hπ.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self π
    exact (hI.eq_of_le hJ.ne_top ((Ideal.span_singleton_le_iff_mem J).mpr
      (hJ.isPrime.mem_of_pow_mem n hpow))).symm⟩
  have hmax : maximalIdeal T = I := (IsLocalRing.eq_maximalIdeal hI).symm
  have : Module.Free R T := hm.free_adjoinRoot
  have hreg : IsSMulRegular T t := by
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hπreg : IsSMulRegular T π := IsSMulRegular.of_ne_zero hπ.ne_zero
    have hpow : t ^ n = t ^ k * t := (congrArg (t ^ ·) hk).trans (pow_succ t k)
    intro x y h
    apply hπreg
    change t * x = t * y at h
    simp only [Algebra.smul_def, ← root_pow π n, hpow, mul_assoc, h]
  obtain ⟨hd, hv⟩ := isDomain_and_isDiscreteValuationRing_of_maximalIdeal_eq_span hmax hreg
  refine ⟨hd, hv, ?_⟩
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mpr hmax

/-- The binomial DVR is the integral closure of the original DVR in its fraction field. -/
def integralClosureEquiv (hπ : Irreducible π) (hn : n ≠ 0) :
    T ≃ₐ[R] integralClosure R (FractionRing T) := by
  have hDvr := isDiscreteValuationRing_adjoinRoot hπ hn
  letI : IsDomain T := hDvr.choose
  letI : IsDiscreteValuationRing T := hDvr.choose_spec.choose
  have : Algebra.IsIntegral R T := AdjoinRoot.isIntegral_of_monic (monic_X_pow_sub_C _ hn)
  have : IsIntegralClosure T R (FractionRing T) := by
    refine ⟨IsFractionRing.injective T (FractionRing T), fun {x} => ⟨fun hx => ?_, ?_⟩⟩
    · exact (isIntegrallyClosed_iff (FractionRing T)).mp inferInstance hx.tower_top
    · rintro ⟨y, rfl⟩
      exact IsIntegral.algebraMap (Algebra.IsIntegral.isIntegral (R := R) y)
  exact IsIntegralClosure.equiv R T (FractionRing T) _

end Langlands.CommutativeAlgebra.DvrUniformizerRoot

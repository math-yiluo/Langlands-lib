import Langlands.Global.Factors.HeckeEulerProduct
import Langlands.ClassField.Global.FiniteDivisorFractionalIdeal
import Langlands.ClassField.Global.PrincipalIdeleDivisor
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

/-! # Arithmetic adapters for finite Hecke divisors -/

noncomputable section

universe u

namespace Langlands.Global.HeckeDivisor

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open Langlands.ClassField.Global
open Langlands.Global.CompletionPadic
open scoped NumberField nonZeroDivisors

variable {K : Type u} [Field K] [NumberField K]

/-- The local order used in the actual Hecke shell formulas is the usual divisor order. -/
theorem ord_eq_neg_unitsExponent (v : FinitePlace K) (x : (FiniteCompletion K v)ˣ) :
    (topologicalData v).ord (x : FiniteCompletion K v) =
      -Multiplicative.toAdd (unitsExponent v x) := by
  unfold PadicField.TopologicalData.ord
  rw [AdelicFunctoriality.FiniteExtension.topologicalData_discreteValuation,
    valued_units, WithZero.log_exp]

/-- Coefficients of the existing idele divisor are the actual local shell orders. -/
theorem ideleDivisor_apply_eq_ord (x : Ideles K) (v : FinitePlace K) :
    ideleDivisor x v = (topologicalData v).ord
      (ideleCoordinate v x : FiniteCompletion K v) := by
  rw [ord_eq_neg_unitsExponent]
  rfl

/-- The principal divisor uses the existing divisor map on the actual principal idele. -/
def principalDivisor (a : Kˣ) : FinitePlaceDivisor K :=
  ideleDivisor (IdeleGroup.unitEmbedding (𝓞 K) K a)

@[simp] theorem principalDivisor_one : principalDivisor (1 : Kˣ) = 0 := by
  simp [principalDivisor]

@[simp] theorem principalDivisor_mul (a b : Kˣ) :
    principalDivisor (a * b) = principalDivisor a + principalDivisor b := by
  simp [principalDivisor]

/-- The coefficient is the multiplicity in the actual principal fractional ideal. -/
theorem principalDivisor_apply (a : Kˣ) (v : FinitePlace K) :
    principalDivisor a v =
      FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) :=
  principalIdeleDivisorFormula K v a

/-- Compatibility of the existing prime-product equivalence with principal elements. -/
theorem fractionalIdeal_principalDivisor (a : Kˣ) :
    finiteDivisorFractionalIdeal K (principalDivisor a) = toPrincipalIdeal (𝓞 K) K a := by
  apply fractionalIdealDivisor_injective K
  rw [fractionalIdealDivisor_finiteDivisorFractionalIdeal]
  ext v
  simpa only [fractionalIdealDivisor_apply, coe_toPrincipalIdeal] using
    principalDivisor_apply a v

/-- The positive real norm of a finite integer divisor. -/
def norm (d : FinitePlaceDivisor K) : ℝ :=
  d.prod fun v n => (Ideal.absNorm v.asIdeal : ℝ) ^ n

/-- This divisor norm is the ordinary absolute norm of its fractional ideal. -/
theorem norm_eq_absNorm (d : FinitePlaceDivisor K) :
    norm d = (FractionalIdeal.absNorm
      (finiteDivisorFractionalIdeal K d : FractionalIdeal (𝓞 K)⁰ K) : ℝ) := by
  simp only [finiteDivisorFractionalIdeal_val, map_finsuppProd, map_zpow₀,
    FractionalIdeal.coeIdeal_absNorm]
  simp only [norm, Finsupp.prod, Rat.cast_prod, Rat.cast_zpow, Rat.cast_natCast]

/-- The norm of a principal divisor is the absolute field norm. -/
theorem norm_principalDivisor (a : Kˣ) :
    norm (principalDivisor a) = |(Algebra.norm ℚ (a : K) : ℝ)| := by
  rw [norm_eq_absNorm, fractionalIdeal_principalDivisor, coe_toPrincipalIdeal,
    FractionalIdeal.absNorm_span_singleton, Rat.cast_abs]

/-- A principal divisor vanishes exactly on the global integral units. -/
theorem principalDivisor_eq_zero_iff (a : Kˣ) :
    principalDivisor a = 0 ↔
      ∃ b : (𝓞 K)ˣ, Units.map (algebraMap (𝓞 K) K : 𝓞 K →* K) b = a := by
  constructor
  · intro ha
    have hv (v : FinitePlace K) : v.valuation K (a : K) = 1 := by
      have h := (ideleDivisor_eq_zero_iff _).mp ha v
      rw [ideleCoordinate_unitEmbedding] at h
      simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
        RingHom.id_apply, valuedAdicCompletion_eq_valuation'] using h
    obtain ⟨b, hb⟩ := mem_integers_of_valuation_le_one K (a : K) fun v => (hv v).le
    obtain ⟨c, hc⟩ := mem_integers_of_valuation_le_one K (↑(a⁻¹) : K) fun v => by
      rw [Units.val_inv_eq_inv_val, map_inv₀, hv v, inv_one]
    have hbc : b * c = 1 := by
      apply IsFractionRing.injective (𝓞 K) K
      rw [map_mul, hb, hc, map_one, Units.mul_inv]
    exact ⟨⟨b, c, hbc, by rw [mul_comm, hbc]⟩, Units.ext hb⟩
  · rintro ⟨b, rfl⟩
    apply (ideleDivisor_eq_zero_iff _).mpr
    intro v
    rw [ideleCoordinate_unitEmbedding]
    change Valued.v (algebraMap K (FiniteCompletion K v)
      (algebraMap (𝓞 K) K (b : 𝓞 K))) = 1
    have hu := congrArg (fun z : Multiplicative ℤ => (z : WithZero (Multiplicative ℤ)))
      (v.valuation_of_unit_eq (K := K) b)
    simpa only [algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
      RingHom.id_apply, valuedAdicCompletion_eq_valuation',
      valuationOfNeZero_eq, Units.coe_map, WithZero.coe_one, MonoidHom.coe_coe] using hu

end Langlands.Global.HeckeDivisor

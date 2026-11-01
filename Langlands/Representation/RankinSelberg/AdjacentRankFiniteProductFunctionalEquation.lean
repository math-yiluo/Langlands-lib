import Langlands.Representation.RankinSelberg.AdjacentRankMatrixReflection
import Langlands.Representation.GodementJacquet.FunctionalEquationProducts

/-! The signed normalized functional equation of the actual adjacent finite sum. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis GodementJacquet
open scoped BigOperators

/-- Absorb the explicitly recorded model sign into the epsilon unit. -/
def absorbedFunctionalEquationSign (ζ c : ℂˣ) (e : ℕ) : ℂˣ :=
  ζ ^ e * c

/-- Keeping a model sign explicit is equivalent to absorbing it in the
epsilon unit; the polynomials, exponent and rational values are unchanged. -/
theorem normalizedFunctionalEquation_absorb_sign_iff
    {q : ℕ} {P PD : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {m : ℤ}
    {R RD : RationalFunctions} :
    NormalizedFunctionalEquation q P PD ζ c e m R RD ↔
      NormalizedFunctionalEquation q P PD 1 (absorbedFunctionalEquationSign ζ c e)
        0 m R RD := by
  constructor <;> intro h s hR hRD <;>
    have hs := h s hR hRD <;>
    simpa only [absorbedFunctionalEquationSign, epsilonMonomial, Units.val_mul,
      Units.val_pow_eq_pow_val, Units.val_one, pow_zero, one_mul, mul_assoc] using hs

/-- Multiplication of the dual rational value by one model-minus-one scalar
increases the recorded sign exponent by exactly one, retaining pole guards. -/
theorem normalizedFunctionalEquation_mul_dual_sign
    {q : ℕ} {P PD : Polynomial ℂ} {ζ c : ℂˣ} {e : ℕ} {m : ℤ}
    {R RD : RationalFunctions}
    (h : NormalizedFunctionalEquation q P PD ζ c e m R RD) :
    NormalizedFunctionalEquation q P PD ζ c (e + 1) m R
      (RatFunc.C (ζ : ℂ) * RD) := by
  intro s hR hRD
  have hinv : RatFunc.C ((ζ : ℂ)⁻¹) * (RatFunc.C (ζ : ℂ) * RD) = RD := by
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ ζ.ne_zero, map_one, one_mul]
  have hd : RD.denom.eval (spectralPoint q (1 - s)) ≠ 0 := by
    have hconst : (RatFunc.C ((ζ : ℂ)⁻¹)).denom.eval
        (spectralPoint q (1 - s)) ≠ 0 := by
      simp only [RatFunc.denom_C, Polynomial.eval_one, ne_eq, one_ne_zero, not_false_eq_true]
    have hp := ratFunc_denom_mul_eval_ne_zero hconst hRD
    rwa [hinv] at hp
  have hev : (RatFunc.C (ζ : ℂ) * RD).eval (RingHom.id ℂ)
      (spectralPoint q (1 - s)) =
      (ζ : ℂ) * RD.eval (RingHom.id ℂ) (spectralPoint q (1 - s)) := by
    rw [RatFunc.eval_mul (RingHom.id ℂ) (spectralPoint q (1 - s)) (by simp) hd,
      RatFunc.eval_C, RingHom.id_apply]
  rw [hev]
  calc
    _ = (ζ : ℂ) * (PD.eval (spectralPoint q (1 - s)) *
        RD.eval (RingHom.id ℂ) (spectralPoint q (1 - s))) := by ring
    _ = (ζ : ℂ) * ((ζ : ℂ) ^ e * epsilonMonomial q c m s *
        (P.eval (spectralPoint q s) * R.eval (RingHom.id ℂ) (spectralPoint q s))) :=
      congrArg (fun z : ℂ => (ζ : ℂ) * z) (h s hR hd)
    _ = _ := by rw [pow_succ]; ring

/-- Equal-rank sign exponent `r` and the matrix functional equation combine
with the reflected-test sign into the ambient exponent `r+1`. The theorem
retains both pole guards even if summand poles cancel in the finite sum. -/
theorem normalizedFunctionalEquation_adjacent_sum_mul
    {q : ℕ} (hq : 1 < q) {ι : Type*} (J : Finset ι)
    {P₀ PD₀ P₁ PD₁ : Polynomial ℂ} {ζ c₀ c₁ : ℂˣ}
    {r : ℕ} {m₀ m₁ : ℤ}
    (A AD M MD : ι → RationalFunctions)
    (hA : ∀ i ∈ J, NormalizedFunctionalEquation q P₀ PD₀ ζ c₀ r m₀ (A i) (AD i))
    (hM : ∀ i ∈ J, NormalizedFunctionalEquation q P₁ PD₁ 1 c₁ 0 m₁ (M i) (MD i)) :
    NormalizedFunctionalEquation q (P₀ * P₁) (PD₀ * PD₁)
      ζ (c₀ * c₁) (r + 1) (m₀ + m₁)
      (∑ i ∈ J, A i * M i) (RatFunc.C (ζ : ℂ) * ∑ i ∈ J, AD i * MD i) := by
  have ha : ∀ i ∈ J, NormalizedFunctionalEquation q P₀ PD₀ 1
      (absorbedFunctionalEquationSign ζ c₀ r) 0 m₀ (A i) (AD i) :=
    fun i hi => normalizedFunctionalEquation_absorb_sign_iff.mp (hA i hi)
  have hs := normalizedFunctionalEquation_sum_mul hq J A AD M MD ha hM
  have hsigned : NormalizedFunctionalEquation q (P₀ * P₁) (PD₀ * PD₁)
      ζ (c₀ * c₁) r (m₀ + m₁)
      (∑ i ∈ J, A i * M i) (∑ i ∈ J, AD i * MD i) := by
    apply normalizedFunctionalEquation_absorb_sign_iff.mpr
    simpa only [absorbedFunctionalEquationSign, mul_assoc] using hs
  exact normalizedFunctionalEquation_mul_dual_sign hsigned

namespace Padic

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance productFEFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance productFEValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance productFELocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The literal model-star/reflected matrix finite sums obey the ambient
normalized functional equation with product polynomials and epsilon units,
the sum of Laurent exponents, and exactly the ambient sign exponent. -/
theorem adjacentRank_reflectedFiniteProducts_functionalEquation
    (χ : Quasicharacter F.Carrier) (r N : ℕ)
    (A AD M MD : Fin N → RationalFunctions)
    (P₀ PD₀ P₁ PD₁ : Polynomial ℂ) (ζ c₀ c₁ : ℂˣ) (m₀ m₁ : ℤ)
    (hA : ∀ i, NormalizedFunctionalEquation
      F.canonicalTopologicalData.residueCardinality
      P₀ PD₀ ζ c₀ r m₀ (A i) (AD i))
    (hM : ∀ i, NormalizedFunctionalEquation
      F.canonicalTopologicalData.residueCardinality
      P₁ PD₁ 1 c₁ 0 m₁ (M i) (MD i)) :
    NormalizedFunctionalEquation F.canonicalTopologicalData.residueCardinality
      (P₀ * P₁) (PD₀ * PD₁) ζ (c₀ * c₁) (r + 1) (m₀ + m₁)
      (∑ i, A i * M i)
      (RatFunc.C (adjacentRankModelStarScalar F χ r) *
        ∑ i, AD i * (RatFunc.C (adjacentRankDualMatrixReflectionScalar F χ r ζ : ℂ) *
          MD i)) := by
  rw [adjacentRankModelStar_reflectedProduct_cancel]
  exact normalizedFunctionalEquation_adjacent_sum_mul
    F.canonicalTopologicalData.residueCardinality_gt_one Finset.univ A AD M MD
    (fun i _ => hA i) (fun i _ => hM i)

end Padic
end Langlands.RankinSelberg

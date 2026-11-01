import Langlands.Analysis.Local.QuotientAutomorphismProof
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonReflectedHaar
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Langlands.Representation.RankinSelberg.GeneralLinearUnimodularity

/-!
# The reflection `[v] ↦ [w v^ι]` of the small quotient

On `N \ GL_(n+1)` the map `[v] ↦ [w v^ι]`, with `w` the long Weyl element and `ι` the
inverse transpose, is a well-defined involutive homeomorphism. It preserves every
compatible quotient measure and exchanges the determinant slices `k` and `-k`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory MeasureTheory.Measure GeneralLinear QuotientIntegration Whittaker
open scoped NNReal ENNReal

universe uG uK uF

/-- An involutive continuous automorphism has Haar modulus one. -/
theorem mulEquivHaarChar_eq_one_of_involutive
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (e : G ≃ₜ* G) (he : Function.Involutive e) :
    mulEquivHaarChar e = 1 := by
  have hee : e.trans e = ContinuousMulEquiv.refl G := by
    ext g
    exact he g
  have hsq : mulEquivHaarChar e * mulEquivHaarChar e = 1 := by
    rw [← mulEquivHaarChar_trans, hee, mulEquivHaarChar_refl]
  apply NNReal.coe_injective
  apply (pow_eq_one_iff_of_nonneg (NNReal.coe_nonneg _) (by decide : 2 ≠ 0)).mp
  simpa only [pow_two, NNReal.coe_mul, NNReal.coe_one] using
    congrArg (fun c : ℝ≥0 => (c : ℝ)) hsq

section Reflection

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K] (n : ℕ)

/-- The continuous automorphism `g ↦ w g^ι w` of `GL_(n+1)`. -/
def reflectionAut : GeneralLinear (n + 1) K ≃ₜ* GeneralLinear (n + 1) K where
  toFun g := weylLong (n + 1) K * inverseTranspose (n + 1) K g * weylLong (n + 1) K
  invFun g := weylLong (n + 1) K * inverseTranspose (n + 1) K g * weylLong (n + 1) K
  left_inv g := by
    simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive]
    calc weylLong (n + 1) K * (weylLong (n + 1) K * g * weylLong (n + 1) K) *
          weylLong (n + 1) K =
        (weylLong (n + 1) K * weylLong (n + 1) K) * g *
          (weylLong (n + 1) K * weylLong (n + 1) K) := by simp only [mul_assoc]
      _ = g := by rw [weylLong_mul_self, one_mul, mul_one]
  right_inv g := by
    simp only [map_mul, inverseTranspose_weylLong, inverseTranspose_involutive]
    calc weylLong (n + 1) K * (weylLong (n + 1) K * g * weylLong (n + 1) K) *
          weylLong (n + 1) K =
        (weylLong (n + 1) K * weylLong (n + 1) K) * g *
          (weylLong (n + 1) K * weylLong (n + 1) K) := by simp only [mul_assoc]
      _ = g := by rw [weylLong_mul_self, one_mul, mul_one]
  map_mul' g g' := by
    simp only [map_mul]
    calc weylLong (n + 1) K * (inverseTranspose (n + 1) K g *
          inverseTranspose (n + 1) K g') * weylLong (n + 1) K =
        weylLong (n + 1) K * inverseTranspose (n + 1) K g *
          (weylLong (n + 1) K * weylLong (n + 1) K) *
          inverseTranspose (n + 1) K g' * weylLong (n + 1) K := by
          rw [weylLong_mul_self, mul_one]
          simp only [mul_assoc]
      _ = _ := by simp only [mul_assoc]
  continuous_toFun :=
    (continuous_const.mul (continuous_inverseTranspose (n + 1) K)).mul continuous_const
  continuous_invFun :=
    (continuous_const.mul (continuous_inverseTranspose (n + 1) K)).mul continuous_const

@[simp]
theorem reflectionAut_apply (g : GeneralLinear (n + 1) K) :
    reflectionAut n g =
      weylLong (n + 1) K * inverseTranspose (n + 1) K g * weylLong (n + 1) K := rfl

theorem reflectionAut_involutive : Function.Involutive (reflectionAut (K := K) n) :=
  (reflectionAut (K := K) n).left_inv

theorem reflectionAut_mem_iff (x : GeneralLinear (n + 1) K) :
    reflectionAut n x ∈ upperUnipotent (n + 1) K ↔ x ∈ upperUnipotent (n + 1) K := by
  constructor
  · intro hx
    rw [← reflectionAut_involutive n x]
    exact (reflectedUnipotent ⟨_, hx⟩).property
  · intro hx
    exact (reflectedUnipotent ⟨x, hx⟩).property

/-- The reflection `[v] ↦ [w v^ι]` of the small quotient. -/
def reflectionQuotient : LeftUnipotentQuotient n K ≃ₜ LeftUnipotentQuotient n K :=
  (quotientAutomorphism (upperUnipotent (n + 1) K) (reflectionAut n)
    (reflectionAut_mem_iff n)).trans
    (rightTranslate (upperUnipotent (n + 1) K) (weylLong (n + 1) K))

@[simp]
theorem reflectionQuotient_mk (g : GeneralLinear (n + 1) K) :
    reflectionQuotient n (Quotient.mk _ g) =
      Quotient.mk _ (weylLong (n + 1) K * inverseTranspose (n + 1) K g) := by
  change Quotient.mk _ (reflectionAut n g * weylLong (n + 1) K) = _
  rw [reflectionAut_apply, mul_assoc, weylLong_mul_self, mul_one]

theorem reflectionQuotient_involutive :
    Function.Involutive (reflectionQuotient (K := K) n) := by
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [reflectionQuotient_mk, reflectionQuotient_mk, map_mul, inverseTranspose_weylLong,
      inverseTranspose_involutive, ← mul_assoc, weylLong_mul_self, one_mul]

end Reflection

section Determinant

variable {K : Type uK} [Field K]

/-- The long Weyl determinant has absolute value one. -/
theorem abv_det_weylLong (abv : AbsoluteValue K ℝ) (r : ℕ) :
    abv (Matrix.det (weylLong r K).val) = 1 := by
  have he : Matrix.det (weylLong r K).val * Matrix.det (weylLong r K).val = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, weylLong_mul_self, Units.val_one, Matrix.det_one]
  apply (pow_eq_one_iff_of_nonneg (abv.nonneg _) (by decide : 2 ≠ 0)).mp
  rw [pow_two, ← map_mul, he, map_one]

/-- `|det(w g^ι)| = |det g|⁻¹`. -/
theorem abv_det_weylLong_mul_inverseTranspose (abv : AbsoluteValue K ℝ) {r : ℕ}
    (g : GeneralLinear r K) :
    abv (Matrix.det (weylLong r K * inverseTranspose r K g).val) =
      (abv (Matrix.det g.val))⁻¹ := by
  rw [Units.val_mul, Matrix.det_mul, map_mul, abv_det_weylLong, one_mul, inverseTranspose_coe,
    Matrix.det_transpose, ← map_inv₀]
  congr 1
  rw [Matrix.coe_units_inv, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']

end Determinant

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The reflection exchanges the determinant slices `k` and `-k`. -/
theorem reflectionQuotient_mem_determinantSlice (n : ℕ) (k : ℤ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    ∀ q : LeftUnipotentQuotient n F.Carrier,
      reflectionQuotient n q ∈ determinantSlice F.canonicalTopologicalData n k ↔
        q ∈ determinantSlice F.canonicalTopologicalData n (-k) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [reflectionQuotient_mk, mk_mem_determinantSlice_iff_normalizedAbs,
      mk_mem_determinantSlice_iff_normalizedAbs]
    have habs := abv_det_weylLong_mul_inverseTranspose (normalizedAbsoluteValue T) g
    change T.normalizedAbs (Matrix.det (weylLong (n + 1) F.Carrier *
      inverseTranspose (n + 1) F.Carrier g).val) = _ ↔
        T.normalizedAbs (Matrix.det g.val) = _
    change T.normalizedAbs _ = (T.normalizedAbs _)⁻¹ at habs
    rw [habs, neg_neg]
    have hq : (0 : ℝ) < T.residueCardinality := by
      exact_mod_cast (Nat.zero_lt_one.trans T.residueCardinality_gt_one)
    constructor
    · intro he
      rw [← inv_inv (T.normalizedAbs _), he, zpow_neg, inv_inv]
    · intro he
      rw [he, zpow_neg]

/-- The reflection preserves every compatible quotient measure on the small quotient. -/
theorem measurePreserving_reflectionQuotient (n : ℕ) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ νA : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) νA →
      MeasurePreserving (reflectionQuotient n) νA νA := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro νA hA
  have := T.fieldT2
  have := T.generalLinearLocallyCompactSpace (n + 1)
  have := T.generalLinearT2Space (n + 1)
  have hclosed : IsClosed (upperUnipotent (n + 1) F.Carrier : Set (GeneralLinear (n + 1) F.Carrier)) :=
    UpperUnipotent.isClosed
  have hscale := compatibleQuotientAutomorphismScaling
    (upperUnipotent (n + 1) F.Carrier) hclosed (generalLinearHaar F.Carrier n)
    (unipotentHaar F.Carrier n) νA hA (reflectionAut n) (reflectionAut_mem_iff n)
  dsimp only at hscale
  obtain ⟨hmap, -⟩ := hscale
  have : LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) := hclosed.locallyCompactSpace
  rw [mulEquivHaarChar_eq_one_of_involutive (reflectionAut n) (reflectionAut_involutive n),
    mulEquivHaarChar_eq_one_of_involutive _ (fun x => Subtype.ext (reflectionAut_involutive n x.val)),
    div_one, ENNReal.coe_one, one_smul] at hmap
  exact (hA.right_invariant (weylLong (n + 1) F.Carrier)).comp
    ⟨(quotientAutomorphism _ (reflectionAut n) (reflectionAut_mem_iff n)).continuous.measurable,
      hmap⟩

/-- Change of variables by the reflection on determinant slices. -/
theorem setIntegral_determinantSlice_reflectionQuotient (n : ℕ) (k : ℤ) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (n + 1)
    letI : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ νA : Measure (LeftUnipotentQuotient n F.Carrier),
      IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
        (unipotentHaar F.Carrier n) νA →
      ∀ (f : LeftUnipotentQuotient n F.Carrier → ℂ),
        (∫ q in determinantSlice T n k, f q ∂νA) =
          ∫ q in determinantSlice T n (-k), f (reflectionQuotient n q) ∂νA := by
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (n + 1)
  let : MeasurableSpace (GeneralLinear (n + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro νA hA f
  have hmp := measurePreserving_reflectionQuotient F n νA hA
  rw [← hmp.setIntegral_preimage_emb (reflectionQuotient n).measurableEmbedding f
    (determinantSlice T n k)]
  have hpre : reflectionQuotient n ⁻¹' determinantSlice T n k = determinantSlice T n (-k) :=
    Set.ext (reflectionQuotient_mem_determinantSlice F n k)
  rw [hpre]

end Padic

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

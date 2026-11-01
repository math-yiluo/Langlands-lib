import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentIntegrands
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentConvergence
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentRowSplit
import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockLaurentReflection
import Mathlib.Probability.Kernel.MeasurableLIntegral

/-!
# The two large first-block coefficients as row integrals of small coefficients

At a fixed representative `g`, the rectangular average over the lower radical of the upper
first-block average on the slice `k` is the row integral of `Φ((x, η) g)` times the
slice coefficient `k` of the original small integral of the translate by `R(0; x) g`.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

open MeasureTheory GeneralLinear TwoBlockJacquet TwoBlockFirstBlockQuotient
  TwoBlockLowerUnipotentQuotient TwoBlockLowerFirstBlockQuotient HarmonicAnalysis
  HarmonicAnalysis.TwoBlockRowPartialFourier QuotientIntegration Whittaker
open scoped ENNReal

universe uF uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
variable {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
variable {ψ : letI := F.canonicalTopologicalData.topology
  HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier}

/-- The upper coefficient at a representative: under absolute convergence of the iterated
fiber integral, it is the row integral of `Φ((x, η) g)` times the original small slice
coefficient of the translate by `R(0; x) g` and the first-block coefficient of `f(g)`. -/
theorem upper_coefficient_eq_rowIntegral (hr : t = m 0 + (m 1 + 0 + 1))
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
    ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA]
      (ν : AdditiveHaarMeasure F.Carrier) (k : ℤ) (g : GeneralLinear (t + 1) F.Carrier),
      AEStronglyMeasurable
        (Function.uncurry fun Z q =>
          TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g)))
        ((rectangularMeasure ν (m 1 + 1) (m 0 + 1)).prod
          (νA.restrict (determinantSlice T (m 0) k))) →
      (∫⁻ Z, ∫⁻ q, ‖TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g))‖ₑ
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) ≠ ⊤ →
      Integrable (fun x => Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ t Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k)
        (rowMeasure ν (m 0 + 1)) ∧
      (∫ Z, ∫ q, TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier Z * g))
          ∂νA.restrict (determinantSlice T (m 0) k)
          ∂rectangularMeasure ν (m 1 + 1) (m 0 + 1)) =
        ∫ x, Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 hr ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ t Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k
          ∂rowMeasure ν (m 0 + 1) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  intro νA _ ν k g hH hfin
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  obtain ⟨hint, heq⟩ := integral_rectangular_rowSnoc ν
    (νA.restrict (determinantSlice T (m 0) k)) (m 1) (m 0 + 1) _ hH hfin
  have hpt : ∀ x : Fin (m 0 + 1) → F.Carrier,
      (∫ q, ∫ y, TwoBlockUnfolding.integrand ell f Wtest Φ
          (fiberPoint h F.Carrier q (lowerRadical h F.Carrier
            (fun i => Fin.snoc (α := fun _ => Fin (m 0 + 1) → F.Carrier) (fun j => y j) x i) * g))
          ∂rectangularMeasure ν (m 1) (m 0 + 1) ∂νA.restrict (determinantSlice T (m 0) k)) =
        Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          unequalRankSliceCoefficientAt F (m 1) 0 rfl ψ νA
            (rectangularMeasure ν (m 1) (m 0 + 1))
            (translateWhittaker ψ _ Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g))
            (firstBlockCoefficient ell f g).val k := by
    intro x
    have hq : ∀ q : LeftUnipotentQuotient (m 0) F.Carrier,
        (∫ y, TwoBlockUnfolding.integrand ell f Wtest Φ
            (fiberPoint h F.Carrier q (lowerRadical h F.Carrier
              (fun i => Fin.snoc (α := fun _ => Fin (m 0 + 1) → F.Carrier)
                (fun j => y j) x i) * g))
            ∂rectangularMeasure ν (m 1) (m 0 + 1)) =
          (∫ y, unequalRankIntegrand ψ (normalizedAbsoluteValue T) (m 1) 0
              (translateWhittaker ψ _ Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g))
              (firstBlockCoefficient ell f g).val 0 y q
            ∂rectangularMeasure ν (m 1) (m 0 + 1)) *
            Φ (Matrix.vecMul
              (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) := by
      intro q
      induction q using Quotient.inductionOn with
      | h v =>
        rw [← integral_mul_const]
        congr 1
        funext y
        exact upperIntegrand_fiberPoint_rowSnoc h ell f Wtest Φ v y x g
    simp_rw [hq]
    rw [integral_mul_const, mul_comm]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [hpt] using hint
  · rw [heq]
    simp only [hpt]

/-- The row restriction `x ↦ Φ((x, η) g)` of a Schwartz–Bruhat function is integrable. -/
theorem integrable_rowRestriction
    (ψ' : letI := F.canonicalTopologicalData.topology
      HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (μ : letI := F.canonicalTopologicalData.topology
      letI : MeasurableSpace F.Carrier := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier)) (g : GeneralLinear (t + 1) F.Carrier) :
    letI := F.canonicalTopologicalData.topology
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    Integrable (fun x => Φ (Matrix.vecMul
        (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val))
      (rowMeasure μ (m 0 + 1)) := by
  let := F.canonicalTopologicalData.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure μ
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  have : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
  have : TotallyDisconnectedSpace F.Carrier := by
    let : NonarchimedeanRing F.Carrier := by
      convert! ValuativeRel.nonarchimedeanRing F.Carrier
      exact Valuation.toTopologicalSpace_eq _
    infer_instance
  have hint := rowPartialFourierIntegrand_integrable ψ' μ (succBlockEquiv h) (rowTranslate g Φ)
    0 (TwoBlockLowerUnfolding.eta (m 1))
  simpa only [rowTranslate_apply, rowPairing, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    AddChar.map_zero_eq_one, one_mul] using hint

/-- On the small slice `k`, the lower density `q^(-k b)`, the inverse half modulus and the
Jacobian `|det v|⁻¹` combine to `q^k` times the transformed small determinant weight. -/
theorem lower_slice_scalar (k : ℤ) (v : GeneralLinear (m 0 + 1) F.Carrier)
    (hv : letI := F.canonicalTopologicalData.topology
      (Quotient.mk _ v : LeftUnipotentQuotient (m 0) F.Carrier) ∈
        determinantSlice F.canonicalTopologicalData (m 0) k) :
    (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(((m 1 + 1 : ℕ) : ℂ) / 2)) *
        ((F.canonicalTopologicalData.normalizedAbs (Matrix.det v.val))⁻¹ : ℂ) =
      (F.canonicalTopologicalData.residueCardinality : ℂ) ^ k *
        determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) v
          (-(0 - ((0 + m 1 + 1 : ℕ) : ℂ) / 2)) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  set q := T.residueCardinality with hq_def
  have hq1 : 1 < q := T.residueCardinality_gt_one
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (Nat.zero_lt_one.trans hq1).ne'
  have hord : T.ord (Matrix.det v.val) = k := hv
  have habs : T.normalizedAbs (Matrix.det v.val) = (q : ℝ) ^ (-k) :=
    (mk_mem_determinantSlice_iff_normalizedAbs T).mp hv
  rw [normalizedDeterminantWeight_eq_spectralPoint_zpow, normalizedDeterminantWeight_eq_spectralPoint_zpow,
    hord, habs]
  simp only [spectralPoint, neg_neg, zero_sub, Nat.zero_add]
  set X : ℂ := (q : ℂ) ^ ((((m 1 + 1 : ℕ) : ℂ)) / 2) with hX_def
  have hX : X ≠ 0 := by
    rw [hX_def]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hq0)
  have hXinv : (T.residueCardinality : ℂ) ^ (-((((m 1 + 1 : ℕ) : ℂ)) / 2)) = X⁻¹ := by
    rw [hX_def, Complex.cpow_neg]
  have hX2 : X ^ 2 = (q : ℂ) ^ (m 1 + 1) := by
    rw [hX_def, ← Complex.cpow_nat_mul, ← Complex.cpow_natCast]
    congr 1
    push_cast
    ring
  have hcast : (((q : ℝ) ^ (-k) : ℝ) : ℂ) = (q : ℂ) ^ (-k) := by push_cast; rfl
  have hY : (X ^ k) ^ 2 = (q : ℂ) ^ (k * ((m 1 + 1 : ℕ) : ℤ)) := by
    rw [← zpow_natCast (X ^ k) 2, ← zpow_mul, mul_comm k, zpow_mul, zpow_natCast, hX2,
      ← zpow_natCast (q : ℂ) (m 1 + 1), ← zpow_mul, mul_comm]
  have hXk : X ^ k ≠ 0 := zpow_ne_zero _ hX
  have hqk : (q : ℂ) ^ k ≠ 0 := zpow_ne_zero _ hq0
  rw [hcast, hXinv, inv_zpow, zpow_neg, ← hY, zpow_neg, inv_inv]
  field_simp

/-- The lower coefficient at a representative: the lower density times the first-block
average on the slice `k` is the row integral of `Φ((x, η) g)` times the reflected series
of the transformed small slice coefficients of the translate by `R(0; x) g`. -/
theorem lower_coefficient_eq_rowIntegral (hlt : m 0 < t) (hr : t = m 0 + (0 + m 1 + 1))
    (ell : letI := F.canonicalTopologicalData.topology
      ∀ i, glInverseFunctionals ψ (m i) (σ i))
    (f : Sections F h σ)
    (Wtest : letI := F.canonicalTopologicalData.topology
      RankinSelberg.WhittakerFunctions ψ t)
    (Φ : letI := F.canonicalTopologicalData.topology
      SchwartzBruhat (Fin (t + 1) → F.Carrier))
    (Kf : (Fin (m 0 + 1) → F.Carrier) → LeftUnipotentQuotient (m 0) F.Carrier → ℂ) :
    let T := F.canonicalTopologicalData
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    letI : MeasurableSpace (GeneralLinear (m 0 + 1) F.Carrier) := borel _
    letI : BorelSpace (GeneralLinear (m 0 + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (upperUnipotent (m 0 + 1) F.Carrier) := borel _
    letI : BorelSpace (upperUnipotent (m 0 + 1) F.Carrier) := ⟨rfl⟩
    letI : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
    letI : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
    ∀ (νA : Measure (LeftUnipotentQuotient (m 0) F.Carrier)) [SigmaFinite νA],
      IsCompatible (upperUnipotent (m 0 + 1) F.Carrier) (generalLinearHaar F.Carrier (m 0))
        (unipotentHaar F.Carrier (m 0)) νA →
      ∀ (ν : AdditiveHaarMeasure F.Carrier) (k : ℤ) (g : GeneralLinear (t + 1) F.Carrier),
      (∀ x v, Kf x (Quotient.mk _ v) = ψ.complex (Matrix.vecMul x (v⁻¹).val 0)) →
      AEStronglyMeasurable (Function.uncurry Kf)
        ((rowMeasure ν (m 0 + 1)).prod (νA.restrict (determinantSlice T (m 0) k))) →
      (∀ x q, ‖Kf x q‖ ≤ 1) →
      Integrable (fun q => ∫ z, unequalRankIntegrandAt F 0 (m 1) hr (ψ.scale (-1))
            (normalizedAbsoluteValue T)
            (translateWhittaker (ψ.scale (-1)) t
              (firstDualFunction ψ t (translateWhittaker ψ t Wtest g)) (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) 0 z
            (reflectionQuotient (m 0) q)
          ∂rectangularMeasure ν 0 (m 0 + 1)) (νA.restrict (determinantSlice T (m 0) k)) →
      Integrable (fun x => Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F 0 (m 1) hr
            (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1))
            (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t
              (translateWhittaker ψ t Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g)))
              (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) k)
        (rowMeasure ν (m 0 + 1)) ∧
      (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          (∫ q in determinantSlice T (m 0) k, TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν
            (firstBlockFiberPoint F h q g) ∂νA) =
        ∫ x, Φ (Matrix.vecMul
            (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val) *
          reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F 0 (m 1) hr
            (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1))
            (translateWhittaker (ψ.scale (-1)) t (firstDualFunction ψ t
              (translateWhittaker ψ t Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g)))
              (blockWeylAt (m 0) t hlt))
            (secondDualFunction ψ (m 0) (firstBlockCoefficient ell f g).val) n) k
          ∂rowMeasure ν (m 0 + 1) := by
  subst hr
  intro T
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.generalLinearTopologicalGroup (m 0 + 1)
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear (m 0 + 1) F.Carrier) := borel _
  let : BorelSpace (GeneralLinear (m 0 + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (upperUnipotent (m 0 + 1) F.Carrier) := borel _
  let : BorelSpace (upperUnipotent (m 0 + 1) F.Carrier) := ⟨rfl⟩
  let : MeasurableSpace (LeftUnipotentQuotient (m 0) F.Carrier) := borel _
  let : BorelSpace (LeftUnipotentQuotient (m 0) F.Carrier) := ⟨rfl⟩
  intro νA _ hνA ν k g hKf hKm hKle hA
  have := TwoBlockLowerUnfolding.sigmaFinite_additiveHaarMeasure ν
  let Fg := (firstBlockCoefficient ell f g).val
  let Wd : (Fin (m 0 + 1) → F.Carrier) → _ := fun x =>
    translateWhittaker (ψ.scale (-1)) _ (firstDualFunction ψ _
      (translateWhittaker ψ _ Wtest (lowerRadical h F.Carrier (rowSnoc 0 x) * g)))
      (blockWeylAt (m 0) _ hlt)
  let A : LeftUnipotentQuotient (m 0) F.Carrier → ℂ := fun q =>
    ∫ z, unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue T) 0 (m 1)
      (translateWhittaker (ψ.scale (-1)) _
        (firstDualFunction ψ _ (translateWhittaker ψ _ Wtest g)) (blockWeylAt (m 0) _ hlt))
      (secondDualFunction ψ (m 0) Fg) 0 z (reflectionQuotient (m 0) q)
      ∂rectangularMeasure ν 0 (m 0 + 1)
  let Φ' : (Fin (m 0 + 1) → F.Carrier) → ℂ := fun x =>
    Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
  have hΦ : Integrable Φ' (rowMeasure ν (m 0 + 1)) := integrable_rowRestriction ψ ν Φ g
  have hfac : ∀ x q, (∫ z, unequalRankIntegrand (ψ.scale (-1)) (normalizedAbsoluteValue T)
      0 (m 1) (Wd x) (secondDualFunction ψ (m 0) Fg) 0 z (reflectionQuotient (m 0) q)
      ∂rectangularMeasure ν 0 (m 0 + 1)) = Kf x q * A q := by
    intro x q
    induction q using Quotient.inductionOn with
    | h v =>
      simp only [A, Wd, rectangularMeasure_zero_rows, integral_dirac]
      rw [dualIntegrand_reflectionQuotient h hlt, dualIntegrand_reflectionQuotient h hlt,
        translateWhittaker_apply, translateWhittaker_apply, mul_assoc (blockRotation h F.Carrier),
        mul_assoc (blockRotation h F.Carrier), whittaker_blockRotation_firstBlockEmbedding_lowerRadical,
        hKf]
      ring
  have ha' : ∀ x, unequalRankSliceCoefficientAt F 0 (m 1) rfl (ψ.scale (-1)) νA
      (rectangularMeasure ν 0 (m 0 + 1)) (Wd x) (secondDualFunction ψ (m 0) Fg) (-k) =
      ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA := by
    intro x
    change (∫ q in determinantSlice T (m 0) (-k), ∫ z, unequalRankIntegrand (ψ.scale (-1))
        (normalizedAbsoluteValue T) 0 (m 1) (Wd x) (secondDualFunction ψ (m 0) Fg) 0 z q
        ∂rectangularMeasure ν 0 (m 0 + 1) ∂νA) = _
    rw [setIntegral_determinantSlice_reflectionQuotient F (m 0) (-k) νA hνA, neg_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun q => hfac x q)
  obtain ⟨hint3, heq3⟩ := integral_mul_integral_swap (νA.restrict (determinantSlice T (m 0) k))
    (rowMeasure ν (m 0 + 1)) A Φ' Kf hA hΦ hKm hKle
  have hrefl : ∀ x, reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F
      0 (m 1) rfl (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
      (secondDualFunction ψ (m 0) Fg) n) k =
      (T.residueCardinality : ℂ) ^ k *
        ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA := by
    intro x
    change (T.residueCardinality : ℂ) ^ k * unequalRankSliceCoefficientAt F 0 (m 1) rfl
      (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
      (secondDualFunction ψ (m 0) Fg) (-k) = _
    rw [ha' x]
  refine ⟨?_, ?_⟩
  · refine (hint3.const_mul ((T.residueCardinality : ℂ) ^ k)).congr
      (Filter.Eventually.of_forall fun x => ?_)
    change (T.residueCardinality : ℂ) ^ k *
        (Φ' x * ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA) =
      Φ' x * reflectSeries T.residueCardinality _ k
    rw [hrefl x]
    ring
  · have hpt : ∀ q ∈ determinantSlice T (m 0) k,
        (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
            TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν (firstBlockFiberPoint F h q g) =
          (T.residueCardinality : ℂ) ^ k *
            (A q * ∫ x, Kf x q * Φ' x ∂rowMeasure ν (m 0 + 1)) := by
      intro q hq
      induction q using Quotient.inductionOn with
      | h v =>
        have hI : (∫ x, Kf x (Quotient.mk _ v) * Φ' x ∂rowMeasure ν (m 0 + 1)) =
            ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
              Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
              ∂rowMeasure ν (m 0 + 1) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by
            dsimp only [Φ']
            rw [hKf])
        rw [hI, lowerIntegrand_firstBlockFiberPoint ell f Wtest Φ ν v g]
        simp only [A, rectangularMeasure_zero_rows, integral_dirac]
        rw [dualIntegrand_reflectionQuotient h hlt, translateWhittaker_apply,
          mul_assoc (blockRotation h F.Carrier)]
        linear_combination
          (Wtest.val (blockRotation h F.Carrier * (firstBlockEmbedding h F.Carrier v * g)) *
            Fg.val v *
            ∫ x, ψ.complex (Matrix.vecMul x (v⁻¹).val 0) *
              Φ (Matrix.vecMul (join (succBlockEquiv h) x (TwoBlockLowerUnfolding.eta (m 1))) g.val)
              ∂rowMeasure ν (m 0 + 1)) * lower_slice_scalar k v hq
    calc (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
          (∫ q in determinantSlice T (m 0) k, TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν
            (firstBlockFiberPoint F h q g) ∂νA)
        = ∫ q in determinantSlice T (m 0) k,
            (T.residueCardinality : ℂ) ^ (-(k * ((m 1 + 1 : ℕ) : ℤ))) *
              TwoBlockLowerUnfolding.integrand ell f Wtest Φ ν (firstBlockFiberPoint F h q g)
            ∂νA := (integral_const_mul _ _).symm
      _ = ∫ q in determinantSlice T (m 0) k, (T.residueCardinality : ℂ) ^ k *
            (A q * ∫ x, Kf x q * Φ' x ∂rowMeasure ν (m 0 + 1)) ∂νA :=
          setIntegral_congr_fun (measurableSet_determinantSlice T (m 0) k) hpt
      _ = (T.residueCardinality : ℂ) ^ k * ∫ x, Φ' x *
            ∫ q in determinantSlice T (m 0) k, Kf x q * A q ∂νA ∂rowMeasure ν (m 0 + 1) := by
          rw [integral_const_mul, heq3]
      _ = ∫ x, Φ' x * reflectSeries T.residueCardinality (fun n => unequalRankSliceCoefficientAt F
            0 (m 1) rfl (ψ.scale (-1)) νA (rectangularMeasure ν 0 (m 0 + 1)) (Wd x)
            (secondDualFunction ψ (m 0) Fg) n) k ∂rowMeasure ν (m 0 + 1) := by
          rw [← integral_const_mul]
          refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [hrefl x]
          ring

/-- Composite Tonelli laws make the iterated absolute fiber integral of an integrable
function finite at almost every base point. -/
theorem ae_lintegral_kernel_comp_lt_top {L M H : Type*} [MeasurableSpace L]
    [MeasurableSpace M] [MeasurableSpace H] (ν0 : Measure L) (νM0 : Measure M) (νH : Measure H)
    (κR : ProbabilityTheory.Kernel L M) (κ : ProbabilityTheory.Kernel M H)
    [ProbabilityTheory.IsSFiniteKernel κR] [ProbabilityTheory.IsSFiniteKernel κ]
    (c : ℝ≥0∞) (hc : c ≠ ⊤)
    (h2 : ∀ f : M → ℝ≥0∞, Measurable f →
      (∫⁻ z, ∫⁻ y, f y ∂κR z ∂ν0) = c * ∫⁻ y, f y ∂νM0)
    (h6 : ∀ f : H → ℝ≥0∞, Measurable f →
      (∫⁻ y, ∫⁻ w, f w ∂κ y ∂νM0) = ∫⁻ w, f w ∂νH)
    (E : H → ℂ) (hEm : Measurable E) (hE : Integrable E νH) :
    ∀ᵐ z ∂ν0, (∫⁻ y, ∫⁻ w, ‖E w‖ₑ ∂κ y ∂κR z) < ⊤ := by
  have hF : Measurable fun y => ∫⁻ w, ‖E w‖ₑ ∂κ y := hEm.enorm.lintegral_kernel
  have hG : Measurable fun z => ∫⁻ y, ∫⁻ w, ‖E w‖ₑ ∂κ y ∂κR z := hF.lintegral_kernel
  refine ae_lt_top hG ?_
  rw [h2 _ hF, h6 _ hEm.enorm]
  exact ENNReal.mul_ne_top hc hE.2.ne

end Langlands.RankinSelberg.TwoBlockFirstBlockLaurent

import Langlands.Representation.RankinSelberg.TwoBlockDominantRectangleUnfolding

/-! # Integrated radical unfolding of the actual unequal-rank section -/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.RankinSelberg.TwoBlockDominantFirstBlock

open MeasureTheory GeneralLinear Whittaker HarmonicAnalysis QuotientIntegration
  TwoBlockJacquet TwoBlockUnipotentQuotient
open scoped ENNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance radicalUnfoldingTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance radicalUnfoldingValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance radicalUnfoldingLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance radicalUnfoldingT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance radicalUnfoldingCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance radicalUnfoldingGLTopology (a : ℕ) :
    IsTopologicalGroup (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearTopologicalGroup a
local instance radicalUnfoldingGLLocalCompact (a : ℕ) :
    LocallyCompactSpace (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearLocallyCompactSpace a
local instance radicalUnfoldingGLCountable (a : ℕ) :
    SecondCountableTopology (GeneralLinear a F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology a
local instance radicalUnfoldingMeasurable : MeasurableSpace F.Carrier := borel _
local instance radicalUnfoldingBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance radicalUnfoldingGLMeasurable (a : ℕ) :
    MeasurableSpace (GeneralLinear a F.Carrier) := borel _
local instance radicalUnfoldingGLBorel (a : ℕ) :
    BorelSpace (GeneralLinear a F.Carrier) := ⟨rfl⟩
local instance radicalUnfoldingNMeasurable (a : ℕ) :
    MeasurableSpace (upperUnipotent a F.Carrier) := borel _
local instance radicalUnfoldingNBorel (a : ℕ) :
    BorelSpace (upperUnipotent a F.Carrier) := ⟨rfl⟩
local instance radicalUnfoldingNCountable (a : ℕ) :
    SecondCountableTopology (upperUnipotent a F.Carrier) :=
  Topology.IsEmbedding.subtypeVal.secondCountableTopology
local instance radicalUnfoldingNQMeasurable (a : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient a F.Carrier) := borel _
local instance radicalUnfoldingNQBorel (a : ℕ) :
    BorelSpace (LeftUnipotentQuotient a F.Carrier) := ⟨rfl⟩

variable {t : ℕ} {m : Fin 2 → ℕ} {h : ∑ i, (m i + 1) = t + 1}
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  {σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i)}
  {ψ : UnitaryAdditiveCharacter F.Carrier}

local instance radicalUnfoldingHMeasurable :
    MeasurableSpace (blockUnipotent h F.Carrier) := borel _
local instance radicalUnfoldingHBorel :
    BorelSpace (blockUnipotent h F.Carrier) := ⟨rfl⟩
local instance radicalUnfoldingHQMeasurable :
    MeasurableSpace (BlockQuotient h F.Carrier) := borel _
local instance radicalUnfoldingHQBorel :
    BorelSpace (BlockQuotient h F.Carrier) := ⟨rfl⟩

/-- The actual determinant weight on the standard unipotent quotient. -/
def quotientDeterminantWeight (n : ℕ) (s : ℂ)
    (q : LeftUnipotentQuotient n F.Carrier) : ℂ :=
  (quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n q : ℂ) ^ s

@[simp] theorem quotientDeterminantWeight_mk (n : ℕ) (s : ℂ)
    (g : GeneralLinear (n + 1) F.Carrier) :
    quotientDeterminantWeight F n s (Quotient.mk _ g) =
      determinantWeight (normalizedAbsoluteValue F.canonicalTopologicalData) g s := rfl

theorem quotientDeterminantWeight_continuous (n : ℕ) (s : ℂ) :
    Continuous (quotientDeterminantWeight F n s) := by
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
  have hdet : Continuous (fun g : GeneralLinear (n + 1) F.Carrier =>
      normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp F.canonicalTopologicalData.continuous_normalizedAbsHom).comp
      Units.continuous_val.matrix_det
  exact (Complex.continuous_ofReal.comp hdet).cpow continuous_const
    (fun g => Complex.ofReal_mem_slitPlane.mpr
      ((normalizedAbsoluteValue F.canonicalTopologicalData).pos g.det_ne_zero))

variable (ell : ∀ i, glInverseFunctionals ψ (m i) (σ i))
  (f : Sections F h σ)
  (μR : Measure (Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier))
  [μR.IsAddHaarMeasure]
  (Wjac : InverseWhittakerFunctions ψ t)
  (hjac : ∀ g : GeneralLinear (t + 1) F.Carrier,
    Wjac.val g = jacquetFunction ψ (fun i => (ell i).val) μR f g)

include hjac in
/-- The signed average at each actual rectangle is the actual JPSS integrand
when the inverse-character function is realized by the ordinary Jacquet integral. -/
theorem radicalAverage_rectangularSectionIntegrand (j k : ℕ)
    (Wtest : WhittakerFunctions ψ (t + (j + k + 1))) (s : ℂ)
    (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier) :
    radicalAverage F h μR
      (rectangularSectionIntegrand F ell f j k Wtest
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)) x) =
      unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wtest Wjac s x := by
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    change radicalAverage F h μR
      (sectionIntegrand F ell f (rectangularWhittaker F j k Wtest x)
        (quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)))
          (Quotient.mk _ g) = _
    rw [sectionAverage_mk, unequalRankIntegrand_mk, rectangularWhittaker_apply,
      quotientDeterminantWeight_mk, hjac]

private theorem radical_continuous_appendIdentity (n d : ℕ) :
    Continuous (appendIdentity (F := F.Carrier) n d) := by
  induction d with
  | zero => exact continuous_id
  | succ d ih => exact (GeneralLinear.rankInclusionContinuous 1).continuous.comp ih

private theorem radical_coefficient_continuous {r : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hπ : IsSmooth π) (lambda : glFunctionals ψ r π)
    (Wtest : (coefficientModel π lambda).toSubmodule) : Continuous Wtest.val.val := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π lambda Wtest
  exact (matrixCoefficient_isLocallyConstant π lambda.val v (hπ v)).continuous

include hjac in
/-- Raw Jacquet convergence gives genuine product convergence on both sides
and the normalized unfolding after integrating the actual external rectangle. -/
theorem rectangularSection_slice_unfolding (j k : ℕ)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GeneralLinear (t + (j + k + 1) + 1) F.Carrier) V)
    (hπ : IsOfWhittakerType (t + (j + k + 1))
      (standardCharacter ψ (t + (j + k + 1))) π)
    (lambda : glFunctionals ψ (t + (j + k + 1)) π)
    (Wtest : (coefficientModel π lambda).toSubmodule)
    (hraw : IsAbsIntegrable ψ (fun i => (ell i).val) μR f)
    (ν : AdditiveHaarMeasure F.Carrier)
    (νN : Measure (LeftUnipotentQuotient t F.Carrier)) [SigmaFinite νN]
    (νH : Measure (BlockQuotient h F.Carrier)) [SigmaFinite νH]
    (hνN : IsCompatible (upperUnipotent (t + 1) F.Carrier)
      (generalLinearHaar F.Carrier t) (unipotentHaar F.Carrier t) νN)
    (hνH : IsCompatible (blockUnipotent h F.Carrier)
      (generalLinearHaar F.Carrier t) (blockHaar F.Carrier h) νH) (a : ℤ) (s : ℂ) :
    let weight := quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)
    let slice := RankinSelberg.determinantSlice F.canonicalTopologicalData t a
    let E := rectangularSectionIntegrand F ell f j k Wtest.val weight
    let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer}
    Integrable (fun z : LeftUnipotentQuotient t F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
      unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wtest.val Wjac s z.2 z.1)
      ((νN.restrict slice).prod (rectangularMeasure ν j (t + 1))) ∧
    Integrable (fun z : BlockQuotient h F.Carrier ×
        Matrix (Fin j) (Fin (t + 1)) F.Carrier => E z.2 z.1)
      ((νH.restrict (projection h F.Carrier ⁻¹' slice)).prod
        (rectangularMeasure ν j (t + 1))) ∧
    (∫ q, ∫ x, unequalRankIntegrand ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) j k Wtest.val Wjac s x q
        ∂rectangularMeasure ν j (t + 1) ∂νN.restrict slice) =
      c.toReal • (∫ z, ∫ x, E x z ∂rectangularMeasure ν j (t + 1)
        ∂νH.restrict (projection h F.Carrier ⁻¹' slice)) := by
  classical
  dsimp only
  let weight := quotientDeterminantWeight F t (s - ((j + k + 1 : ℕ) : ℂ) / 2)
  let slice := RankinSelberg.determinantSlice F.canonicalTopologicalData t a
  let c := μR {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F.Carrier).integer}
  have hw : Continuous weight := quotientDeterminantWeight_continuous F t _
  let : SigmaFinite ν.measure := inferInstance
  obtain ⟨d, φ, fs, he⟩ := exists_rectangularSectionExpansion F j k π hπ lambda Wtest
  let DH (i : Fin d) := sectionIntegrand F ell f
    (diagonalWhittaker ψ (j + k + 1) (fs i).val) weight
  let DN (i : Fin d) := unequalRankIntegrand ψ
    (normalizedAbsoluteValue F.canonicalTopologicalData) j k (fs i).val Wjac s 0
  have havg (i : Fin d) : radicalAverage F h μR (DH i) = DN i := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [DH, DN, sectionAverage_mk, unequalRankIntegrand_mk,
        UnequalRankReduction.unequalRankMatrix_at_zero, weight, quotientDeterminantWeight_mk]
      rw [hjac]
      rfl
  have hdiag (i : Fin d) : Integrable (DH i)
      (νH.restrict (projection h F.Carrier ⁻¹' slice)) ∧
      Integrable (DN i) (νN.restrict slice) ∧
      (∫ q, DN i q ∂νN.restrict slice) =
        c.toReal • (∫ z, DH i z ∂νH.restrict (projection h F.Carrier ⁻¹' slice)) := by
    have hc : Continuous (diagonalWhittaker ψ (j + k + 1) (fs i).val).val :=
      (radical_coefficient_continuous F π hπ.1.1 lambda (fs i)).comp
        (radical_continuous_appendIdentity F t (j + k + 1))
    obtain ⟨hH, _, hN, hEq⟩ := sectionIntegrand_slice_unfolding F ell f _ weight μR
      hc hw hraw νN νH hνN hνH a
      (diagonalWhittaker_slice_hasCompactSupport F t (j + k) ψ π hπ.1.1 lambda (fs i) a)
    rw [havg] at hN hEq
    exact ⟨hH, hN, hEq⟩
  have hφ (i : Fin d) : Integrable (φ i) (rectangularMeasure ν j (t + 1)) :=
    UnequalRankReduction.padic_rectangular_schwartz_integrable
      F F.canonicalTopologicalData j (t + 1) ν (φ i)
  have eN (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
      (q : LeftUnipotentQuotient t F.Carrier) :
      unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wtest.val Wjac s x q = ∑ i, DN i q * φ i x :=
    UnequalRankReduction.integrand_of_finite_expansion ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData) j k d Wtest.val Wjac
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he s x q
  have eH (x : Matrix (Fin j) (Fin (t + 1)) F.Carrier)
      (z : BlockQuotient h F.Carrier) :
      rectangularSectionIntegrand F ell f j k Wtest.val weight x z =
        ∑ i, DH i z * φ i x :=
    rectangularSectionIntegrand_expansion F ell f j k d Wtest.val weight
      (fun i => (φ i : _ → ℂ)) (fun i => (fs i).val) he x z
  have hNp : Integrable (fun z : LeftUnipotentQuotient t F.Carrier ×
      Matrix (Fin j) (Fin (t + 1)) F.Carrier =>
      unequalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        j k Wtest.val Wjac s z.2 z.1)
      ((νN.restrict slice).prod (rectangularMeasure ν j (t + 1))) := by
    simp_rw [eN]
    exact UnequalRankReduction.integrable_separated_sum Finset.univ _ _
      (fun i _ => (hdiag i).2.1) (fun i _ => hφ i)
  have hHp := rectangularSectionIntegrand_integrable F ell f j k π hπ lambda Wtest
    weight hw μR hraw ν νN νH hνN hνH a
  refine ⟨hNp, hHp, ?_⟩
  calc
    _ = ∫ x, ∫ q, unequalRankIntegrand ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) j k Wtest.val Wjac s x q
          ∂νN.restrict slice ∂rectangularMeasure ν j (t + 1) :=
      integral_integral_swap hNp
    _ = ∫ x, c.toReal • (∫ z,
        rectangularSectionIntegrand F ell f j k Wtest.val weight x z
          ∂νH.restrict (projection h F.Carrier ⁻¹' slice))
            ∂rectangularMeasure ν j (t + 1) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp_rw [eN, eH]
        rw [integral_finsetSum _ (fun i _ => ((hdiag i).2.1).mul_const (φ i x)),
          integral_finsetSum _ (fun i _ => ((hdiag i).1).mul_const (φ i x))]
        simp_rw [integral_mul_const, (hdiag _).2.2]
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i _
        exact smul_mul_assoc c.toReal _ (φ i x)
    _ = c.toReal • (∫ x, ∫ z,
        rectangularSectionIntegrand F ell f j k Wtest.val weight x z
          ∂νH.restrict (projection h F.Carrier ⁻¹' slice)
            ∂rectangularMeasure ν j (t + 1)) := integral_smul _ _
    _ = _ := congrArg (fun v : ℂ => c.toReal • v) (integral_integral_swap hHp.swap)

end Langlands.RankinSelberg.TwoBlockDominantFirstBlock

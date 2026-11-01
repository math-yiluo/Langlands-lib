import Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution
import Langlands.Representation.RankinSelberg.AdjacentRankMatchedInnerSlices

/-! Matched actual shell convolutions with a supplied finite inner expansion. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators Topology

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance matchedShellFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance matchedShellValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance matchedShellLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance matchedShellFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance matchedShellGroupMeasurable (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance matchedShellGroupBorel (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedShellUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance matchedShellUnipotentBorel (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance matchedShellQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance matchedShellQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩
local instance matchedShellQuotientT2 (r : ℕ) : T2Space (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_t2Space _ (GeneralLinear.UpperUnipotent.isClosed (R := F.Carrier))
local instance matchedShellGroupSecondCountable (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance matchedShellGroupSigmaCompact (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance matchedShellQuotientSecondCountable (r : ℕ) : SecondCountableTopology
    (LeftUnipotentQuotient r F.Carrier) :=
  TopologicalSpace.Quotient.secondCountableTopology
    (leftQuotient_isOpenQuotientMap
      (GeneralLinear.upperUnipotent (r + 1) F.Carrier)).isOpenMap
local instance matchedShellQuotientLocallyCompact (r : ℕ) : LocallyCompactSpace
    (LeftUnipotentQuotient r F.Carrier) :=
  leftQuotient_locallyCompactSpace _

/-- The actual finite shell convolution, including integrability of both
product kernels and all quotient and group slice factors. -/
def AdjacentRankShellConvolutionAt {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Lq Lh : ℤ) (B : Fin N → InverseWhittakerFunctions ψ r)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ) (m : ℤ) (s : ℂ) : Prop :=
  let a := adjacentRankInnerMultiplier F χ s
  let η := generalLinearHaar F.Carrier r
  let after := adjacentRankJointShellKernel F ψ W W' Φ φ a m
  let before := adjacentRankBeforeShearKernel F ψ W W' Φ φ a m
  let rhs := ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
    equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W (B i) φ k *
      ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η
  Integrable before (ν.prod η) ∧ Integrable after (ν.prod η) ∧
    (∀ k i, Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
      (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W (B i) φ 0)) ν) ∧
    (∀ j i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j s h * f i h) η) ∧
    (∫ z, after z ∂ν.prod η) = rhs ∧
    (∫ q, ∫ h, before (q, h) ∂η ∂ν) = rhs

set_option maxHeartbeats 1600000 in
/-- Carry a supplied inner expansion through the actual quotient shear and
finite determinant partition, retaining its exact family and coefficients. -/
theorem adjacentRankShell_finiteConvolution_of_innerSeparation {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (W' : InverseWhittakerFunctions ψ r) (hW' : Continuous W'.val)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ F.canonicalTopologicalData.ord (determinant g : F.Carrier))
    (hLh : ∀ h : GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
      Lh ≤ F.canonicalTopologicalData.ord (determinant h : F.Carrier))
    (B : Fin N → InverseWhittakerFunctions ψ r) (hB : ∀ i, Continuous (B i).val)
    (f : Fin N → GeneralLinear (r + 1) F.Carrier → ℂ) (hfc : ∀ i, Continuous (f i))
    (hsep : ∀ (j : ℤ) (s : ℂ) (g : GeneralLinear (r + 1) F.Carrier),
      (∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * W'.val (g * h)
        ∂generalLinearHaar F.Carrier r) =
      ∑ i, (B i).val g * ∫ h, adjacentRankInnerSliceWeight F Φ χ j s h * f i h
        ∂generalLinearHaar F.Carrier r) :
    ∀ (m : ℤ) (s : ℂ),
      AdjacentRankShellConvolutionAt F ψ W.val W' Φ φ χ ν Lq Lh B f m s := by
  classical
  let := hν.regular
  intro m s
  dsimp only [AdjacentRankShellConvolutionAt]
  let η := generalLinearHaar F.Carrier r
  let a := adjacentRankInnerMultiplier F (r := r) χ s
  let after := adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
  let before := adjacentRankBeforeShearKernel F ψ W.val W' Φ φ a m
  let outer := fun q => ∫ h, after (q, h) ∂η
  let I := Finset.Icc Lq (m - Lh)
  obtain ⟨hb, ha, -, ho, -, hba, -⟩ :=
    adjacentRankShell_shear_fubini F ψ σ hσ ℓ W W' hW' Φ φ a
      (continuous_adjacentRankInnerMultiplier F χ s) m ν hν
  have hslice (k : ℤ) (i : Fin N) :
      Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
        (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
          W.val (B i) φ 0)) ν :=
    integrable_equalRankSlice F ψ σ hσ ℓ W (B i) (hB i) φ k ν
  have hfi (j : ℤ) (i : Fin N) : Integrable (fun h =>
      adjacentRankInnerSliceWeight F Φ χ j s h * f i h) η :=
    integrable_adjacentRankInnerSliceWeight_mul F Φ χ j s (f i) (hfc i)
  have hsupport (q : LeftUnipotentQuotient r F.Carrier)
      (h : Langlands.GeneralLinear (r + 1) F.Carrier) (hz : after (q, h) ≠ 0) :
      determinantOrder F.canonicalTopologicalData r q ∈ I := by
    induction q using Quotient.inductionOn with
    | h g =>
      change adjacentRankJointShellKernel F ψ W.val W' Φ φ a m
        (Quotient.mk _ g, h) ≠ 0 at hz
      rw [adjacentRankJointShellKernel_mk] at hz
      split_ifs at hz with hs
      · have htest := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).2
        have hrow := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp hz).1).1).2
        have hfirst := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp
          (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hz).1).1).1).1
        have hq := hLq g hfirst hrow
        have hh := hLh h htest
        exact Finset.mem_Icc.mpr ⟨hq, by
          change F.canonicalTopologicalData.ord
            (GeneralLinear.determinant g : F.Carrier) ≤ m - Lh
          omega⟩
      · exact (hz rfl).elim
  have houterSupport (q : LeftUnipotentQuotient r F.Carrier) (hz : outer q ≠ 0) :
      determinantOrder F.canonicalTopologicalData r q ∈ I := by
    by_contra hn
    apply hz
    exact integral_eq_zero_of_ae (Filter.Eventually.of_forall fun h =>
      by_contra fun hh => hn (hsupport q h hh))
  have hpoint (k : ℤ) :
      (determinantSlice F.canonicalTopologicalData r k).indicator outer =
        fun q => ∑ i, (determinantSlice F.canonicalTopologicalData r k).indicator
          (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
            W.val (B i) φ 0) q *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η := by
    funext q
    by_cases hk : q ∈ determinantSlice F.canonicalTopologicalData r k
    · rw [Set.indicator_of_mem hk]
      induction q using Quotient.inductionOn with
      | h g =>
        have hg : F.canonicalTopologicalData.ord
            (GeneralLinear.determinant g : F.Carrier) = k := hk
        have heq (h : Langlands.GeneralLinear (r + 1) F.Carrier) :
            after (Quotient.mk _ g, h) =
              W.val.val g * φ (lastRow g) *
                (adjacentRankInnerSliceWeight F Φ χ (m - k) s h *
                  W'.val (g * h)) :=
          adjacentRankJointShellKernel_mk_eq_innerSlice F ψ W.val W' Φ φ χ m k s g h hg
        change (∫ h, after (Quotient.mk _ g, h) ∂η) = _
        rw [integral_congr_ae (Filter.Eventually.of_forall heq), integral_const_mul,
          hsep (m - k) s g, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Set.indicator_of_mem hk, equalRankIntegrand_zero_mk]
        change _ = W.val.val g * (B i).val g *
          φ (lastRow g) * _
        ring
    · simp only [Set.indicator_of_notMem hk, zero_mul, Finset.sum_const_zero]
  have hconv :
      (∫ z, after z ∂ν.prod η) = ∑ k ∈ I, ∑ i,
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val (B i) φ k *
          ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k) s h * f i h ∂η := by
    rw [integral_prod _ ha, integral_eq_sum_determinantSlices F ν outer ho I houterSupport]
    apply Finset.sum_congr rfl
    intro k _
    rw [hpoint k, integral_finsetSum Finset.univ (fun i _ => (hslice k i).mul_const _)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_mul_const]
    congr 1
    exact (sliceCoefficient_eq_integral_indicator F.canonicalTopologicalData ν
      (equalRankIntegrand ψ (normalizedAbsoluteValue F.canonicalTopologicalData)
        W.val (B i) φ 0) k).symm
  refine ⟨hb, ha, hslice, hfi, hconv, ?_⟩
  exact hba.trans ((integral_prod _ ha).symm.trans hconv)

/-- Recast the actual image of a specified inverse-character functional as
the image of its scaled-standard transport, retaining the same function. -/
def inverseCoefficientAsScaledStandard {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glInverseFunctionals ψ r σ)
    (W : (coefficientModel σ ℓ).toSubmodule) :
    (glCoefficientModel (ψ.scale (-1)) r σ
      (functionalsCongr (standardCharacter_scale_neg_one ψ r).symm ℓ)).toSubmodule :=
  ⟨InducedTailIntermediate.inverseAsScaledStandard ψ W.val, by
    obtain ⟨v, hv⟩ := W.property
    refine ⟨v, Subtype.ext ?_⟩
    exact congrArg (fun w : InverseWhittakerFunctions ψ r => w.val) hv⟩

/-- The actual pointwise lower support bounds used for a finite convolution. -/
def AdjacentRankShellLowerBounds {r : ℕ}
    (W : GeneralLinear (r + 1) F.Carrier → ℂ)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier)) (Lq Lh : ℤ) : Prop :=
  (∀ g, W g ≠ 0 → φ (lastRow g) ≠ 0 →
    Lq ≤ F.canonicalTopologicalData.ord (determinant g : F.Carrier)) ∧
  (∀ h : GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
    Lh ≤ F.canonicalTopologicalData.ord (determinant h : F.Carrier))

set_option maxHeartbeats 1600000 in
/-- Original and transformed outer convolutions use one actual finite model
family and exactly the same matrix coefficients, transformed by iota. -/
theorem adjacentRankShell_matchedFiniteConvolution {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (Φ ΦD : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φD : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ χD : Quasicharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    ∃ (Lq Lh LqD LhD : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      AdjacentRankShellLowerBounds F W.val.val Φ φ Lq Lh ∧
      AdjacentRankShellLowerBounds F WD.val.val ΦD φD LqD LhD ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          ∀ (m : ℤ) (s : ℂ),
            AdjacentRankShellConvolutionAt F ψ W.val
              (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
              Φ φ χ ν Lq Lh
              (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
              (fun i => (f i).val) m s ∧
            AdjacentRankShellConvolutionAt F (ψ.scale (-1)) WD.val
              (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val
              ΦD φD χD ν LqD LhD
              (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
              (fun i => GodementJacquet.coefficientIota (f i).val) m s := by
  dsimp only
  let σD := inverseTransposePullback σ
  let ℓD := functionalsCongr (standardCharacter_scale_neg_one ψ r).symm
    (dualFunctional ψ σ ℓ)
  let WD := inverseCoefficientAsScaledStandard F ψ σD
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  have hσD : IsSmooth σD :=
    isSmooth_comp (inverseTranspose (r + 1) F.Carrier).toMonoidHom
      (continuous_inverseTranspose (r + 1) F.Carrier) hσ
  obtain ⟨Lq, hLq⟩ := exists_whittakerRow_determinantOrder_lowerBound F ψ σ hσ ℓ W φ
  obtain ⟨Lh, hLh⟩ := exists_matrixTest_determinantOrder_lowerBound F Φ
  obtain ⟨LqD, hLqD⟩ := exists_whittakerRow_determinantOrder_lowerBound
    F (ψ.scale (-1)) σD hσD ℓD WD φD
  obtain ⟨LhD, hLhD⟩ := exists_matrixTest_determinantOrder_lowerBound F ΦD
  obtain ⟨N, B, hB⟩ := adjacentRankInnerSlice_matchedFiniteSeparation
    F (ψ.scale (-1)) τ hτ ℓ' Φ ΦD χ χD
  refine ⟨Lq, Lh, LqD, LhD, N, B, ⟨hLq, hLh⟩, ⟨hLqD, hLhD⟩, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  have hfc (i : Fin N) : Continuous (f i).val :=
    (GodementJacquet.isLocallyConstant_biSmoothMatrixCoefficients _ (f i)).continuous
  have hfo := adjacentRankShell_finiteConvolution_of_innerSeparation
    F ψ σ hσ ℓ W (InducedTailIntermediate.scaledStandardAsInverse ψ W'.val)
    (glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' W')
    Φ φ χ ν hν Lq Lh hLq hLh
    (fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val)
    (fun i => glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' (B i))
    (fun i => (f i).val) hfc (fun j s g => (hf j s g).2.2.2.1)
  have hdc (Z : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule) :
      Continuous (dualModelLinearMap (ψ.scale (-1)) τ ℓ' Z).val.val :=
    (glModelFunction_continuous (ψ.scale (-1)) r τ hτ.1 ℓ' Z).comp
      (continuous_const.mul (continuous_inverseTranspose (r + 1) F.Carrier))
  have hfd := adjacentRankShell_finiteConvolution_of_innerSeparation
    F (ψ.scale (-1)) σD hσD ℓD WD
    (dualModelLinearMap (ψ.scale (-1)) τ ℓ' W').val (hdc W')
    ΦD φD χD ν hν LqD LhD hLqD hLhD
    (fun i => (dualModelLinearMap (ψ.scale (-1)) τ ℓ' (B i)).val)
    (fun i => hdc (B i))
    (fun i => GodementJacquet.coefficientIota (f i).val)
    (fun i => (hfc i).comp (continuous_inverseTranspose (r + 1) F.Carrier))
    (fun j s g => (hf j s g).2.2.2.2)
  exact ⟨f, fun m s => ⟨hfo m s, hfd m s⟩⟩

end Langlands.RankinSelberg.Padic

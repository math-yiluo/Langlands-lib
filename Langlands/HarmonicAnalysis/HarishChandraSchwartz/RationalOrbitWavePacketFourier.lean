import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketPairing
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.FourierTransform

/-! # The Fourier transform of a wave packet (Proposition VII.2.1, `M = G`)

Waldspurger, proof of Proposition VII.2.1, case `M = G` (printed p. 318): the pairing
`(E^G_G ψ', f_ψ)_G` is `0` if `ω' ∉ O` and `(ψ', ψ_{ω'})` if `ω' ∈ O`; comparing with
Lemma VII.1.1 (ii), `(E^G_G ψ', f_ψ)_G = (ψ', f̂_ψ(ω'))`, gives
`f̂_ψ(ω') = ψ_{ω'}` if `ω' ∈ O` and `f̂_ψ(ω') = 0` otherwise.

This module proves this comparison. A generic theorem reads off `f̂` from the values of all the
pairings `∫_G conj(E ψ') f`, using that the form on `A ⊗ Ã` induced by a positive invariant form
is positive definite. For actual rational points, it is applied to a function `f ∈ C(G)` equal
to the wave packet `rationalOrbitWavePacket` of `RationalOrbitWavePacketPairing`, whose pairings
are computed there. The right side `rationalOrbitSectionExtension` is `ψ` extended by zero off
`O`. The constant `ν_A(A_G ∩ G¹)` coming from the Fourier inversion over `A_G` is kept explicit;
Waldspurger normalizes `mes(A_G ∩ K) = 1` instead (I.1).
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe u uV

/-- A positive definite form separates vectors: if `b(x, y) = b(x, z)` for every `x`, then
`y = z`. -/
theorem _root_.Langlands.InvariantPositiveForm.eq_of_forall_inner_eq {H : Type*} [Monoid H]
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ H V}
    (b : InvariantPositiveForm ρ) {y z : V} (h : ∀ x, b.inner x y = b.inner x z) : y = z := by
  let : InnerProductSpace.Core ℂ V := b.toInnerProductCore
  refine sub_eq_zero.mp (b.definite _ ?_)
  change b.inner (y - z) (y - z) = 0
  rw [InnerProductSpace.Core.inner_sub_right, h, sub_self]

section Generic

open Langlands.Plancherel

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [MeasurableMul G] [MeasurableInv G]
  [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] [μ.IsInvInvariant]
  {Ξ σ : G → ℝ}
  (A : SmoothRep.{0, u, uV} ℂ G) (hw : L2Weights μ Ξ σ) (hA : IsAdmissible A.representation)
  (hT : HasTemperedCoefficients Ξ σ A.representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)

/-- **Reading off `f̂` from the pairings** (the comparison with Lemma VII.1.1 (ii)): if
`∫_G conj(E ψ'(g)) f(g) dg = k (ψ', φ)_b` for every `ψ' ∈ A ⊗ Ã`, where `( , )_b` is the form
on `A ⊗ Ã` induced by a positive invariant form `b` on `A`, then `f̂ = d k φ` for the Fourier
transform `f̂ = d π(f̌)` with factor `d`. -/
theorem coefficientFourierTransform_eq_smul_of_forall_integral
    (b : InvariantPositiveForm A.representation) (d : ℝ) (f : Space Ξ σ) (k : ℂ)
    (φ : CoefficientTensor A)
    (h : ∀ ψ' : CoefficientTensor A, ∫ g, conj (coefficientTensorMap A ψ' g) * f g ∂μ =
      k * (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).inner ψ' φ) :
    coefficientFourierTransform A hw hA hT hΞ hσ d f = ((d : ℂ) * k) • φ := by
  have hT' : schwartzActionTensor A hw hA hT (Space.check hΞ hσ f) = k • φ := by
    refine (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA
      b).eq_of_forall_inner_eq fun ψ' => ?_
    rw [← integral_conj_coefficientTensorMap_mul A hw hA hT hΞ hσ b ψ' f, h ψ']
    let := (coefficientTensorInvariantForm A CompactOpenSubgroup.cofinal hA b).toInnerProductCore
    exact (InnerProductSpace.Core.inner_smul_right _ _).symm
  rw [coefficientFourierTransform_apply, hT', smul_smul]

end Generic

section Rational

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance instRationalOrbitWavePacketFourier1 :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance instRationalOrbitWavePacketFourier2 :
    NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance instRationalOrbitWavePacketFourier3 : T2Space F := BruhatTits.localField_t2Space F
local instance instRationalOrbitWavePacketFourier4 : T2Space (GroupScheme.rationalPoints G) :=
  rationalPoint_t2Space F G
local instance instRationalOrbitWavePacketFourier5 :
    LocallyCompactSpace (GroupScheme.rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance instRationalOrbitWavePacketFourier6 :
    SecondCountableTopology (GroupScheme.rationalPoints G) := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  exact (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
local instance instRationalOrbitWavePacketFourier7 :
    Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨BruhatTits.rationalPointCompactOpenSubgroup F G⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} [IsAffine T.X.left]
  (s : T.toGrp ⟶ G) (hs : GroupScheme.IsCentral s)
  [MeasurableSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]
  (mu : Measure (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range))
  (hindex : (RenardCartan.splitValuationImage s).FiniteIndex)
  [MeasurableSpace (GroupScheme.rationalPoints G)]
  [BorelSpace (GroupScheme.rationalPoints G)]
  [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
  [BorelSpace (GroupScheme.rationalPoints.map s).range]
  [MeasurableSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)]

/-- **The right side of Proposition VII.2.1 for `M = G`**: the section `ψ` over the orbit `O`
extended by zero, `ω' ↦ ψ_{ω'}` if `ω' ∈ O` and `ω' ↦ 0` otherwise. For `M = G` the sum over
`s ∈ W(G|G) = {1}` with `s⁻¹ω' ∈ O` has at most the term `ψ_{ω'}`, and `γ(G|G) c(G|G)² = 1`. -/
def rationalOrbitSectionExtension :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      (∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center mu
        (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj) →
      ∀ omega' : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu,
        CoefficientTensor (Quotient.out omega'.val).obj := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega ψ omega'
  classical
  exact if h : omega' ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega then
      ψ ⟨omega', h⟩ else 0

omit [IsAffine T.X.left] [MeasurableSpace (GroupScheme.rationalPoints G)]
  [BorelSpace (GroupScheme.rationalPoints G)]
  [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
  [BorelSpace (GroupScheme.rationalPoints.map s).range]
  [MeasurableSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)] in
theorem rationalOrbitSectionExtension_of_mem :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center
        mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj)
      (omega' : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (homega' : omega' ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega),
      rationalOrbitSectionExtension s hs mu omega ψ omega' = ψ ⟨omega', homega'⟩ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega ψ omega' homega'
  exact dite_eq_left homega'

omit [IsAffine T.X.left] [MeasurableSpace (GroupScheme.rationalPoints G)]
  [BorelSpace (GroupScheme.rationalPoints G)]
  [MeasurableSpace (GroupScheme.rationalPoints.map s).range]
  [BorelSpace (GroupScheme.rationalPoints.map s).range]
  [MeasurableSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (LeftQuotient (GroupScheme.rationalPoints.map s).range)]
  [BorelSpace (GroupScheme.rationalPoints G ⧸ (GroupScheme.rationalPoints.map s).range)] in
theorem rationalOrbitSectionExtension_of_notMem :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range hs.range_le_center
        mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj)
      (omega' : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
      omega' ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →
      rationalOrbitSectionExtension s hs mu omega ψ omega' = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ omega ψ omega' homega'
  exact dite_eq_right homega'

/-- **The Fourier transform of a wave packet off the orbit** (Proposition VII.2.1, `M = G`): if
`f ∈ C(G)` is the wave packet `f_ψ` of a section `ψ` over the orbit `O` and `ω' ∉ O`, then the
Fourier transform of `f` at the chosen representative of `ω'` vanishes, for every factor `d`. -/
theorem coefficientFourierTransform_rationalOrbitWavePacket_eq_zero
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ {Ξ σ : GroupScheme.rationalPoints G → ℝ} (hw : L2Weights μG Ξ σ)
        (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (f : Space Ξ σ),
        (⇑f = rationalOrbitWavePacket s hs mu hindex omega ψ) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu),
        omega' ∉ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega →
      ∀ (hT : HasTemperedCoefficients Ξ σ (Quotient.out omega'.val).obj.representation)
        (d : ℝ),
        coefficientFourierTransform (Quotient.out omega'.val).obj hw
          (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1 hT hΞ hσ
          d f = 0 := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ _ _ _ ν hν hνμ ψ hcont hintA Ξ σ hw hΞ hσ f hf omega'
    homega' hT d
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrable _ hs.range_le_center mu
    (out_representation_central _ hs.range_le_center mu omega') CompactOpenSubgroup.cofinal
    (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega')
    (Quotient.out omega'.val).property.1
  rw [coefficientFourierTransform_eq_smul_of_forall_integral _ hw _ hT hΞ hσ b d f 0 0
    fun ψ' => ?_, smul_zero]
  have hint := integrable_conj_coefficientTensorMap_mul _ hw
    (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1 hT ψ' f
  rw [hf] at hint
  rw [hf, zero_mul]
  exact integral_conj_mul_rationalOrbitWavePacket_eq_zero s hs mu hindex hG hAc omega μA μG ν hν
    hνμ ψ hcont hintA omega' homega' ψ' hint

/-- **The Fourier transform of a wave packet on the orbit** (Proposition VII.2.1, `M = G`): if
`f ∈ C(G)` is the wave packet `f_ψ` of a section `ψ` over the orbit `O` and `ω' ∈ O`, then
`f̂(ω') = ν_A(A_G ∩ G¹) ψ_{ω'}`, where `f̂(ω')` is the Fourier transform `d(ω') π(f̌)` at the
chosen representative of `ω'`. -/
theorem coefficientFourierTransform_rationalOrbitWavePacket_of_mem
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ {Ξ σ : GroupScheme.rationalPoints G → ℝ} (hw : L2Weights μG Ξ σ)
        (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (f : Space Ξ σ),
        (⇑f = rationalOrbitWavePacket s hs mu hindex omega ψ) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
        (homega' : omega' ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega)
        (hT : HasTemperedCoefficients Ξ σ (Quotient.out omega'.val).obj.representation),
        coefficientFourierTransform (Quotient.out omega'.val).obj hw
          (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1 hT hΞ hσ
          (discreteSeriesFormalDegree (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu CompactOpenSubgroup.cofinal omega') f =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) •
          ψ ⟨omega', homega'⟩ := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ _ _ _ ν hν hνμ ψ hcont hintA Ξ σ hw hΞ hσ f hf omega'
    homega' hT
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrable _ hs.range_le_center mu
    (out_representation_central _ hs.range_le_center mu omega') CompactOpenSubgroup.cofinal
    (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega')
    (Quotient.out omega'.val).property.1
  have hd : ((discreteSeriesFormalDegree (GroupScheme.rationalPoints.map s).range
      hs.range_le_center mu CompactOpenSubgroup.cofinal omega' : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (discreteSeriesFormalDegree_pos _ hs.range_le_center mu
      CompactOpenSubgroup.cofinal omega').ne'
  rw [coefficientFourierTransform_eq_smul_of_forall_integral _ hw _ hT hΞ hσ b _ f
    (((μA (Subtype.val ⁻¹'
      (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) *
      ((discreteSeriesFormalDegree (GroupScheme.rationalPoints.map s).range
        hs.range_le_center mu CompactOpenSubgroup.cofinal omega' : ℝ) : ℂ)⁻¹)
    (ψ ⟨omega', homega'⟩) fun ψ' => ?_]
  · rw [mul_left_comm, mul_inv_cancel₀ hd, mul_one]
  have hint := integrable_conj_coefficientTensorMap_mul _ hw
    (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1 hT ψ' f
  rw [hf] at hint
  rw [hf, integral_conj_mul_rationalOrbitWavePacket_of_mem s hs mu hindex hG hAc omega μA μG ν
    hν hνμ ψ hcont hintA omega' homega' b ψ' hint, mul_assoc]

/-- **Proposition VII.2.1 for `M = G`**: if `f ∈ C(G)` is the wave packet `f_ψ` of a section `ψ`
over the orbit `O`, then for every discrete series class `ω'`,
`f̂(ω') = ν_A(A_G ∩ G¹) ψ_{ω'}` if `ω' ∈ O` and `f̂(ω') = 0` otherwise, i.e. `f̂(ω')` is
`ν_A(A_G ∩ G¹)` times `rationalOrbitSectionExtension`. Here `f̂(ω')` is the Fourier transform
`d(ω') π(f̌)` at the chosen representative of `ω'`. -/
theorem coefficientFourierTransform_rationalOrbitWavePacket
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (μG : Measure (GroupScheme.rationalPoints G)) [IsFiniteMeasureOnCompacts μG]
      [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [μG.IsInvInvariant]
      (ν : Measure (LeftQuotient (GroupScheme.rationalPoints.map s).range)),
      IsCompatible (GroupScheme.rationalPoints.map s).range μG μA ν →
      ν.map (normalLeftQuotientHomeomorph (GroupScheme.rationalPoints.map s).range) = mu →
      ∀ (ψ : ∀ ω : discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
          hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega,
          CoefficientTensor (Quotient.out ω.val.val).obj),
      (∀ g, Continuous fun ω => coefficientTensorMap _ (ψ ω) g) →
      (∀ g, Integrable (fun a : (GroupScheme.rationalPoints.map s).range =>
        rationalOrbitWavePacket s hs mu hindex omega ψ ((a : GroupScheme.rationalPoints G) * g))
          μA) →
      ∀ {Ξ σ : GroupScheme.rationalPoints G → ℝ} (hw : L2Weights μG Ξ σ)
        (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (f : Space Ξ σ),
        (⇑f = rationalOrbitWavePacket s hs mu hindex omega ψ) →
      ∀ (omega' : DiscreteSeriesClass.{u, uV}
          (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
        (hT : HasTemperedCoefficients Ξ σ (Quotient.out omega'.val).obj.representation),
        coefficientFourierTransform (Quotient.out omega'.val).obj hw
          (isSquareIntegrableModCentralSubgroup_out _ hs.range_le_center mu omega').1 hT hΞ hσ
          (discreteSeriesFormalDegree (GroupScheme.rationalPoints.map s).range
            hs.range_le_center mu CompactOpenSubgroup.cofinal omega') f =
        ((μA (Subtype.val ⁻¹'
          (rationalCommonNormKernel G : Set (GroupScheme.rationalPoints G)))).toReal : ℂ) •
          rationalOrbitSectionExtension s hs mu omega ψ omega' := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ omega μA _ _ _ _ μG _ _ _ _ ν hν hνμ ψ hcont hintA Ξ σ hw hΞ hσ f hf omega' hT
  by_cases homega' : omega' ∈ discreteSeriesOrbit (GroupScheme.rationalPoints.map s).range
    hs.range_le_center mu (fun psi => (rationalNormCharacters G psi).toMul) omega
  · rw [rationalOrbitSectionExtension_of_mem s hs mu omega ψ omega' homega']
    exact coefficientFourierTransform_rationalOrbitWavePacket_of_mem s hs mu hindex hG hAc omega
      μA μG ν hν hνμ ψ hcont hintA hw hΞ hσ f hf omega' homega' hT
  · rw [rationalOrbitSectionExtension_of_notMem s hs mu omega ψ omega' homega', smul_zero]
    exact coefficientFourierTransform_rationalOrbitWavePacket_eq_zero s hs mu hindex hG hAc omega
      μA μG ν hν hνμ ψ hcont hintA hw hΞ hσ f hf omega' homega' hT _

end Rational

end Langlands.HarishChandraSchwartz

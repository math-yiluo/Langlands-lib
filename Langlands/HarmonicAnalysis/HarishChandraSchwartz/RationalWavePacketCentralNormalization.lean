import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalOrbitWavePacketFourier
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.CentralQuotientGeneration
import Mathlib.Algebra.Group.Subgroup.Pointwise
import Mathlib.Order.Minimal

/-! # The central mass in the `M = G` wave-packet calculation

For a closed central subgroup `A` of the rational points of a connected reductive group,
`A ∩ G¹ = A ∩ K` for every maximal compact subgroup `K`. Consequently Waldspurger's
I.1 normalization `mes(A ∩ K) = 1` removes the central mass in the published
`M = G` packet Fourier calculation, without changing its analytic hypotheses.
-/

noncomputable section

open MeasureTheory Langlands.QuotientIntegration
open scoped Pointwise

namespace Langlands.HarishChandraSchwartz

universe u uV

/-- A compact central subgroup lies in every maximal compact subgroup. This elementary
topological-group lemma does not require a maximal compact subgroup to be open. -/
theorem compactCentralSubgroup_le_maximalCompact {H : Type*} [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H]
    (C K : Subgroup H) (hC : IsCompact (C : Set H))
    (hCc : C ≤ Subgroup.center H)
    (hK : Maximal (fun L : Subgroup H => IsCompact (L : Set H)) K) : C ≤ K := by
  let : C.Normal := C.normal_of_le_center hCc
  have hsup : IsCompact ((K ⊔ C : Subgroup H) : Set H) := by
    rw [Subgroup.mul_normal]
    exact hK.prop.mul hC
  exact le_sup_right.trans (hK.2 hsup le_sup_left)

section Rational

open _root_.CategoryTheory _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X
local instance : NonarchimedeanGroup (GroupScheme.rationalPoints G) :=
  rationalPoints_nonarchimedeanGroup G
local instance : T2Space F := BruhatTits.localField_t2Space F
local instance : T2Space (GroupScheme.rationalPoints G) := rationalPoint_t2Space F G
local instance : LocallyCompactSpace (GroupScheme.rationalPoints G) :=
  rationalPoint_locallyCompactSpace F G
local instance : SecondCountableTopology (GroupScheme.rationalPoints G) := by
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  exact (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
local instance : Nonempty (CompactOpenSubgroup (GroupScheme.rationalPoints G)) :=
  ⟨BruhatTits.rationalPointCompactOpenSubgroup F G⟩

/-- The closed central part of `G¹` is exactly the intersection with a maximal compact
subgroup, including when the split rank is zero. -/
theorem rationalNormKernelPart_eq_inf_maximalCompact
    (hG : GroupScheme.IsConnectedReductive G)
    (A K : Subgroup (GroupScheme.rationalPoints G))
    (hAc : A ≤ Subgroup.center (GroupScheme.rationalPoints G))
    (hA : IsClosed (A : Set (GroupScheme.rationalPoints G)))
    (hK : Maximal (fun L : Subgroup (GroupScheme.rationalPoints G) =>
      IsCompact (L : Set (GroupScheme.rationalPoints G))) K) :
    rationalNormKernelPart G A = A ⊓ K := by
  apply le_antisymm
  · exact le_inf inf_le_left
      (compactCentralSubgroup_le_maximalCompact (rationalNormKernelPart G A) K
        (isCompact_rationalNormKernelPart G hG A hAc hA)
        (inf_le_left.trans hAc) hK)
  · exact inf_le_inf_left A (compactSubgroup_le_rationalCommonNormKernel G K hK.prop)

/-- The exact central-mass assertion needed by the published `M = G` packet formulas.
The measure is on `A`; the subset is the preimage of the actual rational norm kernel. -/
def RationalWavePacketCentralMassNormalizationStatement
    (A : Subgroup (GroupScheme.rationalPoints G)) [MeasurableSpace A]
    (μA : Measure A) : Prop :=
  μA (Subtype.val ⁻¹' (rationalCommonNormKernel G :
    Set (GroupScheme.rationalPoints G))) = 1

/-- I.1's `mes(A ∩ K) = 1` implies the central-mass assertion for a closed central
subgroup and a maximal compact subgroup. No Haar existence or special-vertex
existence assertion is included in this elementary adapter. -/
theorem rationalWavePacketCentralMassNormalization
    (hG : GroupScheme.IsConnectedReductive G)
    (A K : Subgroup (GroupScheme.rationalPoints G))
    (hAc : A ≤ Subgroup.center (GroupScheme.rationalPoints G))
    (hA : IsClosed (A : Set (GroupScheme.rationalPoints G)))
    (hK : Maximal (fun L : Subgroup (GroupScheme.rationalPoints G) =>
      IsCompact (L : Set (GroupScheme.rationalPoints G))) K)
    [MeasurableSpace A] (μA : Measure A)
    (hμA : μA (Subtype.val ⁻¹' (K : Set (GroupScheme.rationalPoints G))) = 1) :
    RationalWavePacketCentralMassNormalizationStatement A μA := by
  have hsets : (Subtype.val ⁻¹' (rationalCommonNormKernel G :
      Set (GroupScheme.rationalPoints G)) : Set A) =
      Subtype.val ⁻¹' (K : Set (GroupScheme.rationalPoints G)) := by
    ext a
    change ((a : GroupScheme.rationalPoints G) ∈ rationalCommonNormKernel G) ↔
      ((a : GroupScheme.rationalPoints G) ∈ K)
    have heq := rationalNormKernelPart_eq_inf_maximalCompact hG A K hAc hA hK
    have hmem := congrArg (fun L : Subgroup (GroupScheme.rationalPoints G) =>
      (a : GroupScheme.rationalPoints G) ∈ L) heq
    simpa only [rationalNormKernelPart, Subgroup.mem_inf, a.property, true_and] using
      (Iff.of_eq hmem)
  change μA _ = 1
  rw [hsets, hμA]

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

/-- Exact conditional source-normalized `M = G` Fourier target. The maximal compact
subgroup and I.1 central mass convention are explicit alongside every hypothesis of
`coefficientFourierTransform_rationalOrbitWavePacket`. -/
def RationalSourceNormalizedOrbitPacketFourierStatement
    (_hG : GroupScheme.IsConnectedReductive G)
    (_hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) : Prop :=
    letI := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
    ∀ [Measure.IsHaarMeasure mu] [mu.IsInvInvariant]
      (K : Subgroup (GroupScheme.rationalPoints G))
      (_hK : Maximal (fun L : Subgroup (GroupScheme.rationalPoints G) =>
        IsCompact (L : Set (GroupScheme.rationalPoints G))) K)
      (omega : DiscreteSeriesClass.{u, uV}
        (GroupScheme.rationalPoints.map s).range hs.range_le_center mu)
      (μA : Measure (GroupScheme.rationalPoints.map s).range) [SFinite μA]
      [μA.IsMulLeftInvariant] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
      (_hμA : μA (Subtype.val ⁻¹' (K : Set (GroupScheme.rationalPoints G))) = 1)
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
        rationalOrbitSectionExtension s hs mu omega ψ omega'

/-- The source-normalized `M = G` formula follows from the published packet Fourier
calculation and the central-mass adapter. All hypotheses of that calculation remain
in the statement; in particular, packet Schwartz membership is still conditional. -/
theorem rationalSourceNormalizedOrbitPacketFourier
    (hG : GroupScheme.IsConnectedReductive G)
    (hAc : IsClosed ((GroupScheme.rationalPoints.map s).range :
      Set (GroupScheme.rationalPoints G))) :
    RationalSourceNormalizedOrbitPacketFourierStatement s hs mu hindex hG hAc := by
  let := (GroupScheme.rationalPoints.map s).range.normal_of_le_center hs.range_le_center
  intro _ _ K hK omega μA _ _ _ _ hμA μG _ _ _ _ ν hν hνμ ψ hcont hintA Ξ σ hw hΞ hσ f hf
    omega' hT
  have hmass := rationalWavePacketCentralMassNormalization hG
    (GroupScheme.rationalPoints.map s).range K hs.range_le_center hAc hK μA hμA
  change μA (Subtype.val ⁻¹' (rationalCommonNormKernel G :
    Set (GroupScheme.rationalPoints G))) = 1 at hmass
  have hcalc := coefficientFourierTransform_rationalOrbitWavePacket s hs mu hindex hG hAc
    omega μA μG ν hν hνμ ψ hcont hintA hw hΞ hσ f hf omega' hT
  simpa only [hmass, ENNReal.toReal_one, Complex.ofReal_one, one_smul] using hcalc

end Rational

end Langlands.HarishChandraSchwartz

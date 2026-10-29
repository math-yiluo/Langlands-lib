import Langlands.Representation.Whittaker.BruhatHaarMeasureStatement
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Group.GL.PadicUpperUnipotent
import Langlands.Representation.RankinSelberg.UnipotentUnimodularity
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Haar measures on actual p-adic unipotent and Bruhat fiber groups

In a second countable locally compact group every Haar measure is unique up to a
positive scalar. A compact open subgroup containing a translation element forces
that scalar to be one, and an involutive anti-automorphism forces the scalar of
the transported measure to square to one.
-/

noncomputable section

namespace Langlands.Whittaker

open Langlands.GeneralLinear MeasureTheory MeasureTheory.Measure Topology TopologicalSpace
open scoped ENNReal NNReal

universe uF uG

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

/-- If every element lies in a compact open subgroup, every Haar measure on a second
countable locally compact group is right invariant. -/
theorem isMulRightInvariant_of_compactOpenCover
    (hcover : ∀ g : G, ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ g ∈ K)
    (μ : Measure G) [IsHaarMeasure μ] : IsMulRightInvariant μ := by
  refine ⟨fun g => ?_⟩
  obtain ⟨K, hK, hg⟩ := hcover g
  have hscale := isMulLeftInvariant_eq_smul (Measure.map (fun x => x * g) μ) μ
  have hpre : (fun x : G => x * g) ⁻¹' (K : Set G) = K := by
    ext x
    exact K.toSubgroup.mul_mem_cancel_right hg
  have hm := congrArg (fun ν : Measure G => ν (K : Set G)) hscale
  rw [Measure.map_apply (measurable_mul_const g) K.isOpen.measurableSet, hpre,
    Measure.smul_apply] at hm
  have hzero : μ (K : Set G) ≠ 0 := K.isOpen.measure_ne_zero μ ⟨1, K.one_mem⟩
  have htop : μ (K : Set G) ≠ ⊤ := hK.measure_ne_top
  have he : (haarScalarFactor (Measure.map (fun x => x * g) μ) μ : ℝ≥0∞) = 1 :=
    (ENNReal.mul_eq_right hzero htop).mp hm.symm
  rw [ENNReal.coe_eq_one.mp he, one_smul] at hscale
  exact hscale

/-- An involutive homeomorphism reversing multiplication preserves every right
invariant Haar measure on a second countable locally compact group. -/
theorem map_eq_self_of_antiInvolution (τ : G ≃ₜ G)
    (hmul : ∀ x y, τ (x * y) = τ y * τ x) (hinv : ∀ x, τ (τ x) = x)
    (μ : Measure G) [IsHaarMeasure μ] [IsMulRightInvariant μ] :
    Measure.map τ μ = μ := by
  have hτ : Measurable τ := τ.continuous.measurable
  have hleft : IsMulLeftInvariant (Measure.map τ μ) := by
    refine ⟨fun g => ?_⟩
    rw [Measure.map_map (measurable_const_mul g) hτ]
    have hfun : (fun x => g * x) ∘ τ = τ ∘ (fun x => x * τ g) := by
      funext x
      simp only [Function.comp_apply, hmul, hinv]
    rw [hfun, ← Measure.map_map hτ (measurable_mul_const (τ g)), map_mul_right_eq_self]
  have hfin : IsFiniteMeasureOnCompacts (Measure.map τ μ) :=
    IsFiniteMeasureOnCompacts.map μ τ
  have hpos : IsOpenPosMeasure (Measure.map τ μ) :=
    τ.continuous.isOpenPosMeasure_map τ.surjective
  let c : ℝ≥0∞ := haarScalarFactor (Measure.map τ μ) μ
  have hc : Measure.map τ μ = c • μ := isMulLeftInvariant_eq_smul (Measure.map τ μ) μ
  have htwice : Measure.map τ (Measure.map τ μ) = μ := by
    rw [Measure.map_map hτ hτ]
    have hid : (τ ∘ τ : G → G) = id := funext hinv
    rw [hid, Measure.map_id]
  have hμ : μ = c ^ 2 • μ := by
    calc μ = Measure.map τ (Measure.map τ μ) := htwice.symm
      _ = Measure.map τ (c • μ) := by rw [hc]
      _ = c • Measure.map τ μ := Measure.map_smul c hτ.aemeasurable
      _ = c • (c • μ) := by rw [hc]
      _ = c ^ 2 • μ := by rw [smul_smul, pow_two]
  have K : PositiveCompacts G := Classical.arbitrary _
  have hK : c ^ 2 * μ K = 1 ^ 2 * μ K := by
    conv_rhs => rw [hμ]
    simp
  have hc2 : c ^ 2 = 1 ^ 2 :=
    (ENNReal.mul_left_inj (measure_pos_of_nonempty_interior _ K.interior_nonempty).ne'
      K.isCompact.measure_lt_top.ne).1 hK
  have hc1 : c = 1 := (ENNReal.pow_right_strictMono two_ne_zero).injective hc2
  rw [hc, hc1, one_smul]

end Generic

/-- A closed subgroup contained in a subgroup covered by compact open subgroups is
itself covered by compact open subgroups. -/
theorem compactOpenCover_of_le {G : Type uG} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {H H' : Subgroup G} (hle : H ≤ H')
    (hH : IsClosed (H : Set G))
    (hcover : ∀ g : H', ∃ K : OpenSubgroup H', IsCompact (K : Set H') ∧ g ∈ K)
    (h : H) : ∃ L : OpenSubgroup H, IsCompact (L : Set H) ∧ h ∈ L := by
  obtain ⟨K, hK, hh⟩ := hcover (Subgroup.inclusion hle h)
  have hcont : Continuous (Subgroup.inclusion hle) :=
    continuous_subtype_val.subtype_mk fun x => hle x.property
  have hemb : IsClosedEmbedding (Subgroup.inclusion hle) :=
    IsClosedEmbedding.of_comp (g := (Subtype.val : H' → G)) IsEmbedding.subtypeVal
      hH.isClosedEmbedding_subtypeVal
  exact ⟨OpenSubgroup.comap (Subgroup.inclusion hle) hcont K,
    hemb.isCompact_preimage hK, hh⟩

/-- **Haar measures on the actual p-adic unipotent and Bruhat fiber groups.** -/
theorem bruhatHaarMeasure : BruhatHaarMeasureStatement.{uF} := by
  intro p hp F n U
  let := F.canonicalNormedField
  let := F.canonicalTopologicalData.valuativeRel
  let : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
  let : MeasurableSpace U := borel U
  have : BorelSpace U := ⟨rfl⟩
  have : LocallyCompactSpace (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearLocallyCompactSpace (n + 1)
  have : SecondCountableTopology (GeneralLinear (n + 1) F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSecondCountableTopology (n + 1)
  have hUclosed : IsClosed (U : Set (GeneralLinear (n + 1) F.Carrier)) :=
    UpperUnipotent.isClosed (R := F.Carrier) (n := n + 1)
  have : LocallyCompactSpace U := hUclosed.locallyCompactSpace
  have : SecondCountableTopology U := IsEmbedding.subtypeVal.secondCountableTopology
  have hUcover : ∀ g : U, ∃ K : OpenSubgroup U, IsCompact (K : Set U) ∧ g ∈ K :=
    RankinSelberg.unipotent_exists_compact_open F.Carrier n
  have hUinv (μ : Measure U) [IsHaarMeasure μ] : IsMulRightInvariant μ :=
    isMulRightInvariant_of_compactOpenCover hUcover μ
  refine ⟨⟨haar, inferInstance⟩, fun μ _ => ⟨inferInstance, hUinv μ, ?_⟩, fun w => ?_⟩
  · have := hUinv μ
    exact map_eq_self_of_antiInvolution (weylTransposeUnipotent n F.Carrier)
      (fun x y => Subtype.ext (weylTransposeHomeomorph_mul n F.Carrier x.val y.val))
      (weylTransposeUnipotent_involutive n F.Carrier) μ
  · intro P
    let : MeasurableSpace P := borel P
    have : BorelSpace P := ⟨rfl⟩
    have hPclosed : IsClosed (P : Set (GeneralLinear (n + 1) F.Carrier)) :=
      isClosed_permutationUnipotentPlus (n + 1) F.Carrier w
    have : LocallyCompactSpace P := hPclosed.locallyCompactSpace
    have : SecondCountableTopology P := IsEmbedding.subtypeVal.secondCountableTopology
    have hPcover : ∀ h : P, ∃ L : OpenSubgroup P, IsCompact (L : Set P) ∧ h ∈ L :=
      compactOpenCover_of_le (permutationUnipotentPlus_le_upperUnipotent (n + 1) F.Carrier w)
        hPclosed hUcover
    exact ⟨⟨haar, inferInstance⟩, fun ν _ =>
      ⟨inferInstance, isMulRightInvariant_of_compactOpenCover hPcover ν⟩⟩

end Langlands.Whittaker

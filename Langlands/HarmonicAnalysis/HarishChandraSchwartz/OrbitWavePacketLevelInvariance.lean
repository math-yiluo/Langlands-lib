import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology

/-! # Wave packets preserve the fixed input level -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "includeLevel" => OrbitSectionLevel.toSections ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "coefficient" => unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ
  ν π hν hr C hC μ hsq e

/-- Every coefficient of a section at level `H` is bi-invariant under this same `H`. -/
theorem unitaryOrbitCoefficientMap_biInvariant_of_level (H : OpenSubgroup G)
    (q : SectionLevel H)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    IsBiInvariant H (coefficient (includeLevel H q) ω) := by
  intro k hk l hl g
  obtain ⟨A, rfl⟩ :=
    unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitCoefficientMap_representative]
  change unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A
      (q.val A) (k * g * l) =
    unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A) g
  let x : H.prod H := ⟨(l, k⁻¹), hl, H.inv_mem hk⟩
  have hfix : (productInducedCoefficientObject h hU A.val.obj).representation x (q.val A) =
      q.val A := congrFun (q.property.2 x) A
  have ht := CompactInduction.coefficientMap_action h hU A.val.obj K hK hP hr
    (fun g => by
      obtain ⟨p, k, hg⟩ := hPK g
      exact ⟨p, p.property, k, k.property, hg⟩)
    hG hδ A.val.property.2 x (q.val A) g
  have hc := congrArg (fun F => unitaryOrbitRepresentativeCoefficientMap
    h hU hP K hK hPK hG hδ ν π hr A F g) hfix
  simpa only [x, inv_inv, unitaryOrbitRepresentativeCoefficientMap] using ht.symm.trans hc

variable [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)

set_option hygiene false in
local notation "packet" => inducedOrbitWavePacket h hU hP K hK hPK hG hδ
  ν π hν hr e C hC μ hsq ρ w

/-- Integration preserves the same fixed subgroup, for every weight and character measure. -/
theorem inducedOrbitWavePacket_biInvariant_of_level (H : OpenSubgroup G) (q : SectionLevel H) :
    IsBiInvariant H (packet (includeLevel H q)) := by
  intro k hk l hl g
  unfold inducedOrbitWavePacket
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    congrArg (fun z : ℂ => w ω * z)
      (unitaryOrbitCoefficientMap_biInvariant_of_level h hU hP K hK hPK hG hδ
        ν π hν hr e C hC μ hsq H q ω k hk l hl g))

/-- The original wave packet restricted to one input level, with its same-level invariance. -/
def inducedOrbitWavePacketLevel (H : OpenSubgroup G) :
    SectionLevel H → {f : G → ℂ // IsBiInvariant H f} :=
  fun q => ⟨packet (includeLevel H q),
    inducedOrbitWavePacket_biInvariant_of_level h hU hP K hK hPK hG hδ
      ν π hν hr e C hC μ hsq ρ w H q⟩

/-- The fixed-level construction retains the literal integral at every group point. -/
@[simp] theorem inducedOrbitWavePacketLevel_apply (H : OpenSubgroup G)
    (q : SectionLevel H) (g : G) :
    (inducedOrbitWavePacketLevel h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w H q).val g =
      packet (includeLevel H q) g :=
  rfl

end Langlands.HarishChandraSchwartz

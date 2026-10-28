import Langlands.HarmonicAnalysis.Distribution.CharacterAverage
import Langlands.Group.GL.CompactOpen
import Langlands.Group.GL.CountabilityProof

/-!
# Surjectivity of character-weighted product averaging

The proposition `SchwartzBruhat.CharacterAverageSurjectiveStatement` asserts that the
published map `SchwartzBruhat.characterAverage χ μ`, sending a test function `α` on
`G × (Y × G)` to
`y ↦ ∫ z, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ)`,
is surjective onto `SchwartzBruhat Y` for every Hausdorff, locally compact,
nonarchimedean topological group `G` with its Borel structure, every topological
space `Y`, every continuous character `χ` and every s-finite Haar measure `μ`.
This is an internal generalization of the surjectivity assertion of Shalika (1974),
Proposition 1.12. Nothing is proved about it here. The module also proves that the
statement applies to the published upper-unipotent specialization, for every Haar
measure. See the paired Markdown.
-/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

universe uG uY uF

/-- For all types `G : Type uG` and `Y : Type uY`, where `G` is a Hausdorff, locally
compact, nonarchimedean topological group with its Borel σ-algebra and `Y` is any
topological space, every continuous character `χ : G → ℂˣ` and every s-finite Haar
measure `μ` on `G`, the published complex-linear map
`characterAverage χ μ : SchwartzBruhat (G × (Y × G)) →ₗ[ℂ] SchwartzBruhat Y`,
`α ↦ (y ↦ ∫ z, α (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹ ∂(μ.prod μ))`,
is surjective. -/
def CharacterAverageSurjectiveStatement : Prop :=
  ∀ (G : Type uG) (Y : Type uY) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
    [MeasurableSpace G] [BorelSpace G] [TopologicalSpace Y]
    (χ : ContinuousMonoidHom G ℂˣ) (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ],
      Function.Surjective (characterAverage (Y := Y) χ μ)

section UpperUnipotent

open Langlands.GeneralLinear Langlands.Whittaker

/-- Every Haar measure on the actual upper unipotent subgroup of `GL_n` over a canonical
p-adic field, with its Borel σ-algebra, is s-finite: the group is second countable and
locally compact, hence σ-compact, and a Haar measure is finite on compact sets. -/
theorem upperUnipotent_sFinite_of_isHaarMeasure {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (upperUnipotent n F.Carrier)
    ∀ (μ : Measure (upperUnipotent n F.Carrier)) [μ.IsHaarMeasure], SFinite μ := by
  let := F.canonicalTopologicalData.topology
  let := borel (upperUnipotent n F.Carrier)
  intro μ _
  have : SecondCountableTopology (Langlands.GeneralLinear n F.Carrier) :=
    F.canonicalTopologicalData.generalLinearSecondCountableTopology n
  have : SecondCountableTopology (upperUnipotent n F.Carrier) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  have : LocallyCompactSpace (upperUnipotent n F.Carrier) :=
    F.canonicalUpperUnipotentLocallyCompactSpace n
  infer_instance

/-- The statement applies to the published upper-unipotent average
`standardCharacterAverage F n ψ μ` on `GL_{n+1}` over every canonical p-adic field
`F : PadicField.{uF} p`, for every `n` including `0`, every unitary additive character
`ψ` and every Haar measure `μ`; the s-finiteness required by the average is supplied by
`upperUnipotent_sFinite_of_isHaarMeasure` rather than assumed. -/
theorem CharacterAverageSurjectiveStatement.surjective_standardCharacterAverage
    (h : CharacterAverageSurjectiveStatement.{uF, uF}) {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : Measure (upperUnipotent (n + 1) F.Carrier))
      [μ.IsHaarMeasure],
      haveI := upperUnipotent_sFinite_of_isHaarMeasure F (n + 1) μ
      Function.Surjective (standardCharacterAverage F n ψ μ) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  have := F.canonicalUpperUnipotentTopologicalGroup (n + 1)
  have := F.canonicalUpperUnipotentT2Space (n + 1)
  have := F.canonicalUpperUnipotentLocallyCompactSpace (n + 1)
  have := F.canonicalUpperUnipotentNonarchimedean (n + 1)
  intro ψ μ _
  have := upperUnipotent_sFinite_of_isHaarMeasure F (n + 1) μ
  exact h (upperUnipotent (n + 1) F.Carrier) (Fin (n + 1) → F.Carrierˣ)
    (standardCharacterContinuous ψ n) μ

end UpperUnipotent

end Langlands.HarmonicAnalysis.SchwartzBruhat

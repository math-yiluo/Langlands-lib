import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Topology.LocallyProfinite

/-! # Integration in a product chart for regular orbits -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis MeasureTheory Set _root_.Topology

universe uX uB uQ

/-- In a product chart over an open parameter set, each slice of a test function is
integrable for a fixed measure finite on compact sets, and the integrals are locally
constant in the parameter. -/
abbrev RegularOrbitalChartIntegrationStatement : Prop :=
  ∀ {X : Type uX} {B : Type uB} {Q : Type uQ}
    [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Q]
    [T2Space B] [T2Space Q] [MeasurableSpace Q] [OpensMeasurableSpace Q]
    (p : X → B) (_ : Continuous p) (_ : Langlands.Topology.HasCompactOpenNeighborhoodBasis B)
    {V : Set B} (_ : IsOpen V) (e : V × Q ≃ₜ (p ⁻¹' V : Set X))
    (_ : ∀ (b : V) (q : Q), p (e (b, q)).val = b.val)
    (ν : Measure Q) [IsFiniteMeasureOnCompacts ν] (f : SchwartzBruhat X),
    (∀ b : V, Integrable (fun q : Q => f (e (b, q)).val) ν) ∧
      IsLocallyConstant (fun b : V => ∫ q : Q, f (e (b, q)).val ∂ν)

variable {X : Type uX} {B : Type uB} {Q : Type uQ}
  [TopologicalSpace X] [TopologicalSpace B] [TopologicalSpace Q]

/-- A chart over a saturated parameter patch is a closed embedding when restricted to
a closed subset of that patch. -/
private theorem isClosedEmbedding_chartPatch (p : X → B) (hp : Continuous p)
    {C V : Set B} (hC : IsClosed C) (hCV : C ⊆ V)
    (e : V × Q ≃ₜ (p ⁻¹' V : Set X))
    (he : ∀ (b : V) (q : Q), p (e (b, q)).val = b.val) :
    IsClosedEmbedding (fun z : C × Q => (e (inclusion hCV z.1, z.2)).val) := by
  let F : C × Q → X := fun z => (e (inclusion hCV z.1, z.2)).val
  have hF : IsEmbedding F := IsEmbedding.subtypeVal.comp
    (e.isEmbedding.comp ((IsEmbedding.inclusion hCV).prodMap IsEmbedding.id))
  have hrange : range F = p ⁻¹' C := by
    ext x
    constructor
    · rintro ⟨⟨b, q⟩, rfl⟩
      change p (e (inclusion hCV b, q)).val ∈ C
      rw [he]
      exact b.property
    · intro hx
      let z := e.symm ⟨x, hCV hx⟩
      have hz : e z = ⟨x, hCV hx⟩ := e.apply_symm_apply _
      have hb : z.1.val = p x := by
        rw [← he z.1 z.2, Prod.mk.eta, hz]
      refine ⟨(⟨z.1.val, hb ▸ hx⟩, z.2), ?_⟩
      change (e (inclusion hCV ⟨z.1.val, _⟩, z.2)).val = x
      have hpair : (inclusion hCV ⟨z.1.val, hb ▸ hx⟩, z.2) = z :=
        Prod.ext (Subtype.ext rfl) rfl
      rw [hpair, hz]
  exact ⟨hF, hrange ▸ hC.preimage hp⟩

/-- Product-chart integration via compact open parameter neighborhoods. -/
theorem integrable_locallyConstant_orbitChart :
    RegularOrbitalChartIntegrationStatement.{uX, uB, uQ} := by
  intro X B Q _ _ _ _ _ _ _ p hp hB V hV e he ν _ f
  have hlocal (b : V) :
      Integrable (fun q : Q => f (e (b, q)).val) ν ∧
        ∃ U : Set V, IsOpen U ∧ b ∈ U ∧
          ∀ b' ∈ U, (∫ q : Q, f (e (b', q)).val ∂ν) = ∫ q : Q, f (e (b, q)).val ∂ν := by
    obtain ⟨C, hbC, hCo, hCc, hCV⟩ := hB b.val V (hV.mem_nhds b.property)
    let F : C × Q → X := fun z => (e (inclusion hCV z.1, z.2)).val
    have hF : IsClosedEmbedding F := isClosedEmbedding_chartPatch p hp hCc.isClosed hCV e he
    let g : SchwartzBruhat (C × Q) :=
      ⟨(f : X → ℂ) ∘ F, f.locallyConstant.comp_continuous hF.continuous,
        f.hasCompactSupport.comp_isClosedEmbedding hF⟩
    refine ⟨(g.sliceSnd ⟨b.val, hbC⟩).integrable ν, ?_⟩
    obtain ⟨W, hWo, hbW, hW⟩ :=
      (g.partialIntegral ν).locallyConstant.exists_open (⟨b.val, hbC⟩ : C)
    have hinc : IsOpenEmbedding (inclusion hCV) :=
      IsOpenEmbedding.inclusion hCV (hCo.preimage continuous_subtype_val)
    refine ⟨inclusion hCV '' W, hinc.isOpenMap W hWo, ⟨⟨b.val, hbC⟩, hbW, rfl⟩, ?_⟩
    rintro b' ⟨c, hc, rfl⟩
    exact hW c hc
  exact ⟨fun b => (hlocal b).1, IsLocallyConstant.iff_exists_open _ |>.2 fun b => (hlocal b).2⟩

end Langlands.BaseChange

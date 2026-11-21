import Langlands.BaseChange.RegularOrbitalChartIntegration
import Langlands.BaseChange.RegularOrbitalNormalization
import Langlands.BaseChange.TwistedOrbitalConjugation

/-! Normalized orbital profiles from product charts with fixed section centralizer. -/

noncomputable section

namespace Langlands.BaseChange

open Set MeasureTheory _root_.Topology
open Langlands.HarmonicAnalysis Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (HasCompactOpenNeighborhoodBasis)
open scoped NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {B : Type v} [TopologicalSpace B]
variable {R : Set G}

/-- A chart over an open patch of parameters with a fixed centralizer on its section. -/
structure RegularOrbitalChart (θ : G →* G) (p : R → B) where
  parameters : Set B
  isOpen : IsOpen parameters
  centralizer : Subgroup G
  representative : parameters → R
  chart : parameters × LeftQuotient centralizer ≃ₜ (p ⁻¹' parameters : Set R)
  stabilizer (b : parameters) : twistedCentralizer θ (representative b : G) = centralizer
  parameter (z : parameters × LeftQuotient centralizer) : p (chart z).val = z.1.val
  apply_mk (b : parameters) (g : G) :
    (chart (b, leftQuotientMap centralizer g)).val.val = twistedConj θ g (representative b : G)

variable {θ : G →* G} {p : R → B}

omit [IsTopologicalGroup G] in
private theorem isOpenMap_of_orbitalCharts
    (hcharts : ∀ r : R, ∃ c : RegularOrbitalChart θ p, p r ∈ c.parameters) :
    IsOpenMap p := by
  intro U hU
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨r, hr, rfl⟩
  obtain ⟨c, hcr⟩ := hcharts r
  let W := Prod.fst '' (c.chart ⁻¹' (Subtype.val ⁻¹' U))
  have hW : IsOpen W :=
    isOpenMap_fst _ ((hU.preimage continuous_subtype_val).preimage c.chart.continuous)
  let z := c.chart.symm ⟨r, hcr⟩
  have hz : c.chart z = ⟨r, hcr⟩ := c.chart.apply_symm_apply _
  have hrW : p r ∈ Subtype.val '' W := by
    refine ⟨z.1, ⟨z, ?_, rfl⟩, ?_⟩
    · change (c.chart z).val ∈ U
      rwa [hz]
    · rw [← c.parameter z, hz]
  refine Filter.mem_of_superset ((c.isOpen.isOpenMap_subtype_val _ hW).mem_nhds hrW) ?_
  rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
  exact ⟨(c.chart w).val, hw, c.parameter w⟩

variable [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
variable [MeasurableSpace G] [BorelSpace G]
variable {μ : Measure G} {m : RegularOrbitalMeasures θ μ R}

namespace RegularOrbitalMeasures.IsNormalized

/-- Normalized quotient measures give the same orbital integrals under twisted conjugation. -/
theorem orbitalConj [μ.IsMulLeftInvariant] (hm : m.IsNormalized) (hθ : Continuous θ)
    (r : R) (g : G) (hg : twistedConj θ g (r : G) ∈ R) (f : G → ℂ) :
    let s : R := ⟨twistedConj θ g (r : G), hg⟩
    (Integrable (twistedOrbitFunction θ (s : G) f) (m.quotient s) ↔
      Integrable (twistedOrbitFunction θ (r : G) f) (m.quotient r)) ∧
    twistedOrbitalIntegral θ (s : G) (m.quotient s) f =
      twistedOrbitalIntegral θ (r : G) (m.quotient r) f := by
  let s : R := ⟨twistedConj θ g (r : G), hg⟩
  change (Integrable (twistedOrbitFunction θ (s : G) f) (m.quotient s) ↔ _) ∧
    twistedOrbitalIntegral θ (s : G) (m.quotient s) f = _
  obtain ⟨kr, hkr⟩ := hm r
  obtain ⟨ks, hks⟩ := hm s
  have hc := isClosed_twistedCentralizer θ hθ (s : G)
  let : LocallyCompactSpace (twistedCentralizer θ (s : G)) := hc.locallyCompactSpace
  let : SecondCountableTopology (twistedCentralizer θ (s : G)) :=
    IsEmbedding.subtypeVal.secondCountableTopology
  let : (m.centralizer r).IsMulRightInvariant := m.rightInvariant r
  let : (m.centralizer s).IsMulRightInvariant := m.rightInvariant s
  let : (m.centralizer s).IsHaarMeasure := m.haar s
  let : (m.centralizer s).Regular := hks.symm ▸ inferInstanceAs (ks.haar.Regular)
  have hmap : m.centralizer s =
      Measure.map (twistedCentralizerConj θ (r : G) g) (m.centralizer r) := by
    rw [hkr, hks]
    exact (kr.map_haar ks _).symm
  have hcomp := isCompatible_map_twistedConj θ (r : G) g
    (m.centralizer r) (m.centralizer s) μ hmap (m.quotient r) (m.compatible r)
  have hν : m.quotient s = Measure.map (twistedOrbitQuotientConj θ (r : G) g) (m.quotient r) := by
    simpa only [one_smul] using (m.compatible s).eq_smul_of_subgroup_smul hc hcomp
      (c := 1) (one_smul ℝ≥0 _).symm
  rw [hν]
  exact twistedOrbitalIntegral_map_conj θ (r : G) g (m.quotient r) f

end RegularOrbitalMeasures.IsNormalized

omit [SecondCountableTopology G] in
private theorem slice_eq_orbitalIntegral (hm : m.IsNormalized) (hθ : Continuous θ)
    {r : R} {H : Subgroup G} (hH : twistedCentralizer θ (r : G) = H)
    (k : HasLargestCompactOpenSubgroup H) [k.haar.IsMulRightInvariant]
    (ν : Measure (LeftQuotient H)) (hν : IsCompatible H μ k.haar ν)
    (f : G → ℂ) (slice : LeftQuotient H → ℂ)
    (hs : ∀ g : G, slice (leftQuotientMap H g) = f (twistedConj θ g r)) :
    (Integrable slice ν ↔ Integrable (twistedOrbitFunction θ (r : G) f) (m.quotient r)) ∧
    (∫ q, slice q ∂ν) = twistedOrbitalIntegral θ (r : G) (m.quotient r) f := by
  subst H
  let : (m.centralizer r).IsMulRightInvariant := m.rightInvariant r
  obtain ⟨kr, hkr⟩ := hm r
  have hμ : m.centralizer r = (1 : ℝ≥0) • k.haar := by
    simpa only [one_smul] using hkr
  have hνr : ν = m.quotient r := by
    simpa only [one_smul] using hν.eq_smul_of_subgroup_smul
      (isClosed_twistedCentralizer θ hθ (r : G)) (m.compatible r) hμ
  have hslice : slice = twistedOrbitFunction θ (r : G) f := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => exact hs g
  rw [hslice, hνr]
  exact ⟨Iff.rfl, rfl⟩

private theorem RegularOrbitalChart.exists_profile [T2Space B] [μ.IsMulLeftInvariant]
    (hm : m.IsNormalized) (hθ : Continuous θ) (hp : Continuous p)
    (hB : HasCompactOpenNeighborhoodBasis B) (c : RegularOrbitalChart θ p) (b₀ : c.parameters)
    (f : SchwartzBruhat G) (hf : Function.support f ⊆ R) :
    ∃ P : c.parameters → ℂ, IsLocallyConstant P ∧
      ∀ (r : R) (hr : p r ∈ c.parameters),
        Integrable (twistedOrbitFunction θ (r : G) (f : G → ℂ)) (m.quotient r) ∧
        twistedOrbitalIntegral θ (r : G) (m.quotient r) f = P ⟨p r, hr⟩ := by
  obtain ⟨V, hV, H, s, e, hH, hep, he⟩ := c
  change ↥V at b₀
  have hH₀ := hH b₀
  subst H
  let H₀ := twistedCentralizer θ (s b₀ : G)
  let ν : Measure (LeftQuotient H₀) := m.quotient (s b₀)
  obtain ⟨k, hk⟩ := hm (s b₀)
  have compatible_of_eq (η : Measure H₀) (hη : m.centralizer (s b₀) = η) :
      let _ : η.IsMulRightInvariant := hη ▸ m.rightInvariant (s b₀)
      IsCompatible H₀ μ η ν := by
    subst η
    exact m.compatible (s b₀)
  let : k.haar.IsMulRightInvariant := hk ▸ m.rightInvariant (s b₀)
  have hν : IsCompatible H₀ μ k.haar ν := compatible_of_eq k.haar hk
  let : ν.Regular := hν.regular
  let : T2Space (LeftQuotient H₀) := leftQuotient_t2Space H₀
    (isClosed_twistedCentralizer θ hθ (s b₀ : G))
  have hfc : IsCompact (Subtype.val ⁻¹' Function.support f : Set R) :=
    (IsInducing.subtypeVal.isCompact_preimage_iff (by simpa using hf)).mpr
      (Hecke.TestFunction.isCompact_support f)
  let fR : SchwartzBruhat R :=
    ⟨(f : G → ℂ) ∘ Subtype.val, f.locallyConstant.comp_continuous continuous_subtype_val,
      HasCompactSupport.of_support_subset_isCompact hfc subset_rfl⟩
  obtain ⟨hi, hl⟩ := integrable_locallyConstant_orbitChart p hp hB hV e
    (fun b q => hep (b, q)) ν fR
  refine ⟨(fun b => ∫ q, fR (e (b, q)).val ∂ν), hl, ?_⟩
  intro r hr
  let z := e.symm ⟨r, hr⟩
  have hz : e z = ⟨r, hr⟩ := e.apply_symm_apply _
  have hb : z.1 = (⟨p r, hr⟩ : V) := Subtype.ext (by rw [← hep z, hz])
  obtain ⟨g, hg⟩ := Quotient.exists_rep z.2
  have hconj : twistedConj θ g (s z.1 : G) = r := by
    rw [← he z.1 g]
    change (e (z.1, Quotient.mk _ g)).val.val = r
    rw [hg, Prod.mk.eta, hz]
  have hmem : twistedConj θ g (s z.1 : G) ∈ R := hconj.symm ▸ r.property
  have hs : (⟨twistedConj θ g (s z.1 : G), hmem⟩ : R) = r := Subtype.ext hconj
  let integrableAt (a : R) := Integrable (twistedOrbitFunction θ (a : G) (f : G → ℂ)) (m.quotient a)
  let integralAt (a : R) := twistedOrbitalIntegral θ (a : G) (m.quotient a) f
  have ht : (integrableAt r ↔ integrableAt (s z.1)) ∧ integralAt r = integralAt (s z.1) := by
    rw [← hs]
    exact hm.orbitalConj hθ (s z.1) g hmem (f : G → ℂ)
  have hslice := slice_eq_orbitalIntegral hm hθ (hH z.1) k ν hν
    (f : G → ℂ) (fun q => fR (e (z.1, q)).val) (fun a => congrArg f (he z.1 a))
  exact ⟨ht.1.mpr (hslice.1.mp (hi z.1)),
    ht.2.trans (hslice.2.symm.trans (congrArg (fun b => ∫ q, fR (e (b, q)).val ∂ν) hb))⟩

/-- Product charts and compatible normalized measures give regular orbital profiles. -/
def RegularOrbitalProfilesFromChartsStatement : Prop :=
  ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] {B : Type v} [TopologicalSpace B] [T2Space B]
    (θ : G →* G), Continuous θ → ∀ (μ : Measure G) [μ.IsMulLeftInvariant]
    (R : Set G), IsOpen R → ∀ (p : R → B), Continuous p → HasCompactOpenNeighborhoodBasis B →
    (∀ (r : R) (g : G), ∃ s : R, (s : G) = twistedConj θ g r ∧ p s = p r) →
    (∀ r : R, ∃ c : RegularOrbitalChart θ p, p r ∈ c.parameters) →
    ∀ m : RegularOrbitalMeasures θ μ R, m.IsNormalized → RegularOrbitalProfileData m p

theorem regularOrbitalProfilesFromCharts : RegularOrbitalProfilesFromChartsStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ B _ _ θ hθ μ _ R hR p hp hB horbit hcharts m hm
  have hlocal (r₀ : R) (f : SchwartzBruhat G) (hf : Function.support f ⊆ R) :
      ∃ (V : Set B) (_ : IsOpen V) (_ : p r₀ ∈ V) (P : V → ℂ), IsLocallyConstant P ∧
        ∀ (r : R) (hr : p r ∈ V),
          Integrable (twistedOrbitFunction θ (r : G) (f : G → ℂ)) (m.quotient r) ∧
          twistedOrbitalIntegral θ (r : G) (m.quotient r) f = P ⟨p r, hr⟩ := by
    obtain ⟨c, hc⟩ := hcharts r₀
    obtain ⟨P, hPl, hP⟩ := c.exists_profile hm hθ hp hB ⟨p r₀, hc⟩ f hf
    exact ⟨c.parameters, c.isOpen, hc, P, hPl, hP⟩
  refine ⟨hR, hp, isOpenMap_of_orbitalCharts hcharts, horbit, ?_, ?_, ?_⟩
  · intro r f hf
    obtain ⟨V, _, hr, P, _, hP⟩ := hlocal r f hf
    exact (hP r hr).1
  · intro f hf
    apply (IsLocallyConstant.iff_exists_open _).mpr
    intro r
    obtain ⟨V, hV, hr, P, hPl, hP⟩ := hlocal r f hf
    obtain ⟨W, hW, hrW, hWP⟩ := hPl.exists_open (⟨p r, hr⟩ : V)
    refine ⟨p ⁻¹' (Subtype.val '' W), (hV.isOpenMap_subtype_val _ hW).preimage hp,
      ⟨⟨p r, hr⟩, hrW, rfl⟩, ?_⟩
    rintro r' ⟨b, hb, hbr'⟩
    have hr' : p r' ∈ V := hbr' ▸ b.property
    rw [(hP r' hr').2, (hP r hr).2, show (⟨p r', hr'⟩ : V) = b from Subtype.ext hbr'.symm]
    exact hWP b hb
  · intro f hf r s hs
    obtain ⟨V, _, hr, P, _, hP⟩ := hlocal r f hf
    have hps : p s ∈ V := hs ▸ hr
    exact (hP r hr).2.trans ((congrArg P (Subtype.ext hs)).trans (hP s hps).2.symm)

end Langlands.BaseChange

import Langlands.BaseChange.RegularTransferMeasures
import Langlands.Analysis.Local.QuotientMass
import Langlands.Representation.Hecke.TestFunction
import Langlands.Topology.LocallyProfinite

noncomputable section

open Set MeasureTheory Topology

namespace Langlands.BaseChange

open Langlands.HarmonicAnalysis Langlands.QuotientIntegration Langlands.TraceFormula
open Langlands.Topology (IsLocallyProfinite)

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

variable {G B : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [MeasurableSpace G] [BorelSpace G] [TopologicalSpace B] [T2Space B]
variable {θ : G →* G} {μ : Measure G} {R : Set G}

/-- Choices of the actual centralizer and quotient measures on an open
regular locus. The compatibility field uses the chosen right invariance. -/
structure RegularOrbitalMeasures (θ : G →* G) (μ : Measure G) (R : Set G) where
  centralizer (r : R) : Measure (twistedCentralizer θ (r : G))
  quotient (r : R) : Measure (LeftQuotient (twistedCentralizer θ (r : G)))
  haar (r : R) : (centralizer r).IsHaarMeasure
  rightInvariant (r : R) : (centralizer r).IsMulRightInvariant
  compatible (r : R) : let _ := rightInvariant r
    IsCompatible (twistedCentralizer θ (r : G)) μ (centralizer r) (quotient r)

/-- Analytic hypotheses for normalized orbital integrals on an open locus
with a continuous open map to orbit parameters. They apply to the Library's
orbital function and quotient integral. -/
structure RegularOrbitalProfileData (m : RegularOrbitalMeasures θ μ R) (p : R → B) : Prop where
  isOpen : IsOpen R
  continuous : Continuous p
  isOpenMap : IsOpenMap p
  orbit (r : R) (g : G) : ∃ s : R, (s : G) = twistedConj θ g r ∧ p s = p r
  integrable (r : R) (f : SchwartzBruhat G) (hf : Function.support f ⊆ R) :
    Integrable (twistedOrbitFunction θ (r : G) (f : G → ℂ)) (m.quotient r)
  locallyConstant (f : SchwartzBruhat G) (hf : Function.support f ⊆ R) :
    IsLocallyConstant (fun r : R => twistedOrbitalIntegral θ (r : G) (m.quotient r) f)
  invariant (f : SchwartzBruhat G) (hf : Function.support f ⊆ R) (r s : R) (hs : p r = p s) :
    twistedOrbitalIntegral θ (r : G) (m.quotient r) f =
      twistedOrbitalIntegral θ (s : G) (m.quotient s) f

namespace RegularOrbitalProfileData

variable {m : RegularOrbitalMeasures θ μ R} {p : R → B}

omit [T2Space B] in
private theorem orbitalIntegral_zero_of_disjoint_image
    (d : RegularOrbitalProfileData m p) {f : SchwartzBruhat G}
    (r : R) (hr : p r ∉ p '' (Subtype.val ⁻¹' Function.support f)) :
    twistedOrbitalIntegral θ (r : G) (m.quotient r) f = 0 := by
  have hz : twistedOrbitFunction θ (r : G) (f : G → ℂ) = 0 := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨s, hs, hp⟩ := d.orbit r g
      change f (twistedConj θ g r) = 0
      rw [← hs]
      by_contra h
      exact hr ⟨s, h, hp⟩
  simp [twistedOrbitalIntegral, hz]

/-- The quotient integrals descend to a compactly supported locally constant
function on the parameter space, with zero extension off the parameter image. -/
theorem exists_profile (d : RegularOrbitalProfileData m p)
    {f : SchwartzBruhat G} (hf : Function.support f ⊆ R) :
    ∃ P : SchwartzBruhat B, Function.support P ⊆ range p ∧
      ∀ r : R, P (p r) = twistedOrbitalIntegral θ (r : G) (m.quotient r) f := by
  classical
  let F : R → ℂ := fun r => twistedOrbitalIntegral θ (r : G) (m.quotient r) f
  let P : B → ℂ := fun b => if h : b ∈ range p then F h.choose else 0
  have happ (r : R) : P (p r) = F r := by
    rw [show P (p r) = F (mem_range_self r).choose from dite_eq_left (mem_range_self r)]
    exact d.invariant f hf _ _ (mem_range_self r).choose_spec
  let H := p '' (Subtype.val ⁻¹' Function.support f)
  have hHc : IsCompact H := by
    have hK : IsCompact (Subtype.val ⁻¹' Function.support f : Set R) :=
      (IsInducing.subtypeVal.isCompact_preimage_iff
        (by simpa using hf)).mpr (Hecke.TestFunction.isCompact_support f)
    exact hK.image d.continuous
  have hPH : Function.support P ⊆ H := by
    intro b hb
    by_contra hn
    apply hb
    by_cases h : b ∈ range p
    · obtain ⟨r, rfl⟩ := h
      rw [happ]
      exact orbitalIntegral_zero_of_disjoint_image d r hn
    · exact dite_eq_right h
  have hPl : IsLocallyConstant P := by
    apply (IsLocallyConstant.iff_exists_open P).mpr
    intro b
    by_cases h : b ∈ range p
    · obtain ⟨r, rfl⟩ := h
      obtain ⟨V, hVo, hrV, hV⟩ := (d.locallyConstant f hf).exists_open r
      refine ⟨p '' V, d.isOpenMap _ hVo, mem_image_of_mem _ hrV, ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      rw [happ, happ]
      exact hV s hs
    · have hHr : H ⊆ range p := image_subset_range _ _
      refine ⟨Hᶜ, hHc.isClosed.isOpen_compl, fun hb => h (hHr hb), ?_⟩
      intro b' hb'
      have hz : P b' = 0 := by
        by_contra hn
        exact hb' (hPH hn)
      simpa only [P, dite_eq_right h] using hz
  exact ⟨⟨P, hPl, HasCompactSupport.of_support_subset_isCompact hHc hPH⟩,
    hPH.trans (image_subset_range _ _), happ⟩

omit [T2Space B] in
private theorem exists_compactOpen_cover (d : RegularOrbitalProfileData m p)
    (hG : IsLocallyProfinite G) {S : Set B} (hSc : IsCompact S) (hS : S ⊆ range p) :
    ∃ K : Set G, IsOpen K ∧ IsCompact K ∧ K ⊆ R ∧
      S ⊆ p '' (Subtype.val ⁻¹' K) := by
  classical
  choose V hVr hVo hVc hVR using fun r : R =>
    hG.2 (r : G) R (d.isOpen.mem_nhds r.property)
  have hcover : S ⊆ ⋃ r : R, p '' (Subtype.val ⁻¹' V r) := by
    intro b hb
    obtain ⟨r, rfl⟩ := hS hb
    exact mem_iUnion.mpr ⟨r, mem_image_of_mem p (hVr r)⟩
  obtain ⟨t, ht⟩ := hSc.elim_finite_subcover _ (fun r =>
    d.isOpenMap _ ((hVo r).preimage continuous_subtype_val)) hcover
  refine ⟨⋃ r ∈ t, V r, isOpen_biUnion (fun r _ => hVo r),
    t.finite_toSet.isCompact_biUnion (fun r _ => hVc r), iUnion₂_subset (fun r _ => hVR r), ?_⟩
  simpa only [preimage_iUnion, image_iUnion] using ht

variable [T2Space G]

omit [T2Space B] in
private theorem characteristic_orbitalIntegral_ne_zero (d : RegularOrbitalProfileData m p)
    (hθ : Continuous θ) {K : Set G} (hKo : IsOpen K) (hKc : IsCompact K) (hK : K ⊆ R)
    (r : R) (hr : (r : G) ∈ K) :
    twistedOrbitalIntegral θ (r : G) (m.quotient r)
      (Hecke.TestFunction.characteristic ⟨hKc.isClosed, hKo⟩ hKc) ≠ 0 := by
  let H := twistedCentralizer θ (r : G)
  let u : LeftQuotient H → G := twistedOrbitFunction θ (r : G) id
  let C := u ⁻¹' K
  let ν := m.quotient r
  let A := Hecke.TestFunction.characteristic ⟨hKc.isClosed, hKo⟩ hKc
  have hu : Continuous u := by
    apply (leftQuotient_isOpenQuotientMap H).isQuotientMap.continuous_iff.mpr
    exact (continuous_inv.mul continuous_const).mul hθ
  have hCo : IsOpen C := hKo.preimage hu
  have htest : twistedOrbitFunction θ (r : G) (A : G → ℂ) =
      C.indicator (fun _ => (1 : ℂ)) := by
    funext q
    induction q using Quotient.inductionOn with
    | h g => rfl
  have hint := d.integrable r A ((Hecke.TestFunction.support_characteristic _ _).trans_le hK)
  rw [htest, integrable_indicator_iff hCo.measurableSet] at hint
  have hCfin : ν C < ⊤ := ((integrableOn_const_iff (by finiteness)).mp hint).resolve_left (by simp)
  let := m.rightInvariant r
  let : ν.IsOpenPosMeasure := (m.compatible r).isOpenPosMeasure
  have hCne : C.Nonempty := ⟨leftQuotientMap H 1, by
    change (1 : G)⁻¹ * (r : G) * θ 1 ∈ K
    simpa using hr⟩
  have hCpos : 0 < ν C := hCo.measure_pos ν hCne
  change (∫ q, twistedOrbitFunction θ (r : G) A q ∂ν) ≠ 0
  rw [htest, integral_indicator_const _ hCo.measurableSet]
  simpa [Complex.real_smul, measureReal_def] using
    (ENNReal.toReal_pos hCpos.ne' hCfin.ne).ne'

/-- Realization of an orbital-integral profile using a single compact open
cutoff and its orbital integrals. -/
theorem exists_test (d : RegularOrbitalProfileData m p) (hG : IsLocallyProfinite G)
    (hθ : Continuous θ) (P : SchwartzBruhat B) (hP : Function.support P ⊆ range p) :
    ∃ f : SchwartzBruhat G, Function.support f ⊆ R ∧
      ∀ r : R, twistedOrbitalIntegral θ (r : G) (m.quotient r) f = P (p r) := by
  classical
  obtain ⟨K, hKo, hKc, hKR, hPK⟩ :=
    exists_compactOpen_cover d hG (Hecke.TestFunction.isCompact_support P) hP
  let A := Hecke.TestFunction.characteristic ⟨hKc.isClosed, hKo⟩ hKc
  obtain ⟨Q, _, hQ⟩ := d.exists_profile (f := A)
    ((Hecke.TestFunction.support_characteristic _ _).trans_le hKR)
  have hQne (b : B) (hb : P b ≠ 0) : Q b ≠ 0 := by
    obtain ⟨r, hr, rfl⟩ := hPK hb
    rw [hQ]
    exact characteristic_orbitalIntegral_ne_zero d hθ hKo hKc hKR r hr
  let ratio : B → ℂ := fun b => P b / Q b
  have hratio : IsLocallyConstant ratio :=
    P.locallyConstant.comp₂ Q.locallyConstant (· / ·)
  let a : K → ℂ := fun x => ratio (p ⟨x, hKR x.property⟩)
  have ha : IsLocallyConstant a := hratio.comp_continuous (d.continuous.comp
    (continuous_subtype_val.subtype_mk fun x : K => hKR x.property))
  let f : G → ℂ := fun x => if hx : x ∈ K then a ⟨x, hx⟩ else 0
  have hfl : IsLocallyConstant f := by
    apply (IsLocallyConstant.iff_exists_open f).mpr
    intro x
    by_cases hx : x ∈ K
    · obtain ⟨U, hUo, hxU, hU⟩ := ha.exists_open ⟨x, hx⟩
      refine ⟨Subtype.val '' U, hKo.isOpenMap_subtype_val _ hUo,
        ⟨⟨x, hx⟩, hxU, rfl⟩, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      simpa [f, hx, y.property] using hU y hy
    · exact ⟨Kᶜ, hKc.isClosed.isOpen_compl, hx, fun y hy => by simp [f, hx, show y ∉ K from hy]⟩
  have hfK : Function.support f ⊆ K := by
    intro x hx
    by_contra hn
    exact hx (dite_eq_right hn)
  refine ⟨⟨f, hfl, HasCompactSupport.of_support_subset_isCompact hKc hfK⟩, hfK.trans hKR, ?_⟩
  intro r
  have hfun : twistedOrbitFunction θ (r : G) f = fun q =>
      ratio (p r) * twistedOrbitFunction θ (r : G) (A : G → ℂ) q := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      obtain ⟨s, hs, hp⟩ := d.orbit r g
      change f (twistedConj θ g r) = ratio (p r) * A (twistedConj θ g r)
      rw [← hs, show A (s : G) = K.indicator (fun _ => (1 : ℂ)) s from rfl]
      by_cases hsK : (s : G) ∈ K
      · have hsub : (⟨(s : G), hKR hsK⟩ : R) = s := Subtype.ext rfl
        simp [f, a, hsK, hsub, hp]
      · simp [f, hsK]
  change (∫ q, twistedOrbitFunction θ (r : G) f q ∂m.quotient r) = P (p r)
  rw [hfun, integral_const_mul, ← twistedOrbitalIntegral, ← hQ]
  by_cases hp : P (p r) = 0
  · simp [ratio, hp]
  · exact div_mul_cancel₀ _ (hQne _ hp)

end RegularOrbitalProfileData

end Langlands.BaseChange

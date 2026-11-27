import Langlands.BaseChange.TwistedLocalDescentStatement
import Langlands.BaseChange.TwistedLocalDescent.MassLocal
import Langlands.BaseChange.TwistedLocalDescent.ConstantTermIntegral
import Langlands.BaseChange.TwistedLocalDescent.Windows
import Langlands.BaseChange.TwistedLocalDescent.Classification
import Langlands.BaseChange.TwistedLocalDescent.Support
import Langlands.BaseChange.ExactNormLeviCentralizer
import Langlands.BaseChange.RelativeParabolicDiscriminantRegular

/-! # Proof of the local descent of the twisted constant term

The pieces are the restrictions of the normalized twisted constant term
(`normalizedTwistedParabolicConstantTerm`) to the twisted saturations of small windows around the
Levi representatives. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set
open scoped _root_.Topology
open Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.JacquetLanglands
open scoped ENNReal NNReal

universe u v

section Pieces

variable {X : Type*} [TopologicalSpace X]

/-- The restriction of a test function to an open set `S` is a test function when the support
of the function is covered by `S` and an open set disjoint from `S`. -/
theorem indicator_mem_schwartzBruhat (f : SchwartzBruhat X) {S T : Set X} (hS : IsOpen S)
    (hT : IsOpen T) (hST : Disjoint S T) (hcover : ∀ x, f x ≠ 0 → x ∈ S ∪ T) :
    S.indicator (f : X → ℂ) ∈ schwartzBruhatSubmodule X := by
  refine ⟨?_, f.hasCompactSupport.mono fun x hx => ?_⟩
  swap
  · rw [Function.mem_support] at hx ⊢
    intro h
    exact hx (by simp [h])
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  by_cases hxS : x ∈ S
  · have h1 := hS.mem_nhds hxS
    have h2 := (IsLocallyConstant.iff_eventually_eq _).mp f.locallyConstant x
    filter_upwards [h1, h2] with y hy hfy
    rw [Set.indicator_of_mem hy, Set.indicator_of_mem hxS, hfy]
  · by_cases hxT : x ∈ T
    · filter_upwards [hT.mem_nhds hxT] with y hy
      rw [Set.indicator_of_notMem (Set.disjoint_right.mp hST hy), Set.indicator_of_notMem hxS]
    · have hfx : f x = 0 := by
        by_contra h
        rcases hcover x h with h' | h'
        · exact hxS h'
        · exact hxT h'
      have h2 := (IsLocallyConstant.iff_eventually_eq _).mp f.locallyConstant x
      filter_upwards [h2] with y hfy
      rw [Set.indicator_of_notMem hxS]
      by_cases hy : y ∈ S
      · rw [Set.indicator_of_mem hy, hfy, hfx]
      · rw [Set.indicator_of_notMem hy]

end Pieces

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  TwistedVanDijk.unipotentSubgroup_secondCountable TwistedVanDijk.unipotentSubgroup_locallyCompact
  TwistedVanDijk.parabolic_secondCountable TwistedVanDijk.parabolic_locallyCompact
  TwistedVanDijk.integralGL_compactSpace TwistedVanDijk.integralGL_secondCountable

/-- **Local descent of the twisted constant term.** -/
theorem twistedLocalDescent : TwistedLocalDescentStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ _ σ l n hE hn B δ γ hδγ hγ k m hm d hd
  let _ : MeasurableSpace (GeneralLinear n E) := borel _
  have _ : BorelSpace (GeneralLinear n E) := ⟨rfl⟩
  let _ : MeasurableSpace (B.Levi E) := borel _
  have _ : BorelSpace (B.Levi E) := ⟨rfl⟩
  have : FiniteDimensional F E := hE.1
  intro μG _ μM _ μU _ μK _ _ hG hM hU Ω hΩo hΩd
  have hσ := hE.pow_eq_one
  -- windows
  obtain ⟨Ω', hΩ'o, hdΩ', hΩ'Ω, hcop, hsep⟩ :=
    exists_windows (l := l) σ B hγ hm (fun j i => (hd j).2 i) Ω hΩo hΩd
  set θS := (leviAut σ B).toMonoidHom
  set S : Fin k → Set (B.Levi E) := fun j => twistedConjugacySaturation θS (Ω' j)
  have hSo : ∀ j, IsOpen (S j) := fun j => isOpen_twistedConjugacySaturation θS (hΩ'o j)
  have hSdisj : ∀ j j', j ≠ j' → Disjoint (S j) (S j') := by
    intro j j' hjj
    rw [Set.disjoint_left]
    intro z hz hz'
    obtain ⟨y, u, hu, hzu⟩ := Set.mem_iUnion.1 hz
    obtain ⟨y', u', hu', hzu'⟩ := Set.mem_iUnion.1 hz'
    apply hsep j j' hjj u hu u' hu'
    have h1 := normCoeffs_twistedConj σ l B hσ y u
    have h2 := normCoeffs_twistedConj σ l B hσ y' u'
    change normCoeffs σ l B (y * u * (θS y)⁻¹) = _ at h1
    change normCoeffs σ l B (y' * u' * (θS y')⁻¹) = _ at h2
    rw [← h1, ← h2]
    change normCoeffs σ l B (twistedConjugationHomeomorph θS y u) =
      normCoeffs σ l B (twistedConjugationHomeomorph θS y' u')
    rw [hzu, hzu']
  have hSsub : ∀ j, S j ⊆ twistedConjugacySaturation θS (Ω j) := fun j =>
    Set.iUnion_mono fun y => Set.image_mono (hΩ'Ω j)
  -- representatives and nonvanishing discriminants
  choose x hx using fun j => (hd j).1
  have hreg : ∀ j, IsRegularSemisimple (B.leviEmbedding F (m j)) := fun j => by
    obtain ⟨y, hy⟩ := hm.1 j
    rw [← hy]
    exact isRegularSemisimple_conj hγ y
  have hD : ∀ j, twistedRelativeParabolicDiscriminant B σ (d j) ≠ 0 := fun j =>
    twistedRelativeParabolicDiscriminant_ne_zero_of_cyclicNorm B hE
      (cyclicNorm_leviEmbedding_eq_of_blockwise B (m j) (d j) (hd j).2) (hreg j)
  -- the local mass neighbourhoods
  have hloc := fun j => exists_nhds_integral_twistedOrbitalKernel B σ hE μG μM μU μK hG hM hU
    (Ω' j) (hΩ'o j) (hcop j) (d j) (hdΩ' j) (hD j) (x j)
  choose V hVo hVδ hVmass using hloc
  have hδV : ∀ j, δ ∈ V j := by
    intro j
    have := hVδ j
    rwa [← hx j, show x j * ((x j)⁻¹ * δ * entrywiseAut σ n (x j)) * (entrywiseAut σ n (x j))⁻¹ =
      δ by group] at this
  -- the support neighbourhood
  obtain ⟨U₁, hU₁o, hδU₁, hU₁⟩ := exists_nhds_forall_proj_mem (entrywiseAut σ n)
    (continuous_entrywiseAut σ n) (TwistedVanDijk.isCompact_integralGL n)
    (B.parabolic E) (B.isClosed_parabolic E) (B.leviProjection E)
    (B.leviProjectionContinuous E).continuous (isOpen_iUnion hSo) δ (by
      intro κ _ hp
      obtain ⟨j, y, hy⟩ := exists_levi_twistedConj_of_parabolic B hE hδγ hγ hm
        (fun j i => (hd j).2 i) κ⁻¹ ⟨_, hp⟩ (by simp [map_inv])
      refine Set.mem_iUnion.2 ⟨j, ?_⟩
      have : B.leviProjection E ⟨_, hp⟩ = y * d j * (θS y)⁻¹ := by
        rw [← hy]
        change _ = y * (y⁻¹ * B.leviProjection E ⟨_, hp⟩ * leviAut σ B y) * (leviAut σ B y)⁻¹
        group
      rw [this]
      exact twistedConj_mem_twistedConjugacySaturation θS (hdΩ' j) y)
  refine ⟨U₁ ∩ ⋂ j, V j, hU₁o.inter (isOpen_iInter_of_finite hVo),
    ⟨hδU₁, Set.mem_iInter.2 hδV⟩, fun φ hφ => ?_⟩
  set CT := normalizedTwistedParabolicConstantTerm E B σ φ
  -- the twisted constant term vanishes outside the saturations
  have hCT : ∀ z, CT z ≠ 0 → z ∈ ⋃ j, S j := by
    intro z hz
    rw [normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup σ B μU hU μK] at hz
    have hint := right_ne_zero_of_mul hz
    obtain ⟨y, hy⟩ : ∃ y : B.unipotentSubgroup E, ∫ κ, φ ((κ : GeneralLinear n E)⁻¹ *
        B.leviEmbedding E z * (y : GeneralLinear n E) * entrywiseAut σ n κ) ∂μK ≠ 0 := by
      by_contra h
      push Not at h
      exact hint (by rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_zero])
    obtain ⟨κ, hκ⟩ : ∃ κ : TwistedVanDijk.integralGL E n, φ ((κ : GeneralLinear n E)⁻¹ *
        B.leviEmbedding E z * (y : GeneralLinear n E) * entrywiseAut σ n κ) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (by rw [integral_congr_ae (Filter.Eventually.of_forall h), integral_zero])
    have hmem := (hφ hκ).1
    have := hU₁ κ κ.property (TwistedVanDijk.parabolicProduct B (z, y)) (by
      rwa [TwistedVanDijk.coe_parabolicProduct, ← mul_assoc])
    rwa [TwistedVanDijk.leviProjection_parabolicProduct] at this
  -- the pieces
  have hpiece : ∀ j, (S j).indicator (CT : B.Levi E → ℂ) ∈ schwartzBruhatSubmodule (B.Levi E) := by
    intro j
    refine indicator_mem_schwartzBruhat CT (hSo j)
      (T := ⋃ (j' : Fin k) (_ : j' ≠ j), S j')
      (isOpen_iUnion fun j' => isOpen_iUnion fun _ => hSo j') ?_ ?_
    · rw [Set.disjoint_iUnion_right]
      intro j'
      rw [Set.disjoint_iUnion_right]
      intro hj'
      exact hSdisj j j' (Ne.symm hj')
    · intro z hz
      obtain ⟨j', hj'⟩ := Set.mem_iUnion.1 (hCT z hz)
      by_cases h : j' = j
      · subst h
        exact Or.inl hj'
      · exact Or.inr (Set.mem_iUnion₂.2 ⟨j', h, hj'⟩)
  refine ⟨fun j => ⟨(S j).indicator (CT : B.Levi E → ℂ), hpiece j⟩, ?_, ?_, ?_⟩
  · intro j z hz
    refine hSsub j ?_
    by_contra h
    exact hz (Set.indicator_of_notMem h _)
  · intro j
    change ∫ z, (S j).indicator (CT : B.Levi E → ℂ) z ∂μM = _
    rw [integral_indicator_twistedConstantTerm σ B μM μU μK hU (S j) (hSo j).measurableSet φ]
    exact hVmass j φ (fun g hg => (Set.mem_iInter.1 (hφ hg).2) j)
  · intro z
    rw [← normalizedTwistedParabolicConstantTerm_apply_unipotentSubgroup σ B μU hU μK φ z]
    change ∑ j, (S j).indicator (CT : B.Levi E → ℂ) z = CT z
    by_cases hz : ∃ j, z ∈ S j
    · obtain ⟨j₀, hj₀⟩ := hz
      rw [Finset.sum_eq_single j₀ (fun j _ hj => Set.indicator_of_notMem
        (Set.disjoint_left.mp (hSdisj j₀ j (Ne.symm hj)) hj₀) _)
        (fun h => absurd (Finset.mem_univ j₀) h), Set.indicator_of_mem hj₀]
    · push Not at hz
      have hCTz : CT z = 0 := by
        by_contra h
        obtain ⟨j, hj⟩ := Set.mem_iUnion.1 (hCT z h)
        exact hz j hj
      rw [hCTz]
      exact Finset.sum_eq_zero fun j _ => Set.indicator_of_notMem (hz j) _

end Langlands.BaseChange.TwistedLocalDescent

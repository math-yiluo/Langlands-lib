import Langlands.BaseChange.TwistedLocalDescent.IwahoriGroup
import Langlands.BaseChange.TwistedLocalDescent.Beta
import Langlands.BaseChange.TwistedLocalDescent.ModularCharacter

/-! # Reducing the twisted orbital kernel to the opposite unipotent ball

For a group `G`, a subgroup `P`, an endomorphism `θ` of `G`, a set `Q ⊆ P` and a weight `δh` on `P`,
the twisted orbital kernel is `Φ(g) = ∫_Q δh(p) φ(g⁻¹ p θ(g)) dp`. If `θ` restricts to `θP` on `P`,
`Q` and `δh` are invariant under `p ↦ h p θP(h)⁻¹`, `μP` is a left Haar measure and `φ`, `δh` are
continuous, then `Φ(h g) = Δ_P(θP h) Φ(g)`. Over an ultrametric proper nontrivially normed field,
for `G = GL_n` and the standard parabolic `P`, suppose moreover that `θ` is continuous, `θP`
preserves the Haar measure of `P`, `dg = dp dk` for a compact subgroup `K` with `dg` right
invariant, `φ` is bi-invariant under an open subgroup, `U` is a compact congruence subgroup of
radius `0 < r < 1`, and every `k ∈ K` with `Φ(k) ≠ 0` lies in `P U x⁻¹`. Then the integral of `Φ`
over `K` equals the Iwahori constant times the integral of `Z ↦ Φ((1 + Z) x⁻¹)` over the ball of
radius `r` in `𝔲̄`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

section General

variable {X : Type*} [TopologicalSpace X]

theorem IsClopen.continuous_indicator' {s : Set X} (hs : IsClopen s) {f : X → ℂ}
    (hf : Continuous f) : Continuous (s.indicator f) := by
  classical
  rw [← Set.piecewise_eq_indicator]
  exact hf.piecewise (fun a ha => by simp [hs.frontier_eq] at ha) continuous_const

end General

section Kernel

variable {G : Type*} [Group G] {P : Subgroup G} [MeasurableSpace P]

/-- The twisted orbital kernel `Φ(g) = ∫_Q δ(p) φ(g⁻¹ p θ(g)) dp`. -/
def twistedOrbitalKernel (θ : G →* G) (μP : Measure P) (Q : Set P) (δh : P → ℝ) (φ : G → ℂ)
    (g : G) : ℂ :=
  ∫ p, Q.indicator (fun p : P => (δh p : ℂ) * φ (g⁻¹ * p * θ g)) p ∂μP

/-- If `φ` is bi-invariant under a subgroup `V`, the twisted orbital kernel is invariant under
right translation by every `v ∈ V` with `θ(v) ∈ V`, i.e. under `V ∩ θ⁻¹(V)`; this subgroup is open
when `V` is open and `θ` is continuous. -/
theorem twistedOrbitalKernel_mul_right' (θ : G →* G) (μP : Measure P) (Q : Set P) (δh : P → ℝ)
    (φ : G → ℂ) (V : Subgroup G) (hφV : ∀ v ∈ V, ∀ v' ∈ V, ∀ g, φ (v * g * v') = φ g)
    (g : G) {v : G} (hv : v ∈ V) (hθv : θ v ∈ V) :
    twistedOrbitalKernel θ μP Q δh φ (g * v) = twistedOrbitalKernel θ μP Q δh φ g := by
  unfold twistedOrbitalKernel
  congr 1
  funext p
  by_cases hp : p ∈ Q
  · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    congr 1
    rw [mul_inv_rev, map_mul]
    have := hφV v⁻¹ (V.inv_mem hv) (θ v) hθv (g⁻¹ * p * θ g)
    rw [← this]
    group
  · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem continuous_twistedOrbitalKernel (θ : G →* G) (hθ : Continuous θ) (μP : Measure P)
    (Q : Set P) (δh : P → ℝ) (φ : G → ℂ) (V : Subgroup G) (hVo : IsOpen (V : Set G))
    (hφV : ∀ v ∈ V, ∀ v' ∈ V, ∀ g, φ (v * g * v') = φ g) :
    Continuous (twistedOrbitalKernel θ μP Q δh φ) := by
  refine continuous_iff_continuousAt.mpr fun g => ?_
  let V' : Set G := (V : Set G) ∩ θ ⁻¹' (V : Set G)
  have hV'o : IsOpen V' := hVo.inter (hVo.preimage hθ)
  have hnhds : (fun v => g * v) '' V' ∈ 𝓝 g :=
    ((isOpenMap_mul_left g) _ hV'o).mem_nhds ⟨1, ⟨V.one_mem, by simp [V.one_mem]⟩, mul_one g⟩
  refine (continuousAt_const (y := twistedOrbitalKernel θ μP Q δh φ g)).congr ?_
  filter_upwards [hnhds] with y hy
  obtain ⟨v, ⟨hv, hθv⟩, rfl⟩ := hy
  exact (twistedOrbitalKernel_mul_right' θ μP Q δh φ V hφV g hv hθv).symm

variable [BorelSpace P] [LocallyCompactSpace P] [SecondCountableTopology P]

/-- **Covariance of the twisted orbital kernel.** -/
theorem twistedOrbitalKernel_mul_left (θ : G →* G) (θP : P →* P) (hθP : ∀ p, (θP p : G) = θ p)
    (μP : Measure P) [μP.IsHaarMeasure] (Q : Set P) (hQ : MeasurableSet Q)
    (hQinv : ∀ h p, p ∈ Q → h * p * (θP h)⁻¹ ∈ Q) (δh : P → ℝ) (hδc : Continuous δh)
    (hδinv : ∀ h p, δh (h * p * (θP h)⁻¹) = δh p) (φ : G → ℂ) (hφc : Continuous φ)
    (h : P) (g : G) :
    twistedOrbitalKernel θ μP Q δh φ ((h : G) * g) =
      (modularCharacter (θP h) : ℂ) * twistedOrbitalKernel θ μP Q δh φ g := by
  set F : P → ℂ := Q.indicator (fun p : P => (δh p : ℂ) * φ (((h : G) * g)⁻¹ * p * θ ((h : G) * g)))
  have hFm : Measurable F := by
    refine Measurable.indicator ?_ hQ
    exact ((Complex.continuous_ofReal.comp hδc).mul (hφc.comp
      ((continuous_const.mul continuous_subtype_val).mul continuous_const))).measurable
  -- left invariance by `h`, then right translation by `θ(h)⁻¹`
  have hpt : ∀ p : P, F (h * (p * (θP h)⁻¹)) =
      Q.indicator (fun p : P => (δh p : ℂ) * φ (g⁻¹ * p * θ g)) p := by
    intro p
    have hmem : h * (p * (θP h)⁻¹) ∈ Q ↔ p ∈ Q := by
      constructor
      · intro hp
        have := hQinv h⁻¹ _ hp
        simpa [mul_assoc] using this
      · intro hp
        have := hQinv h p hp
        simpa [mul_assoc] using this
    dsimp only [F]
    by_cases hp : p ∈ Q
    · rw [Set.indicator_of_mem (hmem.mpr hp), Set.indicator_of_mem hp]
      have hδ : δh (h * (p * (θP h)⁻¹)) = δh p := by
        rw [← mul_assoc]
        exact hδinv h p
      rw [hδ]
      congr 2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hθP, map_mul, mul_inv_rev]
      group
    · rw [Set.indicator_of_notMem (fun h' => hp (hmem.mp h')), Set.indicator_of_notMem hp]
  have h1 : ∫ p, F p ∂μP = ∫ p, F (h * p) ∂μP := (integral_mul_left_eq_self F h).symm
  have h2 : ∫ p, F (h * (p * (θP h)⁻¹)) ∂μP =
      (modularCharacter (θP h)⁻¹ : ℝ≥0∞).toReal • ∫ p, F (h * p) ∂μP := by
    have hm : Measurable (fun p : P => p * (θP h)⁻¹) := measurable_mul_const _
    have := integral_map (μ := μP) hm.aemeasurable
      (f := fun p => F (h * p)) (hFm.comp (measurable_const_mul h)).aestronglyMeasurable
    rw [map_mul_right_eq_modularCharacter_smul μP, integral_smul_measure] at this
    exact this.symm
  change ∫ p, F p ∂μP = _
  rw [h1]
  have h3 : ∫ p, F (h * (p * (θP h)⁻¹)) ∂μP = twistedOrbitalKernel θ μP Q δh φ g := by
    simp_rw [hpt]
    rfl
  rw [h3] at h2
  rw [h2, map_inv, ENNReal.coe_toReal, NNReal.coe_inv, Complex.real_smul, ← mul_assoc]
  have hpos : (modularCharacter (θP h) : ℝ) ≠ 0 :=
    (NNReal.coe_pos.mpr (modularCharacterFun_pos (θP h))).ne'
  rw [Complex.ofReal_inv, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hpos), one_mul]

end Kernel

section Reduction

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace matrix_locallyCompactSpace
  parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing
  lowerLie_locallyCompact matrix_secondCountable lowerLie_secondCountable
  parabolicSubalgebra_secondCountable

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n)
  [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]
  [MeasurableSpace (Matrix (Fin n) (Fin n) 𝕂)] [BorelSpace (Matrix (Fin n) (Fin n) 𝕂)]

/-- **Reduction of `∫_K Φ` to the opposite unipotent ball.** -/
theorem integral_twistedOrbitalKernel_eq_iwahori
    (θ : GeneralLinear n 𝕂 →* GeneralLinear n 𝕂) (hθ : Continuous θ)
    (θP : B.parabolic 𝕂 →* B.parabolic 𝕂) (hθP : ∀ p, (θP p : GeneralLinear n 𝕂) = θ p)
    (hθPm : Measurable θP)
    (μG : Measure (GeneralLinear n 𝕂)) [μG.IsHaarMeasure] [μG.IsMulRightInvariant]
    (μP : Measure (B.parabolic 𝕂)) [μP.IsHaarMeasure] (hμPθ : μP.map θP = μP)
    (K : Subgroup (GeneralLinear n 𝕂)) [CompactSpace K] (μK : Measure K) [IsFiniteMeasure μK]
    (hIw : μG = (μP.prod μK).map (fun y => (y.1 : GeneralLinear n 𝕂) * y.2))
    (Q : Set (B.parabolic 𝕂)) (hQ : MeasurableSet Q)
    (hQinv : ∀ h p, p ∈ Q → h * p * (θP h)⁻¹ ∈ Q)
    (δh : B.parabolic 𝕂 → ℝ) (hδc : Continuous δh)
    (hδinv : ∀ h p, δh (h * p * (θP h)⁻¹) = δh p)
    (φ : GeneralLinear n 𝕂 → ℂ) (hφc : Continuous φ) (V : Subgroup (GeneralLinear n 𝕂))
    (hVo : IsOpen (V : Set (GeneralLinear n 𝕂)))
    (hφV : ∀ v ∈ V, ∀ v' ∈ V, ∀ g, φ (v * g * v') = φ g)
    (νS : Measure (parabolicSubalgebra (R := 𝕂) B)) [νS.IsAddHaarMeasure]
    (νL : Measure (lowerLie (E := 𝕂) B)) [νL.IsAddHaarMeasure]
    (U : OpenSubgroup (GeneralLinear n 𝕂)) (hUc : IsCompact (U : Set (GeneralLinear n 𝕂)))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (x : GeneralLinear n 𝕂)
    (hrel : ∀ k : K, twistedOrbitalKernel θ μP Q δh φ k ≠ 0 →
      ∃ h : B.parabolic 𝕂, ∃ w ∈ U.toSubgroup, (k : GeneralLinear n 𝕂) = h * w * x⁻¹) :
    ∫ k, twistedOrbitalKernel θ μP Q δh φ k ∂μK =
      ((iwahoriConstant B μG μP νS νL U r).toReal : ℂ) *
        ∫ Z, twistedOrbitalKernel θ μP Q δh φ (lowerUnit B Z * x⁻¹)
          ∂(νL.restrict (Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)) := by
  set Φ := twistedOrbitalKernel θ μP Q δh φ
  set W := U.toSubgroup
  set s := {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ W}
  set RL : Set (lowerLie (E := 𝕂) B) :=
    Subtype.val ⁻¹' closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r
  have : SecondCountableTopology (GeneralLinear n 𝕂) :=
    Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
  have : SecondCountableTopology (B.parabolic 𝕂) :=
    inferInstanceAs (SecondCountableTopology ((B.parabolic 𝕂) : Set (GeneralLinear n 𝕂)))
  have : SecondCountableTopology K :=
    inferInstanceAs (SecondCountableTopology (K : Set (GeneralLinear n 𝕂)))
  have hPcl := isClosed_parabolic_of_normed (𝕂 := 𝕂) B
  have : LocallyCompactSpace (B.parabolic 𝕂) :=
    hPcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let HP : Subgroup (B.parabolic 𝕂) := W.comap (B.parabolic 𝕂).subtype
  have hHPo : IsOpen (HP : Set (B.parabolic 𝕂)) := U.isOpen.preimage continuous_subtype_val
  have hHPc : IsCompact (HP : Set (B.parabolic 𝕂)) :=
    hPcl.isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have hs_eq : s = (HP : Set (B.parabolic 𝕂)) := rfl
  have hs_meas : MeasurableSet s := hHPo.measurableSet
  -- the modular character
  let Δ : B.parabolic 𝕂 → ℝ≥0 := fun q => modularCharacter q
  have hΔ : ∀ q, μP.map (· * q) = (Δ q : ℝ≥0∞) • μP :=
    map_mul_right_eq_modularCharacter_smul μP
  have hΔmul : ∀ a b, Δ (a * b) = Δ a * Δ b := fun a b => map_mul _ a b
  have hΔone : Δ 1 = 1 := map_one _
  have hΔc : Continuous Δ := continuous_modularCharacter μP HP hHPo hHPc
  have hΔW : ∀ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ W → Δ h = 1 :=
    fun h hh => ModularCompactAverage.modularCharacter_eq_one_of_mem HP hHPo hHPc hh
  have hΦc : Continuous Φ := continuous_twistedOrbitalKernel θ hθ μP Q δh φ V hVo hφV
  have hΦ : ∀ (h : B.parabolic 𝕂) (g : GeneralLinear n 𝕂), Φ (h * g) = (Δ h : ℂ) * Φ g := by
    intro h g
    change twistedOrbitalKernel θ μP Q δh φ ((h : GeneralLinear n 𝕂) * g) =
      (Δ h : ℂ) * twistedOrbitalKernel θ μP Q δh φ g
    rw [twistedOrbitalKernel_mul_left θ θP hθP μP Q hQ hQinv δh hδc hδinv φ hφc h g,
      modularCharacter_map_eq μP θP hθPm hμPθ HP hHPo hHPc h]
  -- integrability for the β-identity
  have hWclopen : IsClopen {g : GeneralLinear n 𝕂 | g * x ∈ W} :=
    ⟨U.isClosed.preimage (continuous_id.mul continuous_const),
      U.isOpen.preimage (continuous_id.mul continuous_const)⟩
  have hint : Integrable (fun y : B.parabolic 𝕂 × K =>
      {g : GeneralLinear n 𝕂 | g * x ∈ W}.indicator Φ ((y.1 : GeneralLinear n 𝕂) * y.2))
      (μP.prod μK) := by
    have hcont : Continuous (fun y : B.parabolic 𝕂 × K =>
        {g : GeneralLinear n 𝕂 | g * x ∈ W}.indicator Φ ((y.1 : GeneralLinear n 𝕂) * y.2)) :=
      (IsClopen.continuous_indicator' hWclopen hΦc).comp
        ((continuous_subtype_val.comp continuous_fst).mul
          (continuous_subtype_val.comp continuous_snd))
    refine hcont.integrable_of_hasCompactSupport ?_
    let C₀ : Set (GeneralLinear n 𝕂) :=
      (fun q : GeneralLinear n 𝕂 × GeneralLinear n 𝕂 => q.1 * x⁻¹ * q.2⁻¹) ''
        ((W : Set (GeneralLinear n 𝕂)) ×ˢ (K : Set (GeneralLinear n 𝕂)))
    have hC₀ : IsCompact C₀ := by
      refine (hUc.prod (isCompact_iff_compactSpace.mpr ‹_›)).image ?_
      exact (continuous_fst.mul continuous_const).mul continuous_snd.inv
    have hC : IsCompact ((Subtype.val ⁻¹' C₀ : Set (B.parabolic 𝕂)) ×ˢ (univ : Set K)) :=
      (hPcl.isClosedEmbedding_subtypeVal.isCompact_preimage hC₀).prod isCompact_univ
    refine HasCompactSupport.intro hC fun y hy => ?_
    rw [Set.indicator_of_notMem]
    intro hmem
    have h1 : ((y.1 : B.parabolic 𝕂) : GeneralLinear n 𝕂) ∈ C₀ :=
      ⟨((y.1 : GeneralLinear n 𝕂) * (y.2 : GeneralLinear n 𝕂) * x, (y.2 : GeneralLinear n 𝕂)),
        ⟨hmem, y.2.property⟩, by simp only; group⟩
    exact hy ⟨h1, trivial⟩
  have hβ := integral_indicator_eq_of_iwasawa μG μP μK hIw Δ hΔ hΔmul hΔone hΔc W U.isOpen hΔW
    Φ hΦc hΦ x hrel hint
  -- right translation by `x⁻¹`
  have hc : ∫ g, {g : GeneralLinear n 𝕂 | g * x ∈ W}.indicator Φ g ∂μG =
      ∫ g in (W : Set (GeneralLinear n 𝕂)), Φ (g * x⁻¹) ∂μG := by
    have hWmeas : MeasurableSet (W : Set (GeneralLinear n 𝕂)) := U.isOpen.measurableSet
    rw [← integral_mul_right_eq_self (μ := μG) _ x⁻¹, ← integral_indicator hWmeas]
    congr 1
    funext g
    by_cases hg : g ∈ (W : Set (GeneralLinear n 𝕂))
    · rw [Set.indicator_of_mem (show g * x⁻¹ ∈ {g : GeneralLinear n 𝕂 | g * x ∈ W} by
        simpa using hg), Set.indicator_of_mem hg]
    · rw [Set.indicator_of_notMem (show g * x⁻¹ ∉ {g : GeneralLinear n 𝕂 | g * x ∈ W} by
        simpa using hg), Set.indicator_of_notMem hg]
  -- the Iwahori factorization
  have hIwa := restrict_congruenceBall_eq_map_mul_lowerUnit B μG μP νS νL U hUc hr0 hr1 hU hrange
  have hm : Measurable (fun q : B.parabolic 𝕂 × lowerLie (E := 𝕂) B =>
      (q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2) :=
    ((continuous_subtype_val.comp continuous_fst).mul
      ((continuous_lowerUnit B).comp continuous_snd)).measurable
  have hΦ'c : Continuous fun g : GeneralLinear n 𝕂 => Φ (g * x⁻¹) :=
    hΦc.comp (continuous_id.mul continuous_const)
  have hprod : (μP.restrict s).prod (νL.restrict RL) =
      (μP.prod (νL.restrict RL)).restrict (s ×ˢ univ) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  have hef : ∫ g in (W : Set (GeneralLinear n 𝕂)), Φ (g * x⁻¹) ∂μG =
      ((iwahoriConstant B μG μP νS νL U r).toReal : ℂ) *
        ((μP.real s : ℂ) * ∫ Z, Φ (lowerUnit B Z * x⁻¹) ∂(νL.restrict RL)) := by
    change ∫ g, Φ (g * x⁻¹) ∂(μG.restrict (U : Set (GeneralLinear n 𝕂))) = _
    rw [hIwa, integral_smul_measure, integral_map hm.aemeasurable hΦ'c.aestronglyMeasurable,
      ← Complex.real_smul]
    congr 1
    change ∫ q, Φ ((q.1 : GeneralLinear n 𝕂) * lowerUnit B q.2 * x⁻¹)
      ∂((μP.restrict s).prod (νL.restrict RL)) = _
    rw [hprod, setIntegral_congr_fun (hs_meas.prod MeasurableSet.univ)
      (g := fun q => Φ (lowerUnit B q.2 * x⁻¹)), ← hprod]
    · have hsnd := integral_fun_snd (μ := μP.restrict s) (ν := νL.restrict RL)
        (fun Z => Φ (lowerUnit B Z * x⁻¹))
      rw [hsnd, measureReal_restrict_apply_univ, Complex.real_smul]
    · intro q hq
      simp only
      rw [mul_assoc, hΦ, hΔW q.1 hq.1, NNReal.coe_one, Complex.ofReal_one, one_mul]
  rw [hc, hef] at hβ
  have hsne : (μP.real s : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero, measureReal_def]
    exact (ENNReal.toReal_pos (hHPo.measure_pos μP ⟨1, U.one_mem⟩).ne'
      hHPc.measure_lt_top.ne).ne'
  apply mul_left_cancel₀ hsne
  rw [hβ]
  ring

end Reduction

end Langlands.BaseChange.TwistedLocalDescent

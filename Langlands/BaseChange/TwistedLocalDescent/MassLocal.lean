import Langlands.BaseChange.TwistedLocalDescent.MassIdentity
import Langlands.BaseChange.TwistedLocalDescent.ChartLinear
import Langlands.BaseChange.TwistedLocalDescent.LocalHelpers
import Langlands.BaseChange.TwistedLocalDescent.Rigidity
import Langlands.BaseChange.TwistedLocalDescent.SigmaIsometry
import Langlands.BaseChange.TwistedCharacter.Saturation
import Langlands.BaseChange.TwistedVanDijk.LevelExistence

/-! # The mass of the twisted orbital kernel over a local field

Let `E/F` be a cyclic algebra of nonarchimedean local fields of group `⟨σ⟩` of order `l`, with
`E` carrying the `F`-module topology, and let the Haar measures be normalized by
`μG(K) = μM(M(𝒪)) = μU(U ∩ K) = 1`, `μK` the Haar probability measure on `K = GL_n(𝒪_E)`. For an
open window `Ω` in the Levi `M(E)` on which the norm characteristic polynomials of distinct
blocks at any two points are coprime, a point `d ∈ Ω` with nonzero twisted relative discriminant
and `x ∈ GL_n(E)`, there is an open neighbourhood `V` of `x d σ(x)⁻¹` such that for every test
function `φ` supported in `V`, the integral over `K` of the twisted orbital kernel of `φ` along
the parabolic elements with Levi part in the twisted saturation of `Ω` equals
`|D_{G/M,σ}(d)|_F^{-1/2} ∫ φ`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric
open scoped _root_.Topology
open Langlands.GeneralLinear Langlands.HarmonicAnalysis
open scoped ENNReal NNReal

universe u v

section Saturation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem twistedConj_mem_saturation_of_mem (θ : G →* G) {U : Set G} {z : G}
    (hz : z ∈ twistedConjugacySaturation θ U) (x : G) :
    x * z * (θ x)⁻¹ ∈ twistedConjugacySaturation θ U := by
  obtain ⟨y, ⟨u, hu, rfl⟩⟩ := Set.mem_iUnion.1 hz
  have := twistedConj_mem_twistedConjugacySaturation θ hu (x * y)
  simp only [twistedConjugationHomeomorph_apply, map_mul, mul_inv_rev] at this ⊢
  convert this using 1
  group

end Saturation

section Iwasawa

variable {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

attribute [local instance] LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  TwistedVanDijk.unipotentSubgroup_secondCountable TwistedVanDijk.unipotentSubgroup_locallyCompact
  TwistedVanDijk.parabolic_secondCountable TwistedVanDijk.parabolic_locallyCompact
  TwistedVanDijk.integralGL_compactSpace TwistedVanDijk.integralGL_secondCountable

/-- The Iwasawa decomposition `dg = dp dk` with `dp = dm du`. -/
theorem iwasawa_parabolicHaar [MeasurableSpace (GeneralLinear n E)]
    [BorelSpace (GeneralLinear n E)] [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
    (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
    (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
    (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    (μK : Measure (TwistedVanDijk.integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (hG : μG (TwistedVanDijk.integralGL E n) = 1)
    (hM : μM {x | ∀ i, x i ∈ TwistedVanDijk.integralGL E (B.size i)} = 1)
    (hU : μU {y | (y : GeneralLinear n E) ∈ TwistedVanDijk.integralGL E n} = 1) :
    μG = ((TwistedVanDijk.parabolicHaar B μM μU).prod μK).map
      (fun y => (y.1 : GeneralLinear n E) * y.2) := by
  have h := TwistedVanDijk.iwasawa_measure_eq B μG μM μU μK hG hM hU
  have hprod : (TwistedVanDijk.parabolicHaar B μM μU).prod μK =
      ((μM.prod μU).prod μK).map (Prod.map (TwistedVanDijk.parabolicProduct B) id) := by
    unfold TwistedVanDijk.parabolicHaar
    conv_lhs => rw [← Measure.map_id (μ := μK)]
    exact Measure.map_prod_map _ _ (TwistedVanDijk.measurable_parabolicProduct B) measurable_id
  have hmul : Measurable (fun p : B.parabolic E × TwistedVanDijk.integralGL E n =>
      (p.1 : GeneralLinear n E) * p.2) :=
    (continuous_subtype_val.comp continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd) |>.measurable
  rw [hprod, Measure.map_map hmul
    ((TwistedVanDijk.measurable_parabolicProduct B).prodMap measurable_id)]
  exact h

end Iwasawa

section Main

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [Algebra F E] [IsModuleTopology F E] {n : ℕ} (B : BlockShape n) (σ : E ≃ₐ[F] E)

noncomputable local instance normedLocalE : NontriviallyNormedField E :=
  LocalGalois.localNormedField E

local instance ultrametricLocalE : IsUltrametricDist E := LocalGalois.localNormedField_ultrametric E

theorem properSpace_localField : ProperSpace E :=
  ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace E

attribute [local instance] properSpace_localField
  Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace matrix_locallyCompactSpace
  parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing
  lowerLie_locallyCompact matrix_secondCountable lowerLie_secondCountable
  parabolicSubalgebra_secondCountable
  LocalFieldTopology.t2Space
  LocalFieldTopology.generalLinear_t2Space
  LocalFieldTopology.generalLinear_locallyCompactSpace
  LocalFieldTopology.generalLinear_secondCountableTopology
  TwistedVanDijk.unipotentSubgroup_secondCountable TwistedVanDijk.unipotentSubgroup_locallyCompact
  TwistedVanDijk.parabolic_secondCountable TwistedVanDijk.parabolic_locallyCompact
  TwistedVanDijk.integralGL_compactSpace TwistedVanDijk.integralGL_secondCountable

/-- A metric radius about the identity inside an open neighbourhood of `1` in `GL_n(E)`. -/
theorem exists_radius_subset {O : Set (GeneralLinear n E)} (hO : IsOpen O) (h1 : 1 ∈ O) :
    ∃ ε > 0, ∀ g : GeneralLinear n E, ‖g.val - 1‖ < ε → g ∈ O := by
  have hemb := isOpenEmbedding_val_generalLinear (𝕂 := E) (n := n)
  have hopen : IsOpen ((fun g : GeneralLinear n E => g.val) '' O) := hemb.isOpenMap O hO
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 1 ⟨1, h1, rfl⟩
  refine ⟨ε, hε, fun g hg => ?_⟩
  have : g.val ∈ ball (1 : Matrix (Fin n) (Fin n) E) ε := by rwa [mem_ball, dist_eq_norm]
  obtain ⟨g', hg', hgg⟩ := hball this
  rwa [show g = g' from Units.ext hgg.symm]

/-- **The mass of the twisted orbital kernel near `x d σ(x)⁻¹`.** -/
theorem exists_nhds_integral_twistedOrbitalKernel {l : ℕ} (hE : IsCyclicAlgebra σ l)
    [FiniteDimensional F E] [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
    (μG : Measure (GeneralLinear n E)) [μG.IsHaarMeasure]
    (μM : Measure (B.Levi E)) [μM.IsHaarMeasure]
    (μU : Measure (B.unipotentSubgroup E)) [μU.IsHaarMeasure]
    (μK : Measure (TwistedVanDijk.integralGL E n)) [μK.IsHaarMeasure] [IsProbabilityMeasure μK]
    (hG : μG (TwistedVanDijk.integralGL E n) = 1)
    (hM : μM {x | ∀ i, x i ∈ TwistedVanDijk.integralGL E (B.size i)} = 1)
    (hU : μU {y | (y : GeneralLinear n E) ∈ TwistedVanDijk.integralGL E n} = 1)
    (Ω : Set (B.Levi E)) (hΩ : IsOpen Ω)
    (hcop : ∀ x ∈ Ω, ∀ x' ∈ Ω, ∀ i i', i ≠ i' →
      IsCoprime (normCharpoly σ l B x' i') (normCharpoly σ l B x i))
    (d : B.Levi E) (hd : d ∈ Ω)
    (hD : twistedRelativeParabolicDiscriminant B σ d ≠ 0) (x : GeneralLinear n E) :
    ∃ V : Set (GeneralLinear n E), IsOpen V ∧
      x * B.leviEmbedding E d * (entrywiseAut σ n x)⁻¹ ∈ V ∧
      ∀ φ : SchwartzBruhat (GeneralLinear n E), Function.support φ ⊆ V →
        ∫ k, twistedOrbitalKernel (Matrix.GeneralLinearGroup.map (σ : E →+* E))
            (TwistedVanDijk.parabolicHaar B μM μU)
            {p | B.leviProjection E p ∈ twistedConjugacySaturation (leviAut σ B).toMonoidHom Ω}
            (fun p => (parabolicHalfModulusNNReal B p : ℝ)) φ k ∂μK =
          (((Real.sqrt (LocalField.residueNormalizedAbsoluteValue F
            (twistedRelativeParabolicDiscriminant B σ d)))⁻¹ : ℝ) : ℂ) * ∫ g, φ g ∂μG := by
  let _ : MeasurableSpace (Matrix (Fin n) (Fin n) E) := borel _
  have _ : BorelSpace (Matrix (Fin n) (Fin n) E) := ⟨rfl⟩
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) (σ : E →+* E)
  have hσ : ∀ a : E, ‖(σ : E →+* E) a‖ = ‖a‖ := fun a => norm_algEquiv_eq hE.pow_eq_one hE.pos a
  have hdet := det_chartLinear_ne_zero B σ hE d hD
  set A₀ := chartLinearEquiv B σ d hdet
  obtain ⟨C, hC0, hC⟩ := exists_norm_symm_chartLinearEquiv_le B σ d hdet
  set dG := B.leviEmbedding E d
  set κ := max (‖(dG⁻¹).val‖ * ‖dG.val‖) 1
  have hκ0 : 0 ≤ κ := zero_le_one.trans (le_max_right _ _)
  obtain ⟨r₀, hr₀, hball⟩ := exists_congruenceBall (𝕂 := E) (n := n)
  -- the window neighbourhood of `1`
  set Wp : Set (B.parabolic E) := {h | d * B.leviProjection E h ∈ Ω}
  have hWp : IsOpen Wp :=
    hΩ.preimage (continuous_const.mul (B.leviProjectionContinuous E).continuous)
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp hWp
  have h1O : (1 : GeneralLinear n E) ∈ O := by
    have : (1 : B.parabolic E) ∈ Wp := by
      change d * B.leviProjection E 1 ∈ Ω
      rwa [map_one, mul_one]
    rw [← hOeq] at this
    exact this
  obtain ⟨ε, hε, hεO⟩ := exists_radius_subset hO h1O
  -- the radius
  set r := min r₀ (min (1 / 2) (min (ε / 2) (1 / (2 * (C * κ) + 2))))
  have hden : 0 < 2 * (C * κ) + 2 := by positivity
  have hr0 : 0 < r := lt_min hr₀ (lt_min (by norm_num) (lt_min (by linarith) (by positivity)))
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  have hr1 : r < 1 := (min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt (by norm_num))
  have hrε : r < ε :=
    (min_le_right _ _).trans_lt ((min_le_right _ _).trans_lt ((min_le_left _ _).trans_lt
      (by linarith)))
  have hsmall : C * (κ * r) < 1 := by
    have hrle : r ≤ 1 / (2 * (C * κ) + 2) :=
      (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
    have hCκ : 0 ≤ C * κ := mul_nonneg hC0 hκ0
    calc C * (κ * r) = (C * κ) * r := by ring
      _ ≤ (C * κ) * (1 / (2 * (C * κ) + 2)) := mul_le_mul_of_nonneg_left hrle hCκ
      _ < 1 := by
        rw [mul_one_div, div_lt_one hden]
        linarith
  obtain ⟨U, hUc, hUeq, hrange⟩ := hball r ⟨hr0, hrr₀⟩
  have hUO : ∀ g ∈ U, g ∈ O := by
    intro g hg
    have : g ∈ (U : Set (GeneralLinear n E)) := hg
    rw [hUeq, mem_ofPred_eq, mem_closedBall_zero_iff] at this
    exact hεO g (this.trans_lt hrε)
  -- the radius `s` inside `A(ball)`
  obtain ⟨s₁, hs₁, hs₁A⟩ : ∃ s₁ > 0, ball (0 : Matrix (Fin n) (Fin n) E) s₁ ⊆
      A₀ '' ball 0 r := by
    have hopen : IsOpen (A₀ '' ball (0 : Matrix (Fin n) (Fin n) E) r) :=
      A₀.toHomeomorph.isOpenMap _ isOpen_ball
    exact Metric.isOpen_iff.mp hopen 0 ⟨0, mem_ball_self hr0, map_zero A₀⟩
  set s := min s₁ r
  have hs0 : 0 < s := lt_min hs₁ hr0
  have hsr : s ≤ r := min_le_right _ _
  have hsA : ball (0 : Matrix (Fin n) (Fin n) E) s ⊆ A₀ '' closedBall 0 r :=
    (ball_subset_ball (min_le_left _ _)).trans (hs₁A.trans (image_mono ball_subset_closedBall))
  set Us : Set (GeneralLinear n E) := {g | ‖g.val - 1‖ < s}
  have hUs : IsOpen Us :=
    isOpen_lt ((Units.continuous_val.sub continuous_const).norm) continuous_const
  set T : GeneralLinear n E ≃ₜ GeneralLinear n E :=
    (Homeomorph.mulLeft (x * dG)).trans (Homeomorph.mulRight (θ x)⁻¹)
  refine ⟨T '' Us, T.isOpenMap _ hUs, ⟨1, by simp [Us, hs0], by simp [T]; rfl⟩, fun φ hφ => ?_⟩
  -- the data of the abstract mass identity
  set μP := TwistedVanDijk.parabolicHaar B μM μU
  have : μP.IsHaarMeasure := TwistedVanDijk.parabolicHaar_isHaarMeasure B μM μU
  have : μG.IsMulRightInvariant := isMulRightInvariant_generalLinear μG
  have hIw := iwasawa_parabolicHaar B μG μM μU μK hG hM hU
  set S := twistedConjugacySaturation (leviAut σ B).toMonoidHom Ω
  set Q : Set (B.parabolic E) := {p | B.leviProjection E p ∈ S}
  have hSo : IsOpen S := isOpen_twistedConjugacySaturation _ hΩ
  have hQ : MeasurableSet Q :=
    (hSo.preimage (B.leviProjectionContinuous E).continuous).measurableSet
  set θP : B.parabolic E →* B.parabolic E := (parabolicContinuousAut B σ).toMulEquiv.toMonoidHom
  have hθP : ∀ p : B.parabolic E, (θP p : GeneralLinear n E) = θ p := fun p => rfl
  have hθPm : Measurable θP := (parabolicContinuousAut B σ).continuous.measurable
  have hμPθ : μP.map θP = μP := map_parabolicContinuousAut_eq B σ μP
  have hprθ : ∀ h : B.parabolic E, B.leviProjection E (θP h) = leviAut σ B (B.leviProjection E h) :=
    fun h => leviProjection_entrywiseAut σ B h
  have hQinv : ∀ h p, p ∈ Q → h * p * (θP h)⁻¹ ∈ Q := by
    intro h p hp
    change B.leviProjection E (h * p * (θP h)⁻¹) ∈ S
    rw [map_mul, map_mul, map_inv, hprθ]
    exact twistedConj_mem_saturation_of_mem (leviAut σ B).toMonoidHom hp _
  set δh : B.parabolic E → ℝ := fun p => (parabolicHalfModulusNNReal B p : ℝ)
  have hδc : Continuous δh :=
    NNReal.continuous_coe.comp (continuous_parabolicHalfModulusNNReal (E := E) B)
  have hδmul : ∀ a b, δh (a * b) = δh a * δh b := by
    intro a b
    simp only [δh, map_mul, NNReal.coe_mul]
  have hδinv : ∀ h p, δh (h * p * (θP h)⁻¹) = δh p := by
    intro h p
    have hθ : parabolicHalfModulusNNReal B (θP h) = parabolicHalfModulusNNReal B h :=
      parabolicHalfModulusNNReal_aut B σ h
    have hne : parabolicHalfModulusNNReal B h ≠ 0 := ((Group.isUnit h).map _).ne_zero
    simp only [δh, map_mul, map_inv, hθ, NNReal.coe_mul, NNReal.coe_inv]
    field_simp
  -- the level of `φ`
  obtain ⟨L⟩ := TwistedVanDijk.exists_level σ φ
  have hφV : ∀ v ∈ L.K'.toSubgroup, ∀ v' ∈ L.K'.toSubgroup, ∀ g, φ (v * g * v') = φ g := by
    intro v hv v' hv' g
    rw [L.right (v * g) v' hv', L.left v hv g]
  -- additive Haar measures on `𝔭` and `𝔲̄`
  set νS : Measure (parabolicSubalgebra (R := E) B) := Measure.addHaar
  set νL : Measure (lowerLie (E := E) B) := Measure.addHaar
  -- `δ` is trivial on `P ∩ U`
  let HP : Subgroup (B.parabolic E) := U.toSubgroup.comap (B.parabolic E).subtype
  have hHPc : IsCompact (HP : Set (B.parabolic E)) :=
    (B.isClosed_parabolic E).isClosedEmbedding_subtypeVal.isCompact_preimage hUc
  have hδW : ∀ h : B.parabolic E, (h : GeneralLinear n E) ∈ U → δh h = 1 := by
    intro h hh
    have := eq_one_of_mem_compact (parabolicHalfModulusNNReal B)
      (continuous_parabolicHalfModulusNNReal (E := E) B) HP hHPc (k := h) hh
    simp only [δh, this, NNReal.coe_one]
  -- the parabolic point and the chart
  set d' := B.leviInParabolic E d
  have hd'G : (d' : GeneralLinear n E) = dG := rfl
  let A : Matrix (Fin n) (Fin n) E ≃ₜ+ Matrix (Fin n) (Fin n) E :=
    { toAddEquiv := A₀.toLinearEquiv.toAddEquiv
      continuous_toFun := A₀.continuous
      continuous_invFun := A₀.symm.continuous }
  have hAlin : ∀ X, A X = twistedChartLinear B (σ : E →+* E) (d' : GeneralLinear n E).val
      ((d' : GeneralLinear n E)⁻¹).val X := by
    intro X
    change A₀ X = _
    rw [chartLinearEquiv_apply, chartLinear_eq_twistedChartLinear]
    rfl
  have hAsymm : ∀ Y, ‖A.symm Y‖ ≤ C * ‖Y‖ := hC
  set ν := blockSumMeasure B νS νL
  set c : ℝ≥0 := (residueAbsoluteNNReal F (LinearMap.det (chartLinear B σ d)))⁻¹
  have hA : ν.map A = (c : ℝ≥0∞) • ν := by
    have h := map_chartLinearEquiv B σ d hdet ν
    change ν.map A₀ = _
    rw [h]
    rfl
  -- the support hypothesis
  have hsupp : ∀ y : GeneralLinear n E, φ (x * y * (θ x)⁻¹) ≠ 0 →
      ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧
        y.val = (d' : GeneralLinear n E).val * (1 + Y) := by
    intro y hy
    obtain ⟨g, hg, hgy⟩ := hφ hy
    have hyg : y = dG * g := by
      have : x * dG * g * (θ x)⁻¹ = x * y * (θ x)⁻¹ := hgy
      have h2 := congrArg (fun z => x⁻¹ * z * θ x) this
      simpa [mul_assoc] using h2.symm
    have hgs : ‖g.val - 1‖ < s := hg
    refine ⟨g.val - 1, hsA (by rwa [mem_ball, dist_zero_right]), hgs.le.trans hsr, ?_⟩
    rw [hyg, Units.val_mul, add_sub_cancel]
    rfl
  -- rigidity
  have hrig : ∀ (g : GeneralLinear n E) (p h : B.parabolic E), p ∈ Q →
      (h : GeneralLinear n E) ∈ U →
      g * p * (θ g)⁻¹ = d' * h → g ∈ B.parabolic E := by
    intro g p h hp hh heq
    have hhO : (h : GeneralLinear n E) ∈ O := hUO _ hh
    have hhW : h ∈ Wp := by rw [← hOeq]; exact hhO
    have hp' : B.leviProjection E (d' * h) ∈ S := by
      rw [map_mul, B.leviProjection_section E]
      exact subset_twistedConjugacySaturation _ _ hhW
    exact mem_parabolic_of_twistedConj σ l B hE.pow_eq_one Ω hcop hp hp' g heq
  have hdQ : ∀ h : B.parabolic E, (h : GeneralLinear n E) ∈ U → d' * h ∈ Q := by
    intro h hh
    have hhW : h ∈ Wp := by rw [← hOeq]; exact hUO _ hh
    change B.leviProjection E (d' * h) ∈ S
    rw [map_mul, B.leviProjection_section E]
    exact subset_twistedConjugacySaturation _ _ hhW
  have hmass := integral_twistedOrbitalKernel_eq_mass B (σ : E →+* E) hσ θP hθP hθPm μG μP hμPθ
    (TwistedVanDijk.integralGL E n) μK hIw Q hQ hQinv δh hδc hδinv hδmul φ φ.continuous
    φ.hasCompactSupport L.K'.toSubgroup L.K'.isOpen hφV νS νL U hUc hr0 hr1 hUeq hrange hδW d' x
    A hAlin hC0 hAsymm (c : ℝ≥0∞) hA hsmall hsupp hrig hdQ
  rw [hmass]
  congr 1
  have hδd : δh d' = (NNReal.sqrt ((LocalFieldData.ofInstances E).leviModulus B d : ℝ≥0) : ℝ) := by
    simp only [δh, parabolicHalfModulusNNReal, MonoidHom.coe_mk, OneHom.coe_mk, d',
      B.leviProjection_section E]
  rw [hδd, ENNReal.coe_toReal, ← Complex.ofReal_mul, sqrt_leviModulus_mul_inv_det_chartLinear B σ hE d]

end Main

end Langlands.BaseChange.TwistedLocalDescent

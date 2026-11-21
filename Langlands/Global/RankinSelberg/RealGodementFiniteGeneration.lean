import Langlands.Global.RankinSelberg.RealGodementCompactApproximation
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Weierstrass

/-! # Compact Godement generation of real K-finite principal-series vectors -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Filter MeasureTheory Set
open scoped ContDiff Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

variable {m : ℕ}

local notation "M" => Matrix (Fin m) (Fin m) ℝ
local notation "X" => Matrix (Fin m) (Fin (m + 1)) ℝ
local notation "G" => Langlands.GeneralLinear m ℝ
local notation "H" => Langlands.GeneralLinear (m + 1) ℝ
local notation "K" => unitaryCompact ℝ (m + 1)
local notation "ρ" => Whittaker.rightTranslation ℂ H

/-- The complex span of Godement sections formed with smooth tests supported in
compact full-row-rank sets and vectors of the lower position principal series. -/
def compactSectionSpan [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock) :
    Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ {U | ∃ (f : G → ℂ) (S : Set X) (Φ : X → ℂ),
    f ∈ principalSeries ℝ m (realPositionCharacter ds) ∧ IsCompact S ∧
      (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ Φ ∧ (∀ x ∉ S, Φ x = 0) ∧
      U = sectionValue μ c f Φ}

/-- Compact Godement sections whose lower input is K-finite in the position principal series. -/
def compactKFiniteLowerSectionSpan [MeasurableSpace G]
    (μ : Measure G) (c : RealCharacterData) (ds : List RealBlock) : Submodule ℂ (H → ℂ) :=
  Submodule.span ℂ {U | ∃ (f : G → ℂ) (S : Set X) (Φ : X → ℂ),
    f ∈ kFiniteFunctions (principalSeries ℝ m (realPositionCharacter ds)) (unitaryCompact ℝ m) ∧
      IsCompact S ∧ (∀ x ∈ S, HasFullRowRank x) ∧ ContDiff ℝ ∞ Φ ∧
      (∀ x ∉ S, Φ x = 0) ∧ U = sectionValue μ c f Φ}

theorem compactKFiniteLowerSectionSpan_le [MeasurableSpace G]
    (μ : Measure G) (c : RealCharacterData) (ds : List RealBlock) :
    compactKFiniteLowerSectionSpan μ c ds ≤ compactSectionSpan μ c ds := by
  apply Submodule.span_mono
  rintro _ ⟨f, S, Φ, hf, hS, hRank, hΦ, hZero, rfl⟩
  exact ⟨f, S, Φ, hf.1, hS, hRank, hΦ, hZero, rfl⟩

private def compactRestriction : (H → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun F k := F k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Compact Godement sections span a subspace of the smooth upper position principal series. -/
theorem compactSectionSpan_le_principalSeries [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) :
    compactSectionSpan μ c ds ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f, S, Φ, hf, hS, hRank, hΦ, hZero, rfl⟩
  exact realGodementSection m μ c ds f hf S hS hRank Φ hΦ hZero

private theorem gramSection_mem_kFiniteLowerSectionSpan [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock)
    {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {S : Set M} (hS : IsCompact S) (hUnit : ∀ y ∈ S, IsUnit y)
    {β : M → ℝ} (hβ : ContDiff ℝ ∞ β) (hβZero : ∀ y ∉ S, β y = 0)
    (p : Polynomial ℝ) :
    sectionValue μ c (lowerCutoff ds p.eval) (gramTest c F β) ∈ compactKFiniteLowerSectionSpan μ c ds := by
  apply Submodule.subset_span
  exact ⟨lowerCutoff ds p.eval, rowGram ⁻¹' S, gramTest c F β,
    lowerCutoff_polynomial_mem_kFiniteFunctions ds p, isCompact_rowGram_preimage hS,
    fun x hx => hasFullRowRank_of_isUnit_rowGram (hUnit (rowGram x) hx),
    contDiff_gramTest c ds hF hS.isClosed hUnit hβ hβZero,
    fun _ hx => gramTest_eq_zero c F hβZero hx, rfl⟩

private def orbitCoefficient {V : Submodule ℂ (H → ℂ)} (v : K → V) :
    Module.Dual ℂ V →ₗ[ℂ] (K → ℂ) where
  toFun L k := L (v k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def compactKernelFunctional [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] (c : RealCharacterData) (ds : List RealBlock)
    {V : Submodule ℂ (H → ℂ)}
    (hV : V ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (w : G → ℝ) (hw : Continuous w) (hwS : HasCompactSupport w) : Module.Dual ℂ V where
  toFun v := ∫ h : G, (w h : ℂ) * compactKernel ds (v : H → ℂ) h 1 ∂μ
  map_add' v₁ v₂ := by
    rw [← integral_add (integrable_weightedKernel μ c ds (hV v₁.2) 1 hw hwS)
      (integrable_weightedKernel μ c ds (hV v₂.2) 1 hw hwS)]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro h
    simp only [compactKernel, Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' z v := by
    rw [RingHom.id_apply, smul_eq_mul, ← integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro h
    simp only [compactKernel, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    ring

private theorem compactRestriction_gramSection_mem_range
    [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {V : Submodule ℂ (H → ℂ)}
    (hV : V ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (hOrbit : ∀ k : K, ρ k.val F ∈ V) {β : M → ℝ} {b : ℝ → ℝ}
    (hw : Continuous (gramAngularWeight β b))
    (hwS : HasCompactSupport (gramAngularWeight β b)) :
    compactRestriction (sectionValue μ c (lowerCutoff ds b) (gramTest c F β)) ∈
      LinearMap.range (orbitCoefficient (fun k : K => ⟨ρ k.val F, hOrbit k⟩)) := by
  refine ⟨compactKernelFunctional μ c ds hV (gramAngularWeight β b) hw hwS, funext fun k => ?_⟩
  change (∫ h : G, (gramAngularWeight β b h : ℂ) * compactKernel ds (ρ k.val F) h 1 ∂μ) =
    sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k.val
  rw [sectionValue_gramTest_lowerCutoff μ c ds hF β b k.property]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  change (gramAngularWeight β b h : ℂ) *
    (F ((lowerBlock h * 1) * k.val) * lowerCutoff ds (fun _ => 1) h⁻¹ *
      (Real.sqrt |h.val.det| : ℂ)) = _
  simp only [mul_one, compactKernel]

private theorem eq_of_compactRestriction {c : RealCharacterData} {ds : List RealBlock}
    {F U : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (hU : U ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    (heq : compactRestriction U = compactRestriction F) : U = F := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  have hK : U k = F k := congrFun heq (⟨k, hk⟩ : K)
  rw [hU.2 a u k, hF.2 a u k, hK]

private theorem exists_polynomial_tendsto_weightedIntegral {A : Type*} [TopologicalSpace A]
    [T2Space A] [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [IsFiniteMeasureOnCompacts μ]
    {T : Set A} (hT : IsCompact T) {angle : A → ℝ} (hAngle : Continuous angle)
    {b : ℝ → ℝ} (hb : Continuous b) :
    ∃ p : ℕ → Polynomial ℝ, ∀ L : A → ℂ, Continuous L →
      Tendsto (fun j => ∫ h in T, ((p j).eval (angle h) : ℝ) * L h ∂μ) atTop
        (𝓝 (∫ h in T, b (angle h) * L h ∂μ)) := by
  have hImage : IsCompact (angle '' T) := hT.image hAngle
  obtain ⟨l, hl⟩ := hImage.bddBelow
  obtain ⟨r, hr⟩ := hImage.bddAbove
  let ε (j : ℕ) : ℝ := 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hε₁ (j : ℕ) : ε j ≤ 1 := by
    dsimp [ε]
    rw [div_le_one (show 0 < (j : ℝ) + 1 by positivity)]
    exact le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) j)
  choose p hp using fun j : ℕ => exists_polynomial_near_of_continuousOn l r b hb.continuousOn (ε j) (hε j)
  have hErr (j : ℕ) {h : A} (hh : h ∈ T) : |(p j).eval (angle h) - b (angle h)| < ε j :=
    hp j _ ⟨hl ⟨h, hh, rfl⟩, hr ⟨h, hh, rfl⟩⟩
  refine ⟨p, fun L hL => ?_⟩
  let V (b' : ℝ → ℝ) (h : A) := (b' (angle h) : ℂ) * L h
  have hV {b' : ℝ → ℝ} (hb' : Continuous b') : Continuous (V b') :=
    (Complex.continuous_ofReal.comp (hb'.comp hAngle)).mul hL
  let C (h : A) := (|b (angle h)| + 1) * ‖L h‖
  have hC : Integrable C (μ.restrict T) :=
    ((((hb.comp hAngle).abs.add continuous_const).mul hL.norm).continuousOn.integrableOn_compact hT)
  refine tendsto_integral_of_dominated_convergence (μ := μ.restrict T)
    (F := fun j => V (p j).eval) (f := V b) C
    (fun j => (hV (p j).continuous).aestronglyMeasurable) hC ?_ ?_
  · intro j
    rw [ae_restrict_iff' hT.isClosed.measurableSet]
    exact ae_of_all _ fun h hh => by
      have hNorm : |(p j).eval (angle h)| ≤ |b (angle h)| + 1 := by
        have h := abs_add_le ((p j).eval (angle h) - b (angle h)) (b (angle h))
        rw [sub_add_cancel] at h
        exact h.trans ((add_comm _ _).le.trans (add_le_add_right ((hErr j hh).le.trans (hε₁ j)) _))
      change ‖(↑((p j).eval (angle h)) : ℂ) * L h‖ ≤ C h
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hNorm (norm_nonneg _)
  · rw [ae_restrict_iff' hT.isClosed.measurableSet]
    exact ae_of_all _ fun h hh => by
      have hPt : Tendsto (fun j => (p j).eval (angle h)) atTop (𝓝 (b (angle h))) := by
        refine tendsto_iff_dist_tendsto_zero.mpr (tendsto_of_tendsto_of_tendsto_of_le_of_le
          tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat (fun _ => dist_nonneg) ?_)
        intro j
        change dist ((p j).eval (angle h)) (b (angle h)) ≤ ε j
        rw [Real.dist_eq]
        exact (hErr j hh).le
      exact (Complex.continuous_ofReal.continuousAt.tendsto.comp hPt).mul tendsto_const_nhds

/-- Polynomial angular cutoffs approximate a continuous cutoff in every compact
evaluation of the section formed with a fixed Gram test. -/
theorem exists_polynomial_gramSection_tendsto
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {S : Set M} (hS : IsCompact S) (hUnit : ∀ x ∈ S, IsUnit x)
    {β : M → ℝ} (hβ : Continuous β) (hβZero : ∀ x ∉ S, β x = 0)
    {b : ℝ → ℝ} (hb : Continuous b) :
    ∃ p : ℕ → Polynomial ℝ, ∀ k : K,
      Tendsto (fun j => sectionValue μ c (lowerCutoff ds (p j).eval) (gramTest c F β) k.val)
        atTop (𝓝 (sectionValue μ c (lowerCutoff ds b) (gramTest c F β) k.val)) := by
  let T := lowerGram (m := m) ⁻¹' S
  have hT : IsCompact T := isCompact_lowerGram_preimage hS hUnit
  obtain ⟨p, hp⟩ := exists_polynomial_tendsto_weightedIntegral μ hT continuous_lowerAngle hb
  refine ⟨p, ?_⟩
  intro k
  let L (h : G) := (β (lowerGram h) : ℂ) * compactKernel ds F h k.val
  have hPair : Continuous (fun h : G => (h, k.val)) :=
    continuous_id.prodMk continuous_const
  have hKernel := continuous_compactKernel (m := m) ds (F := F) c hF
  have hK := hKernel.comp hPair
  change Continuous (fun h : G => compactKernel ds F h k.val) at hK
  have hβ' : Continuous (fun h : G => (β (lowerGram h) : ℂ)) :=
    Complex.continuous_ofReal.comp (hβ.comp continuous_lowerGram)
  have hL : Continuous L := hβ'.mul hK
  have hEq (b' : ℝ → ℝ) :
      sectionValue μ c (lowerCutoff ds b') (gramTest c F β) k.val =
        ∫ h in T, (b' (lowerAngle h) : ℂ) * L h ∂μ := by
    rw [sectionValue_gramTest_lowerCutoff μ c ds hF β b' k.property]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun h hh =>
      show (b' (lowerAngle h) : ℂ) * L h = 0 by
        simp only [L, hβZero _ hh, Complex.ofReal_zero, zero_mul, mul_zero])]
    apply integral_congr_ae (ae_of_all _ fun h => ?_)
    simp only [L, gramAngularWeight, Complex.ofReal_mul]
    rw [mul_comm (β (lowerGram h) : ℂ) (b' (lowerAngle h) : ℂ), mul_assoc]
  rw [funext (fun j => hEq (p j).eval), hEq b]
  exact hp L hL

private theorem mem_compactKFiniteLowerSectionSpan_of_kFinite
    [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ kFiniteFunctions
      (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) K) :
    F ∈ compactKFiniteLowerSectionSpan μ c ds := by
  classical
  let V : Submodule ℂ (H → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k.val F)
  have : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hF.2
  have hOrbit (k : K) : ρ k.val F ∈ V := Submodule.subset_span ⟨k, rfl⟩
  have hV : V ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_principalSeries _ hF.1 k.val
  let W : Submodule ℂ (K → ℂ) := LinearMap.range (orbitCoefficient (fun k : K => ⟨ρ k.val F, hOrbit k⟩))
  let P : Submodule ℂ (K → ℂ) := (compactKFiniteLowerSectionSpan μ c ds).map compactRestriction
  let E : Submodule ℂ (K → ℂ) := W ⊓ P
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range _
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le (inf_le_left : E ≤ W)
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose S β b hS hUnit hβ hZero hb hError using fun j : ℕ =>
    realGodementCompactApproximation m μ c ds F hF.1 (ε j) (hε j)
  let U : ℕ → H → ℂ := fun j => sectionValue μ c (lowerCutoff ds (b j)) (gramTest c F (β j))
  have hU (j : ℕ) : compactRestriction (U j) ∈ E := by
    obtain ⟨p, hp⟩ := exists_polynomial_gramSection_tendsto μ c ds hF.1 (hS j) (hUnit j)
      (hβ j).continuous (hZero j) (hb j).continuous
    let A (i : ℕ) : H → ℂ := sectionValue μ c (lowerCutoff ds (p i).eval) (gramTest c F (β j))
    have hA (i : ℕ) : compactRestriction (A i) ∈ E := by
      refine ⟨compactRestriction_gramSection_mem_range μ c ds hF.1 hV hOrbit
        (continuous_gramAngularWeight (hβ j).continuous (p i).continuous)
        (hasCompactSupport_gramAngularWeight (p i).eval (hS j) (hUnit j) (hZero j)), ?_⟩
      exact ⟨A i, gramSection_mem_kFiniteLowerSectionSpan μ c ds hF.1 (hS j) (hUnit j)
        (hβ j) (hZero j) (p i), rfl⟩
    have hLim : Tendsto (fun i => compactRestriction (A i)) atTop (𝓝 (compactRestriction (U j))) :=
      tendsto_pi_nhds.mpr hp
    exact E.closed_of_finiteDimensional.mem_of_tendsto hLim (Eventually.of_forall hA)
  have hLim : Tendsto (fun j => compactRestriction (U j)) atTop (𝓝 (compactRestriction F)) := by
    apply tendsto_pi_nhds.mpr
    intro k
    apply tendsto_iff_dist_tendsto_zero.mpr
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun _ => dist_nonneg) (fun j => ?_)
    change dist (U j k.val) (F k.val) ≤ ε j
    rw [dist_eq_norm]
    exact (hError j k.val k.property).le
  have hE : compactRestriction F ∈ E :=
    E.closed_of_finiteDimensional.mem_of_tendsto hLim (Eventually.of_forall hU)
  obtain ⟨f, hf, hEq⟩ := (show compactRestriction F ∈ P from hE.2)
  have hf' := compactSectionSpan_le_principalSeries μ c ds (compactKFiniteLowerSectionSpan_le μ c ds hf)
  have hSame := eq_of_compactRestriction hF.1 hf' hEq
  rwa [← hSame]

/-- Every real upper K-finite position principal-series vector is in the complex
span of Godement sections with compact full-row-rank tests. -/
def RealGodementFiniteGenerationStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ),
    F ∈ kFiniteFunctions (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
      (unitaryCompact ℝ (m + 1)) → F ∈ compactSectionSpan μ c ds

theorem realGodementFiniteGeneration : RealGodementFiniteGenerationStatement := by
  intro m _ _ μ _ _ _ c ds F hF
  exact compactKFiniteLowerSectionSpan_le μ c ds (mem_compactKFiniteLowerSectionSpan_of_kFinite μ c ds hF)

/-- The lower vectors in compact Godement generation may be chosen K-finite in their
position principal series. -/
def RealGodementFiniteGenerationKFiniteLowerStatement : Prop :=
  ∀ (m : ℕ) [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) (F : Langlands.GeneralLinear (m + 1) ℝ → ℂ),
    F ∈ kFiniteFunctions (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
      (unitaryCompact ℝ (m + 1)) → F ∈ compactKFiniteLowerSectionSpan μ c ds

theorem realGodementFiniteGenerationKFiniteLower : RealGodementFiniteGenerationKFiniteLowerStatement := by
  intro m _ _ μ _ _ _ c ds F hF
  exact mem_compactKFiniteLowerSectionSpan_of_kFinite μ c ds hF

end Langlands.Global.RankinSelbergGlobal.RealGodement

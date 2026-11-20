import Langlands.Global.RankinSelberg.RealGodementCompactApproximation
import Mathlib.Topology.Algebra.Module.FiniteDimension

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

private def compactRestriction : (H → ℂ) →ₗ[ℂ] (K → ℂ) where
  toFun F k := F k.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem sectionSpan_le [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    [BorelSpace (Langlands.GeneralLinear m ℝ)] (μ : Measure (Langlands.GeneralLinear m ℝ))
    [IsFiniteMeasureOnCompacts μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) :
    compactSectionSpan μ c ds ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨f, S, Φ, hf, hS, hRank, hΦ, hZero, rfl⟩
  exact realGodementSection m μ c ds f hf S hS hRank Φ hΦ hZero

private theorem gramSection_mem_sectionSpan [MeasurableSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) (c : RealCharacterData) (ds : List RealBlock)
    {F : H → ℂ}
    (hF : F ∈ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)))
    {S : Set M} (hS : IsCompact S) (hUnit : ∀ y ∈ S, IsUnit y)
    {β : M → ℝ} (hβ : ContDiff ℝ ∞ β) (hβZero : ∀ y ∉ S, β y = 0)
    {b : ℝ → ℝ} (hb : ContDiff ℝ ∞ b) :
    sectionValue μ c (lowerCutoff ds b) (gramTest c F β) ∈ compactSectionSpan μ c ds := by
  apply Submodule.subset_span
  exact ⟨lowerCutoff ds b, rowGram ⁻¹' S, gramTest c F β,
    (realGodementLowerCutoff m ds b hb).1, isCompact_rowGram_preimage hS,
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

private theorem mem_compactSectionSpan_of_kFinite
    [MeasurableSpace (Langlands.GeneralLinear m ℝ)] [BorelSpace (Langlands.GeneralLinear m ℝ)]
    (μ : Measure (Langlands.GeneralLinear m ℝ)) [IsFiniteMeasureOnCompacts μ]
    [Measure.IsOpenPosMeasure μ] [Measure.IsMulRightInvariant μ]
    (c : RealCharacterData) (ds : List RealBlock) {F : H → ℂ}
    (hF : F ∈ kFiniteFunctions
      (principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds))) K) :
    F ∈ compactSectionSpan μ c ds := by
  classical
  let V : Submodule ℂ (H → ℂ) := Submodule.span ℂ (Set.range fun k : K => ρ k.val F)
  have : FiniteDimensional ℂ V := (mem_kFiniteVectors_iff _ _ _).mp hF.2
  have hOrbit (k : K) : ρ k.val F ∈ V := Submodule.subset_span ⟨k, rfl⟩
  have hV : V ≤ principalSeries ℝ (m + 1) (realPositionCharacter (.character c :: ds)) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨k, rfl⟩
    exact rightTranslation_mem_principalSeries _ hF.1 k.val
  let W : Submodule ℂ (K → ℂ) := LinearMap.range (orbitCoefficient (fun k : K => ⟨ρ k.val F, hOrbit k⟩))
  let P : Submodule ℂ (K → ℂ) := (compactSectionSpan μ c ds).map compactRestriction
  let E : Submodule ℂ (K → ℂ) := W ⊓ P
  have : FiniteDimensional ℂ W := LinearMap.finiteDimensional_range _
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le (inf_le_left : E ≤ W)
  let ε : ℕ → ℝ := fun j => 1 / ((j : ℝ) + 1)
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  choose S β b hS hUnit hβ hZero hb hError using fun j : ℕ =>
    realGodementCompactApproximation m μ c ds F hF.1 (ε j) (hε j)
  let U : ℕ → H → ℂ := fun j => sectionValue μ c (lowerCutoff ds (b j)) (gramTest c F (β j))
  have hU (j : ℕ) : compactRestriction (U j) ∈ E := by
    refine ⟨compactRestriction_gramSection_mem_range μ c ds hF.1 hV hOrbit
      (continuous_gramAngularWeight (hβ j).continuous (hb j).continuous)
      (hasCompactSupport_gramAngularWeight (b j) (hS j) (hUnit j) (hZero j)), ?_⟩
    exact ⟨U j, gramSection_mem_sectionSpan μ c ds hF.1 (hS j) (hUnit j) (hβ j) (hZero j) (hb j), rfl⟩
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
  have hSame := eq_of_compactRestriction hF.1 (sectionSpan_le μ c ds hf) hEq
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
  exact mem_compactSectionSpan_of_kFinite μ c ds hF

end Langlands.Global.RankinSelbergGlobal.RealGodement

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Basic
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitSectionTopology

/-! # Schwartz synthesis from fixed-level derivative estimates -/

noncomputable section

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

open Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal

namespace Langlands.HarishChandraSchwartz

universe uG uI uV uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  {J : Type uJ} [Fintype J] [DecidableEq J]
  (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (K : OpenSubgroup G) (hP : IsClosed (P : Set G))
  (hK : IsCompact (K : Set G)) (hν : ∀ i, Continuous (ν i))
  (hr : Continuous h.projection)
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))

set_option hygiene false in
local notation "Sections" => OrbitSectionSpace ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "SectionLevel" => OrbitSectionLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "includeLevel" => OrbitSectionSpace.ofLevel ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "inputSeminorms" => OrbitSectionLevel.seminormFamily ν π e h hU K hP hK hν hr hPK
set_option hygiene false in
local notation "DerivativeIndex" => List J × Module.Dual ℂ (ProductInducedCompactPicture h K π.obj)

/-- The compact open subgroup attached to an open subgroup contained in the packet subgroup. -/
def orbitSectionCompactLevel (H : {H : OpenSubgroup G // H ≤ K}) : CompactOpenSubgroup G :=
  ⟨H.1, hK.of_isClosed_subset H.1.isClosed H.2⟩

/-- The analytic estimate needed for synthesis: every output Schwartz seminorm is bounded,
uniformly on one input level, by a finite supremum of input derivative seminorms. -/
def OrbitSectionSchwartzEstimates (Ξ σ : G → ℝ) (T : Sections →ₗ[ℂ] (G → ℂ)) : Prop :=
  ∀ (H : {H : OpenSubgroup G // H ≤ K}) (r : ℝ),
    ∃ t : Finset DerivativeIndex, ∃ C : ℝ≥0, ∀ q : SectionLevel H.1,
      nu Ξ σ r (T (includeLevel H.1 q)) ≤
        ENNReal.ofReal ((C : ℝ) * (t.sup (inputSeminorms H.1)) q)

namespace OrbitSectionSchwartzSynthesis

variable (Ξ σ : G → ℝ) (T : Sections →ₗ[ℂ] (G → ℂ))
  (hfix : ∀ (H : {H : OpenSubgroup G // H ≤ K}) (q : SectionLevel H.1),
    IsBiInvariant H.1 (T (includeLevel H.1 q)))
  (hest : OrbitSectionSchwartzEstimates ν π e h hU K hP hK hν hr hPK Ξ σ T)

include hest in
/-- The finite derivative estimate implies actual finiteness, before taking `ENNReal.toReal`. -/
theorem nu_lt_top (H : {H : OpenSubgroup G // H ≤ K}) (q : SectionLevel H.1) (r : ℝ) :
    nu Ξ σ r (T (includeLevel H.1 q)) < ⊤ := by
  obtain ⟨t, C, hb⟩ := hest H r
  exact (hb q).trans_lt ENNReal.ofReal_lt_top

/-- On a fixed section level, synthesis takes values in the same Schwartz level. -/
def levelLinear (H : {H : OpenSubgroup G // H ≤ K}) :
    SectionLevel H.1 →ₗ[ℂ] Level Ξ σ (orbitSectionCompactLevel K hK H) :=
  LinearMap.codRestrict (levelSubmodule Ξ σ H.1)
    (T ∘ₗ includeLevel H.1) fun q =>
      ⟨hfix H q, fun r => nu_lt_top ν π e h hU K hP hK hν hr hPK Ξ σ T hest H q r⟩

/-- The restricted synthesis has exactly the original pointwise values. -/
@[simp] theorem levelLinear_apply (H : {H : OpenSubgroup G // H ≤ K})
    (q : SectionLevel H.1) (g : G) :
    levelLinear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest H q g =
      T (includeLevel H.1 q) g :=
  rfl

/-- The fixed-level estimate gives continuity between the already published level topologies. -/
theorem continuous_levelLinear (H : {H : OpenSubgroup G // H ≤ K}) :
    Continuous (levelLinear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest H) := by
  refine (OrbitSectionLevel.withSeminorms ν π e h hU K hP hK hν hr hPK H.1).continuous_of_isBounded
    (Level.withSeminorms (orbitSectionCompactLevel K hK H)) _ ?_
  intro r
  obtain ⟨t, C, hb⟩ := hest H r
  refine ⟨t, C, fun q => ?_⟩
  change (nu Ξ σ r (T (includeLevel H.1 q))).toReal ≤
    (C : ℝ) * (t.sup (inputSeminorms H.1)) q
  have hb0 : 0 ≤ (C : ℝ) * (t.sup (inputSeminorms H.1)) q :=
    mul_nonneg C.coe_nonneg (apply_nonneg _ _)
  have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb q)
  simpa only [ENNReal.toReal_ofReal hb0] using hle

include hfix hest in
/-- All smooth sections synthesize to the existing Schwartz submodule. -/
theorem mem_schwartzSubmodule (q : Sections) : T q ∈ schwartzSubmodule Ξ σ := by
  obtain ⟨H, q', rfl⟩ := OrbitSectionSpace.exists_ofLevel ν π e h hU K hP hK hν hr hPK q
  exact levelSubmodule_le_schwartzSubmodule Ξ σ (orbitSectionCompactLevel K hK H)
    ((levelLinear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest H q').property)

/-- Algebraic synthesis into `Space`, obtained by restricting the original function-valued map. -/
def linear : Sections →ₗ[ℂ] Space Ξ σ :=
  LinearMap.codRestrict (schwartzSubmodule Ξ σ) T
    (mem_schwartzSubmodule ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest)

/-- Continuous synthesis, conditional on the actual fixed-level derivative estimates. -/
def continuousLinear : Sections →L[ℂ] Space Ξ σ :=
  OrbitSectionSpace.mkCLM ν π e h hU K hP hK hν hr hPK
    (linear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest) fun H => by
      have hc := (Space.continuous_ofLevel (Ξ := Ξ) (σ := σ) (orbitSectionCompactLevel K hK H)).comp
        (continuous_levelLinear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest H)
      exact hc

/-- Continuous synthesis retains the original function-valued map pointwise. -/
@[simp] theorem continuousLinear_apply (q : Sections) (g : G) :
    continuousLinear ν π e h hU K hP hK hν hr hPK Ξ σ T hfix hest q g = T q g :=
  rfl

end OrbitSectionSchwartzSynthesis

end Langlands.HarishChandraSchwartz

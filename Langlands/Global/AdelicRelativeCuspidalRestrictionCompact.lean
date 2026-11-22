import Langlands.Global.AdelicRelativeCuspidalRapidDecay
import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Langlands.Analysis.HilbertSchmidtCompactProof

/-! # Compact restriction of a relatively cuspidal family to a boundary region -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v w

open AlgebraicGeometry CategoryTheory Filter MeasureTheory NumberField Set Topology
open scoped Classical CategoryTheory.MonObj Manifold ContDiff ENNReal NNReal

namespace Langlands.Global

open Langlands.Analysis.OperatorIdeals Langlands.GroupScheme AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Geometry.Manifold RepresentationGrowth
  AdelicSiegelFactors PositiveRealTorus Langlands.LinearAlgebra.RationalSpan

/-- A square-integrable scalar bound on evaluation norms supplies the continuous
linear map into L² as well as the Hilbert–Schmidt estimate. -/
private theorem exists_compactL2_of_evaluation_majorant
    {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {X : Type w} [MeasurableSpace X] {μX : Measure X}
    (ev : X → E →L[ℂ] ℂ) (g : X → ℝ) (hg : MemLp g 2 μX)
    (hMeas : ∀ q : E, AEStronglyMeasurable (fun x => ev x q) μX)
    (hBound : ∀ᵐ x ∂μX, ‖ev x‖ ≤ ‖g x‖) :
    ∃ T : E →L[ℂ] Lp ℂ 2 μX, IsHilbertSchmidt T ∧ IsCompactOperator T ∧
      ∀ q : E, (T q : X → ℂ) =ᵐ[μX] fun x => ev x q := by
  have hpoint (q : E) : ∀ᵐ x ∂μX, ‖ev x q‖ ≤ ‖(‖q‖ • g) x‖ := by
    filter_upwards [hBound] with x hx
    change ‖ev x q‖ ≤ ‖‖q‖ * g x‖
    rw [norm_mul, norm_norm, mul_comm]
    exact (ContinuousLinearMap.le_opNorm (ev x) q).trans
      (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have hm (q : E) : MemLp (fun x => ev x q) 2 μX :=
    (hg.const_smul ‖q‖).of_le (hMeas q) (hpoint q)
  let t (q : E) := (hm q).toLp (fun x => ev x q)
  have ht (q : E) : (t q : X → ℂ) =ᵐ[μX] fun x => ev x q := (hm q).coeFn_toLp
  let A : E →ₗ[ℂ] Lp ℂ 2 μX :=
    { toFun := t
      map_add' := by
        intro q r
        apply Lp.ext
        filter_upwards [ht (q + r), ht q, ht r, Lp.coeFn_add (t q) (t r)] with x hqr hq hr hadd
        rw [hqr, hadd, Pi.add_apply, hq, hr, map_add]
      map_smul' := by
        intro c q
        apply Lp.ext
        filter_upwards [ht (c • q), ht q, Lp.coeFn_smul c (t q)] with x hc hq hsmul
        rw [RingHom.id_apply, hc, hsmul, Pi.smul_apply, hq, map_smul] }
  let T := A.mkContinuous (eLpNorm g 2 μX).toReal (fun q => by
    change ‖t q‖ ≤ _
    rw [Lp.norm_toLp]
    have hnorm := eLpNorm_mono_ae (p := 2) (hMeas q) (hpoint q)
    rw [eLpNorm_const_smul] at hnorm
    calc
      _ ≤ (‖(‖q‖ : ℝ)‖ₑ * eLpNorm g 2 μX).toReal :=
        ENNReal.toReal_mono (ENNReal.mul_ne_top enorm_ne_top hg.eLpNorm_ne_top) hnorm
      _ = _ := by rw [ENNReal.toReal_mul]; simp [mul_comm])
  have hsq : ∀ᵐ x ∂μX, ‖ev x‖ ^ 2 ≤ ‖g x‖ ^ 2 :=
    hBound.mono fun _ hx => pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hgInt := (memLp_two_iff_integrable_sq_norm hg.aestronglyMeasurable).mp hg
  have hHS : IsHilbertSchmidt T :=
    (hilbertSchmidtDominatedEvaluation.{v, w, v} E X μX T ev _ hgInt ht hsq).1
  exact ⟨T, hHS, hilbertSchmidtCompact E (Lp ℂ 2 μX) T hHS, ht⟩

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)
  {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (rT : T₀ ⟶ 𝓕.T)
  {d N : ℕ} (hG : SmoothOfRelativeDimension d G.X.hom) (rho : MatrixRepresentation G (Fin N))

local notation "A" => AdelicGroupPoints F G
local notation "G∞" => InfiniteAdelicGroupPoints F G
local notation "Gf" => FiniteAdelicGroupPoints F G
local notation "W" => smoothModel F d
local notation "IG" => 𝓘(ℝ, W)
local notation "IC" => 𝓘(ℝ, ℂ)
local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν
local notation "Δ" => simpleRelativeRoots 𝓕.i 𝓕.ν
local notation "B₀" => (Subtype.mk ∅ (empty_subset Δ) : Idx)
local notation "aG" => positiveMap F G 𝓕.T 𝓕.i T₀ rT
local notation "height" => adelicHeight F G rho

/-- Relatively cuspidal families of uniform directional growth give a compact
Hilbert–Schmidt restriction whenever the boundary has the indicated chamber
representatives and a square-integrable inverse height power. -/
def AdelicRelativeCuspidalRestrictionCompactStatement : Prop :=
  IsSplitTorus T₀.toGrp → 0 < N →
  letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  letI := smoothChartedSpace F G hG
  ∀ (P : Idx) (Zχ : Set (characterLattice T₀)),
    ratSpan (((fun α : characterLattice 𝓕.T => rT ≫ α) '' Δ) ∪ Zχ) = ⊤ →
  ∀ (b : ℝ≥0ˣ) (B : ℝ), 0 ≤ B →
  ∀ (Ω K : Set A), IsCompact Ω → IsCompact K →
    Ω ⊆ ((map F (𝓕.P B₀) G (𝓕.p B₀)).toMonoidHom.range : Set A) →
  ∀ (Yf : Set Gf), IsCompact Yf → ∀ (L : Subgroup Gf), IsOpen (L : Set Gf) →
  ∀ (E : Type v) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (ev : A → E →L[ℂ] ℂ),
  (∀ q, Continuous (fun x => ev x q)) →
  (∀ q (c : Gf), ContMDiff IG IC ∞ (fun y : G∞ => ev (pair F G y c) q)) →
  (∀ q, ∀ r ∈ rationalImage F (𝓕.p B₀), ∀ x, ev (r * x) q = ev x q) →
  (∀ q (z : AdelicGroupPoints F (𝓕.U P)), ∀ x,
    ev (map F (𝓕.U P) G (𝓕.iU P ≫ 𝓕.p P) z * x) q = ev x q) →
  (∀ q, ∀ l ∈ L, ∀ x, ev (x * ofFinite F G l) q = ev x q) →
  (∀ q, 𝓕.IsCuspidalAlong P (fun x => ev x q)) →
  ∀ R : ℝ, 0 ≤ R →
  (∀ s : List W, ∃ C : ℝ, 0 ≤ C ∧
    ∀ q x, ‖adelicIteratedDirectionalValue hG s (fun y => ev y q) x‖ ≤ C * height x ^ R * ‖q‖) →
  ∀ (X : Type w) [MeasurableSpace X] (μX : Measure X) (rep : X → A) (m : ℕ),
  (∀ q, AEStronglyMeasurable (fun x => ev (rep x) q) μX) →
  (∀ᵐ x ∂μX, ∃ p ∈ Ω,
    ∃ a ∈ weakSimpleRootChamber F T₀ 𝓕.T rT G 𝓕.i 𝓕.ν b,
      (∀ χ ∈ Zχ, |logNormHom F T₀ a.val χ| ≤ B) ∧
      (∀ α ∈ Δ \ P.val, |logNormHom F T₀ a.val (rT ≫ α)| ≤ B) ∧
      ∃ k ∈ K, rep x = p * aG a * k ∧ finite F G (rep x) ∈ Yf) →
  MemLp (fun x => (height (rep x) ^ m)⁻¹) 2 μX →
  ∃ T : E →L[ℂ] Lp ℂ 2 μX, IsHilbertSchmidt T ∧ IsCompactOperator T ∧
    ∀ q, (T q : X → ℂ) =ᵐ[μX] fun x => ev (rep x) q

theorem adelicRelativeCuspidalRestrictionCompact :
    AdelicRelativeCuspidalRestrictionCompactStatement.{u, v, w} 𝓕 rT hG rho := by
  intro hT hN
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  intro P Zχ hSpan b B hB Ω K hΩ hK hΩP Yf hYf L hL E _ _ _ ev hf hfS hfR hfU hfL
    hCusp R hR hGrow X _ μX rep m hMeas hRep hInt
  obtain ⟨C, hC, hDecay⟩ := 𝓕.adelicRelativeCuspidalRapidDecay rT hG rho hT hN P Zχ hSpan
    b B hB Ω K hΩ hK hΩP Yf hYf L hL E (fun q x => ev x q) norm (fun q => norm_nonneg q)
    hf hfS hfR hfU hfL hCusp R hR hGrow m
  refine exists_compactL2_of_evaluation_majorant (fun x => ev (rep x))
    (C • fun x => (height (rep x) ^ m)⁻¹) (hInt.const_smul C) hMeas ?_
  filter_upwards [hRep] with x hx
  obtain ⟨p, hp, a, ha, hz, hOutside, k, hk, hEq, hfin⟩ := hx
  have hPos : 0 < height (rep x) ^ m :=
    pow_pos (zero_lt_one.trans_le (one_le_adelicHeight F G rho hN _)) _
  have hC' := mul_nonneg hC (inv_nonneg.mpr hPos.le)
  have hNorm : ‖ev (rep x)‖ ≤ C * (height (rep x) ^ m)⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound _ hC'
    intro q
    have hd := hDecay q p hp a ha hz hOutside k hk (hEq ▸ hfin)
    rw [← hEq] at hd
    calc
      ‖ev (rep x) q‖ ≤ (C * ‖q‖) / (height (rep x) ^ m) := (le_div_iff₀ hPos).mpr hd
      _ = (C * (height (rep x) ^ m)⁻¹) * ‖q‖ := by rw [div_eq_mul_inv, mul_right_comm]
  change ‖ev (rep x)‖ ≤ ‖C * (height (rep x) ^ m)⁻¹‖
  simpa only [Real.norm_of_nonneg hC'] using hNorm

end StandardParabolicFamily
end Langlands.Global

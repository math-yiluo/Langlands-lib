import Langlands.Global.AdelicSliceGrowthEnveloping
import Langlands.Global.AdelicIntertwiningSmoothSlicesReductionStatement
import Langlands.Global.AdelicIntertwiningIntegrability
import Langlands.Global.AdelicEisensteinGlobalMajorant
import Langlands.Global.AdelicEisensteinUnfoldingGlobalMajorant
import Langlands.Global.AdelicSmoothIwasawaHeight
import Langlands.Geometry.Manifold.SmoothGroupParametricIntegral

/-! # Smooth infinite slices of intertwining integrals from uniform growth

`intertwiningSmoothSlicesReduction` proves `IntertwiningSmoothSlicesReductionStatement`: it
derives `IntertwiningSmoothSlicesStatement` from `AutomorphicFunctionUniformGrowthStatement`,
using the Library's smoothness of the Iwasawa height pairings `adelicSmoothIwasawaHeight`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter Set
open scoped CategoryTheory.MonObj Manifold ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints Langlands.Geometry.Manifold RepresentationGrowth

section Envelope

variable {F : Type u} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  (Γ : Subgroup (AdelicGroupPoints F G)) (H : AdelicGroupPoints F G → ℝ) (e : ℝ)

/-- The infimum of `H ^ e` over a left orbit of `Γ`. -/
private def leftEnvelope (y : AdelicGroupPoints F G) : ℝ :=
  ⨅ t : Γ, H (t.val * y) ^ e

variable {Γ H e}

private theorem leftEnvelope_nonneg (hH : ∀ g, 0 ≤ H g) (y : AdelicGroupPoints F G) :
    0 ≤ leftEnvelope Γ H e y :=
  le_ciInf fun _ => Real.rpow_nonneg (hH _) _

private theorem leftEnvelope_le (hH : ∀ g, 0 ≤ H g) (y : AdelicGroupPoints F G) :
    leftEnvelope Γ H e y ≤ H y ^ e := by
  have hb : BddBelow (Set.range fun t : Γ => H (t.val * y) ^ e) :=
    ⟨0, by rintro _ ⟨t, rfl⟩; exact Real.rpow_nonneg (hH _) _⟩
  show (⨅ t : Γ, H (t.val * y) ^ e) ≤ _
  simpa only [Subgroup.coe_one, one_mul] using ciInf_le hb (1 : Γ)

private theorem leftEnvelope_mul {x : AdelicGroupPoints F G} (hx : x ∈ Γ)
    (y : AdelicGroupPoints F G) : leftEnvelope Γ H e (x * y) = leftEnvelope Γ H e y := by
  unfold leftEnvelope
  have h : (fun t : Γ => H (t.val * (x * y)) ^ e) =
      (fun t : Γ => H (t.val * y) ^ e) ∘ (Equiv.mulRight (⟨x, hx⟩ : Γ)) := by
    funext t
    simp only [Function.comp_apply, Equiv.coe_mulRight, Subgroup.coe_mul, mul_assoc]
  rw [h]
  exact (Equiv.mulRight (⟨x, hx⟩ : Γ)).surjective.iInf_comp (fun t : Γ => H (t.val * y) ^ e)

private theorem norm_le_mul_leftEnvelope {ψ : AdelicGroupPoints F G → ℂ}
    (hinv : IsLeftInvariantUnder F G Γ ψ) {C : ℝ} (hC : 0 < C)
    (hψ : ∀ y, ‖ψ y‖ ≤ C * H y ^ e) (y : AdelicGroupPoints F G) :
    ‖ψ y‖ ≤ C * leftEnvelope Γ H e y := by
  have h : ‖ψ y‖ / C ≤ leftEnvelope Γ H e y := le_ciInf fun t => by
    rw [div_le_iff₀ hC, ← hinv t.val t.property y, mul_comm]
    exact hψ _
  rw [div_le_iff₀ hC] at h
  linarith

end Envelope

set_option maxHeartbeats 1600000 in
/-- Smooth infinite slices of regular intertwining integrals (Mœglin–Waldspurger II.1.6 (i)),
from uniformly moderate growth of automorphic functions on parabolic quotients. -/
theorem intertwiningSmoothSlices_of_uniformGrowth
    (h2 : AutomorphicFunctionUniformGrowthStatement.{u}) :
    IntertwiningSmoothSlicesStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hmul hl'π hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · refine ⟨0, fun lam _ b => ?_⟩
    let : IsClosedImmersion rho.hom.hom.left := hrho
    have : Mono rho.hom.hom := Over.mono_of_mono_left _
    have hsub : Subsingleton (InfiniteAdelicGroupPoints F G) := by
      constructor
      intro x y
      apply MatrixRepresentation.pointMatrix_injective rho
      apply Units.ext
      ext i j
      exact Fin.elim0 i
    apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
    have hconst : functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b =
        fun _ => functionInfiniteSlice F G (hK.intertwiningOperator hK' iU l iV c π' w φ lam) b 1 :=
      funext fun x => congrArg _ (Subsingleton.elim x 1)
    rw [hconst]
    exact contMDiff_const
  -- Smooth heights, maximal compact factors and uniform growth.
  have hH := adelicSmoothIwasawaHeight F G P p K hK hsmooth hKmax
  have hH' := adelicSmoothIwasawaHeight F G Q q K hK' hsmooth hKmax
  have hInf : ∀ k ∈ K, ofInfinite F G (infinite F G k) ∈ K :=
    fun k hk => ((hKmax.mem_iff k).mp hk).1
  let Γ := parabolicQuotientSubgroup F p iU l
  have hgrowth := h2 F G Γ (K.comap (ofInfinite F G).toMonoidHom) rho hsmooth hcalc hG hrho
    hKmax.isMaximalCompact_comap_ofInfinite hN φ hφ
  obtain ⟨e, he, hφc⟩ := exists_hasUniformSliceGrowth hsmooth rho hN hcalc Γ _ hφ hgrowth
  let H := adelicHeight F G rho
  have hH1 (g : AdelicGroupPoints F G) : 1 ≤ H g := one_le_adelicHeight F G rho hN g
  have hH0 (g : AdelicGroupPoints F G) : 0 ≤ H g := zero_le_one.trans (hH1 g)
  -- The envelope of `H ^ e` over left `Γ`-orbits.
  let E' : AdelicGroupPoints F G → ℂ := fun y => (leftEnvelope Γ H e y : ℂ)
  have hE'norm (y : AdelicGroupPoints F G) : ‖E' y‖ = leftEnvelope Γ H e y :=
    Complex.norm_of_nonneg (leftEnvelope_nonneg hH0 y)
  have hE'inv : IsLeftInvariantUnder F G Γ E' := fun x hx y => by
    simp only [E', leftEnvelope_mul hx y]
  have hE'growth : HasModerateGrowthFunction F G rho E' := by
    let scale : ℝ := (N : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
    have hscale : 0 < scale := pow_pos (Nat.cast_pos.mpr hN) _
    refine ⟨scale ^ e, Real.rpow_pos_of_pos hscale _, e, fun y => ?_⟩
    rw [hE'norm]
    refine (leftEnvelope_le hH0 y).trans_eq ?_
    change adelicHeight F G rho y ^ e = _
    rw [adelicHeight_eq_scalar_mul_sourceNorm F G rho y,
      Real.mul_rpow hscale.le (adelicSourceNorm_pos F G rho hN y).le]
  -- The regularity threshold of the Eisenstein majorant of the envelope.
  obtain ⟨R, hR⟩ := eisensteinGlobalMajorant F G P M U A p iU l a r hA hT hG hU hK rho hN hrho
    E' hE'inv hE'growth
  refine ⟨R, fun lam hlam b => ?_⟩
  obtain ⟨bE, dE, hbE, hbE0, hdE, hbound⟩ := hR lam hlam
  let j := iV ≫ q
  let W := innerAdelicPoint F G w
  let Λ := intertwiningRationalSubgroup F p iU j W
  have hΛ := isDiscrete_intertwiningRationalSubgroup F p iU j W
  have hcls : ∀ δ δ' : AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j),
      intertwiningRationalCoset F p w δ = intertwiningRationalCoset F p w δ' →
      (δ' : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) *
        (δ : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))⁻¹ ∈ Λ := by
    intro δ δ' h
    have hrel := QuotientGroup.rightRel_apply.mp (Quotient.exact h)
    rw [parabolicRationalSubgroup, Subgroup.mem_subgroupOf] at hrel
    obtain ⟨z, -, hz⟩ := hrel
    exact mul_inv_mem_intertwiningRationalSubgroup r w hG hU hq hV hmul hw δ.2 δ'.2 ⟨z, hz⟩
  obtain ⟨B, hBint, hB0, hBbound⟩ := exists_integrable_unfolding_majorant hK j w rho hN
    hV.1.smooth hV.1.connectedSpace hV.1.isUnipotent Λ hΛ hcls r.isCompatible.levi hU E'
    hE'inv lam bE hbE hbE0 dE hdE hbound
  -- The twisted derivatives of `φ` along lists of directions.
  let ψ : List (smoothModel F d) → AdelicGroupPoints F G → ℂ :=
    fun ws => ws.foldl (fun χ X => hK.parameterDirectionalSection hsmooth lam X χ) φ
  have hψapp (ws : List (smoothModel F d)) (X : smoothModel F d) :
      ψ (ws ++ [X]) = hK.parameterDirectionalSection hsmooth lam X (ψ ws) := by
    simp only [ψ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  have hψc (ws : List (smoothModel F d)) : HasUniformSliceGrowth hsmooth Γ H e (ψ ws) := by
    induction ws using List.reverseRecOn with
    | nil => exact hφc
    | append_singleton ws X ih =>
      rw [hψapp]
      exact hK.hasUniformSliceGrowth_parameterDirectionalSection hsmooth hH hInf
        (parabolicQuotientSubgroup_le_range iU l) lam X ih
  -- The integrands on the quotient as functions of the infinite variable.
  let meas := intertwiningMeasure F p iU j W
  let out (x : LeftCosetSpace Λ) : AdelicGroupPoints F G :=
    ((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :
      AdelicGroupPoints F G)
  let f : List (smoothModel F d) → LeftCosetSpace Λ → InfiniteAdelicGroupPoints F G → ℂ :=
    fun ws x z => hK.parameterTwist (ψ ws) lam (W⁻¹ * out x * pair F G z b)
  have hleft (y : AdelicGroupPoints F G) (z : InfiniteAdelicGroupPoints F G) :
      y * pair F G z b = pair F G (infinite F G y * z) (finite F G y * b) := by
    rw [← pair_projections F G y, pair_mul]
    simp only [infinite_pair, finite_pair]
  have hf (ws : List (smoothModel F d)) (x : LeftCosetSpace Λ) :
      f ws x = fun z => hK.parameterTwist (ψ ws) lam
        (pair F G (infinite F G (W⁻¹ * out x) * z) (finite F G (W⁻¹ * out x) * b)) := by
    funext z
    exact congrArg (hK.parameterTwist (ψ ws) lam) (hleft (W⁻¹ * out x) z)
  have hs (ws : List (smoothModel F d)) (x : LeftCosetSpace Λ) :
      ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (f ws x) := by
    rw [hf]
    exact (hK.contMDiff_parameterTwist_slice hsmooth hH (ψ ws) lam (hψc ws).1
      (finite F G (W⁻¹ * out x) * b)).comp (contMDiff_const.mul contMDiff_id)
  have hder (ws : List (smoothModel F d)) (x : LeftCosetSpace Λ) (X : smoothModel F d) :
      groupDirectionalValue 𝓘(ℝ, smoothModel F d) X (f ws x) = f (ws ++ [X]) x := by
    rw [hf, hf, hψapp]
    funext z
    exact (groupDirectionalValue_leftTranslation 𝓘(ℝ, smoothModel F d) X
      (infinite F G (W⁻¹ * out x))
      (fun z => hK.parameterTwist (ψ ws) lam (pair F G z (finite F G (W⁻¹ * out x) * b))) z).trans
      (hK.parameterTwist_directionalSection hsmooth lam X (ψ ws) _ _).symm
  -- Measurability, by induction on the list of directions.
  have hclosed := AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let : LocallyCompactSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.locallyCompactSpace
  let : PolishSpace (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) :=
    hclosed.polishSpace
  let : BorelSpace (LeftCosetSpace Λ) := LeftCosetSpace.discreteQuotientBorelSpace Λ hΛ
  have hinvU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) φ :=
    fun x hx g => hφ.1 x (Subgroup.mem_sup_left hx) g
  have hmeas (ws : List (smoothModel F d)) (z : InfiniteAdelicGroupPoints F G) :
      AEStronglyMeasurable (fun x => f ws x z) meas := by
    induction ws using List.reverseRecOn generalizing z with
    | nil =>
      exact (hK.continuous_intertwiningIntegrand iU j w hU.1.isUnipotent hinvU hφ.2.1.1 lam
        (pair F G z b)).aestronglyMeasurable
    | append_singleton ws X ih =>
      have h := aestronglyMeasurable_groupDirectionalValue (u := f ws) (hs ws) ih X z
      simpa only [hder] using h
  -- Domination, locally uniformly in the infinite variable.
  have hψbound (ws : List (smoothModel F d)) : ∃ C : ℝ, 0 < C ∧
      ∀ y, ‖ψ ws y‖ ≤ C * leftEnvelope Γ H e y := by
    obtain ⟨C, hC⟩ := (hψc ws).2.2 []
    have hC1 : 0 < max C 1 := zero_lt_one.trans_le (le_max_right _ _)
    refine ⟨max C 1, hC1, fun y => norm_le_mul_leftEnvelope (hψc ws).2.1 hC1 (fun y => ?_) y⟩
    have h := hC (finite F G y) (infinite F G y)
    change ‖ψ ws (pair F G (infinite F G y) (finite F G y))‖ ≤
      C * H (pair F G (infinite F G y) (finite F G y)) ^ e at h
    rw [pair_projections] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left C 1) (Real.rpow_nonneg (hH0 _) _))
  have hpairc : Continuous fun z : InfiniteAdelicGroupPoints F G => pair F G z b := by
    have hprod : Continuous (fun a : InfiniteAdelicGroupPoints F G => (a, b)) :=
      Continuous.prodMk_left b
    change Continuous ((fun p : InfiniteAdelicGroupPoints F G × FiniteAdelicGroupPoints F G =>
      pair F G p.1 p.2) ∘ fun a => (a, b))
    exact (continuous_pair F G).comp hprod
  have hcontH : Continuous fun z : InfiniteAdelicGroupPoints F G => H (pair F G z b) :=
    (continuous_adelicHeight F G rho hN).comp hpairc
  have hdom (ws : List (smoothModel F d)) (z₀ : InfiniteAdelicGroupPoints F G) :
      ∃ Us ∈ 𝓝 z₀, ∃ bound : LeftCosetSpace Λ → ℝ, Integrable bound meas ∧
        ∀ x, ∀ z ∈ Us, ‖f ws x z‖ ≤ bound x := by
    obtain ⟨C, hC, hCb⟩ := hψbound ws
    let Mb := H (pair F G z₀ b) + 1
    refine ⟨{z | H (pair F G z b) < Mb},
      (isOpen_lt hcontH continuous_const).mem_nhds
        (show H (pair F G z₀ b) < Mb from lt_add_one _),
      fun x => C * Mb ^ dE * B x, hBint.const_mul (C * Mb ^ dE), fun x z hz => ?_⟩
    have hy : ‖E' (W⁻¹ * out x * pair F G z b)‖ *
        ‖hK.heightPower lam (W⁻¹ * out x * pair F G z b)‖ ≤ B x * H (pair F G z b) ^ dE := by
      simpa only [IsIwasawaCompact.parameterTwist, norm_mul] using hBbound x (pair F G z b)
    rw [hE'norm] at hy
    have hz' : H (pair F G z b) ^ dE ≤ Mb ^ dE :=
      Real.rpow_le_rpow (hH0 _) (le_of_lt hz) hdE
    change ‖hK.parameterTwist (ψ ws) lam (W⁻¹ * out x * pair F G z b)‖ ≤ _
    rw [IsIwasawaCompact.parameterTwist, norm_mul]
    calc ‖ψ ws (W⁻¹ * out x * pair F G z b)‖ *
          ‖hK.heightPower lam (W⁻¹ * out x * pair F G z b)‖ ≤
        (C * leftEnvelope Γ H e (W⁻¹ * out x * pair F G z b)) *
          ‖hK.heightPower lam (W⁻¹ * out x * pair F G z b)‖ :=
          mul_le_mul_of_nonneg_right (hCb _) (norm_nonneg _)
      _ = C * (leftEnvelope Γ H e (W⁻¹ * out x * pair F G z b) *
          ‖hK.heightPower lam (W⁻¹ * out x * pair F G z b)‖) := by ring
      _ ≤ C * (B x * H (pair F G z b) ^ dE) := mul_le_mul_of_nonneg_left hy hC.le
      _ ≤ C * (B x * Mb ^ dE) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hz' (hB0 x)) hC.le
      _ = C * Mb ^ dE * B x := by ring
  -- Differentiation under the integral sign and the height factor of the operator.
  obtain ⟨hsm, -⟩ := contMDiff_integral_of_dominated_invariantDerivatives
    (fun (X : smoothModel F d) ws => ws ++ [X]) hs hder hmeas hdom
  have hint : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun z => hK.intertwiningIntegral iU j w φ lam (pair F G z b)) := hsm []
  have hpow : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun z => hK'.heightPower (-weylParameter l c π' lam) (pair F G z b)) :=
    (Complex.contDiff_exp (𝕜 := ℝ) (n := ∞)).contMDiff.comp
      (hH' (-weylParameter l c π' lam) b)
  apply (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr
  exact contMDiff_mul_complex hpow hint

/-- The implication `IntertwiningSmoothSlicesReductionStatement`. -/
theorem intertwiningSmoothSlicesReduction : IntertwiningSmoothSlicesReductionStatement.{u} :=
  fun h2 => intertwiningSmoothSlices_of_uniformGrowth h2

end Langlands.Global

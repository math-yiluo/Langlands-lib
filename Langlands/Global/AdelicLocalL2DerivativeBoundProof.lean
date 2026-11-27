import Langlands.Global.AdelicLocalL2DerivativeBoundStatement
import Langlands.Automorphic.GroupSchemeInvariantFormsComparison
import Langlands.Automorphic.GroupSchemeAdaptedCasimirProof
import Langlands.Automorphic.GroupSchemeAutomorphicUniformGrowthReductionProof
import Langlands.Geometry.Manifold.LieGroupEllipticDerivativeL2
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.InfiniteAdelicModularCharacter

/-! # Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ContDiff ENNReal Manifold NNReal Pointwise

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Geometry.Manifold Langlands.Analysis AdelicGroupPoints

section Slices

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)

/-- Iterated archimedean right-orbit derivatives of a function on `G(𝔸)`, evaluated along the
archimedean slice `t ↦ g · t`, are the iterated left-invariant derivatives of that slice. -/
theorem adelicIteratedDirectionalValue_mul_ofInfinite
    (D : List (InfiniteAdelicGroupPoints.smoothModel F d)) (Φ : AdelicGroupPoints F G → ℂ)
    (g : AdelicGroupPoints F G) (t : InfiniteAdelicGroupPoints F G) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    letI := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
    adelicIteratedDirectionalValue hsmooth D Φ (g * ofInfinite F G t) =
      D.foldr (groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d))
        (fun x => Φ (g * ofInfinite F G x)) t := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  let := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  induction D generalizing t with
  | nil => rfl
  | cons X s ih =>
    have hfun : (fun h : InfiniteAdelicGroupPoints F G =>
        adelicIteratedDirectionalValue hsmooth s Φ (g * ofInfinite F G t * ofInfinite F G h)) =
        fun h => s.foldr (groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d))
          (fun x => Φ (g * ofInfinite F G x)) (t * h) := by
      funext h
      rw [← ih (t * h), map_mul, mul_assoc]
    rw [adelicIteratedDirectionalValue_cons, List.foldr_cons]
    change mvfderiv 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
        (fun h => adelicIteratedDirectionalValue hsmooth s Φ (g * ofInfinite F G t *
          ofInfinite F G h)) 1 X = mvfderiv 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d)
        (fun h => s.foldr (groupDirectionalValue 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d))
          (fun x => Φ (g * ofInfinite F G x)) (t * h)) 1 X
    rw [hfun]

end Slices

section Haar

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

/-- The `L²` mass of a right `L`-invariant continuous function on a compact piece of an
archimedean slice through `g` is controlled by its mass on a fixed compact subset of `g · G(𝔸)`. -/
theorem exists_lintegral_infiniteSlice_le (L : Subgroup (FiniteAdelicGroupPoints F G))
    (hLo : IsOpen (L : Set (FiniteAdelicGroupPoints F G)))
    {V : Set (InfiniteAdelicGroupPoints F G)} (hV : IsCompact V) :
    ∃ (S : Set (AdelicGroupPoints F G)) (c : ℝ≥0), IsCompact S ∧
      ∀ φ : AdelicGroupPoints F G → ℂ, Continuous φ →
        (∀ l ∈ L, ∀ g : AdelicGroupPoints F G, φ (g * ofFinite F G l) = φ g) →
        ∀ g : AdelicGroupPoints F G,
          ∫⁻ x in V, ‖φ (g * ofInfinite F G x)‖ₑ ^ 2
              ∂(Measure.haar : Measure (InfiniteAdelicGroupPoints F G)) ≤
            (c : ℝ≥0∞) * ∫⁻ s in S, ‖φ (g * s)‖ₑ ^ 2
              ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
  classical
  let : MeasurableSpace (FiniteAdelicGroupPoints F G) := borel _
  have : BorelSpace (FiniteAdelicGroupPoints F G) := ⟨rfl⟩
  let U := L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup
  have hUo : IsOpen (U : Set (FiniteAdelicGroupPoints F G)) :=
    hLo.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hUclosed := U.isClosed_of_isOpen hUo
  have hUc : IsCompact (U : Set (FiniteAdelicGroupPoints F G)) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      hUclosed inter_subset_right
  let μInf : Measure (InfiniteAdelicGroupPoints F G) := Measure.haar
  let μf : Measure (FiniteAdelicGroupPoints F G) := Measure.haar
  let haarAd : Measure (AdelicGroupPoints F G) := Measure.haar
  have hUpos : μf (U : Set (FiniteAdelicGroupPoints F G)) ≠ 0 :=
    (hUo.measure_pos μf ⟨1, U.one_mem⟩).ne'
  have hUfin : μf (U : Set (FiniteAdelicGroupPoints F G)) ≠ ⊤ := hUc.measure_lt_top.ne
  let e := split F G
  let ν := (μInf.prod μf).map e.symm
  have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map _
  let c₀ := Measure.haarScalarFactor ν haarAd
  have hν : ν = (c₀ : ℝ≥0∞) • haarAd := Measure.isMulLeftInvariant_eq_smul ν haarAd
  let S := e ⁻¹' (V ×ˢ (U : Set (FiniteAdelicGroupPoints F G)))
  have hSc : IsCompact S := e.toHomeomorph.isCompact_preimage.mpr (hV.prod hUc)
  have hSm : MeasurableSet S := hSc.isClosed.measurableSet
  let K : ℝ≥0∞ := (μf (U : Set (FiniteAdelicGroupPoints F G)))⁻¹ * c₀
  have hK : K ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hUpos) ENNReal.coe_ne_top
  refine ⟨S, K.toNNReal, hSc, fun φ hφ hL g => ?_⟩
  rw [ENNReal.coe_toNNReal hK]
  let h : AdelicGroupPoints F G → ℝ≥0∞ := fun s => ‖φ (g * s)‖ₑ ^ 2
  have hhm : Measurable h :=
    ((hφ.comp (continuous_const.mul continuous_id)).measurable.enorm).pow_const 2
  have hpair (a : InfiniteAdelicGroupPoints F G) (b : FiniteAdelicGroupPoints F G)
      (hb : b ∈ U) : h (e.symm (a, b)) = ‖φ (g * ofInfinite F G a)‖ₑ ^ 2 := by
    have he : e.symm (a, b) = ofInfinite F G a * ofFinite F G b := by
      simp [e, pair, ← map_mul]
    change ‖φ (g * e.symm (a, b))‖ₑ ^ 2 = _
    rw [he, ← mul_assoc, hL b hb.1]
  -- the mass on `S` for the product measure
  have hprod : ∫⁻ s in S, h s ∂ν =
      (∫⁻ x in V, ‖φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf) *
        μf (U : Set (FiniteAdelicGroupPoints F G)) := by
    have hVU : MeasurableSet (V ×ˢ (U : Set (FiniteAdelicGroupPoints F G))) :=
      hV.measurableSet.prod hUo.measurableSet
    calc ∫⁻ s in S, h s ∂ν
        = ∫⁻ s, S.indicator h s ∂ν := (lintegral_indicator hSm _).symm
      _ = ∫⁻ p, S.indicator h (e.symm p) ∂(μInf.prod μf) := by
          change ∫⁻ s, S.indicator h s
              ∂((μInf.prod μf).map e.symm.toHomeomorph.toMeasurableEquiv) = _
          rw [lintegral_map_equiv]
          rfl
      _ = ∫⁻ p, (V ×ˢ (U : Set (FiniteAdelicGroupPoints F G))).indicator
            (fun p => h (e.symm p)) p ∂(μInf.prod μf) := by
          congr 1
          funext p
          by_cases hp : p ∈ V ×ˢ (U : Set (FiniteAdelicGroupPoints F G))
          · have hp' : e.symm p ∈ S := by
              change e (e.symm p) ∈ V ×ˢ (U : Set (FiniteAdelicGroupPoints F G))
              rwa [e.apply_symm_apply]
            rw [indicator_of_mem hp', indicator_of_mem hp]
          · have hp' : e.symm p ∉ S := by
              change e (e.symm p) ∉ V ×ˢ (U : Set (FiniteAdelicGroupPoints F G))
              rwa [e.apply_symm_apply]
            rw [indicator_of_notMem hp', indicator_of_notMem hp]
      _ = ∫⁻ p in V ×ˢ (U : Set (FiniteAdelicGroupPoints F G)), h (e.symm p)
            ∂(μInf.prod μf) := lintegral_indicator hVU _
      _ = ∫⁻ p, h (e.symm p) ∂((μInf.restrict V).prod
            (μf.restrict (U : Set (FiniteAdelicGroupPoints F G)))) := by
          rw [Measure.prod_restrict]
      _ = ∫⁻ a, ∫⁻ b, h (e.symm (a, b))
            ∂(μf.restrict (U : Set (FiniteAdelicGroupPoints F G))) ∂(μInf.restrict V) :=
          lintegral_prod _ (hhm.comp e.symm.continuous.measurable).aemeasurable
      _ = ∫⁻ a in V, ‖φ (g * ofInfinite F G a)‖ₑ ^ 2 *
            μf (U : Set (FiniteAdelicGroupPoints F G)) ∂μInf := by
          refine lintegral_congr fun a => ?_
          rw [setLIntegral_congr_fun hUo.measurableSet (fun b hb => hpair a b hb),
            setLIntegral_const]
      _ = _ := lintegral_mul_const' _ _ hUfin
  have hhaar : ∫⁻ s in S, h s ∂ν = (c₀ : ℝ≥0∞) * ∫⁻ s in S, h s ∂haarAd := by
    rw [hν, Measure.restrict_smul, lintegral_smul_measure, smul_eq_mul]
  have hmain : (∫⁻ x in V, ‖φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf) *
      μf (U : Set (FiniteAdelicGroupPoints F G)) = (c₀ : ℝ≥0∞) * ∫⁻ s in S, h s ∂haarAd := by
    rw [← hprod, hhaar]
  calc ∫⁻ x in V, ‖φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf
      = (∫⁻ x in V, ‖φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf) *
          μf (U : Set (FiniteAdelicGroupPoints F G)) *
            (μf (U : Set (FiniteAdelicGroupPoints F G)))⁻¹ := by
        rw [mul_assoc, ENNReal.mul_inv_cancel hUpos hUfin, mul_one]
    _ = K * ∫⁻ s in S, h s ∂haarAd := by
        rw [hmain]
        simp only [K]
        ring
    _ ≤ K * ∫⁻ s in S, ‖φ (g * s)‖ₑ ^ 2 ∂haarAd := le_rfl

end Haar

/-- **Local `L²` bounds for the archimedean derivatives of `K_∞`- and `𝔷`-finite functions.**
A polynomial in Harish-Chandra's elliptic element annihilates every archimedean slice, the interior
elliptic estimate bounds every word derivative at the identity of a solution by its local `L²`
norm, and the finite level converts the archimedean integral into an adelic one. -/
theorem adelicLocalL2DerivativeBound : AdelicLocalL2DerivativeBoundStatement := by
  intro F _ _ G _ _ _ hG K d hsmooth hcalc hK Φ hΓ hΦ hKfin hZfin D
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  let : LieGroup 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (InfiniteAdelicGroupPoints F G) := InfiniteAdelicGroupPoints.smoothLieGroup F G hsmooth
  let Kinf := K.comap (ofInfinite F G).toMonoidHom
  let f := ofRationalSmoothFunction F G Φ hΓ hΦ
  have hk : IsAdelicInfiniteFinite F G Kinf f :=
    (isInfiniteSubgroupFiniteFunction_evaluate_iff F G Kinf f).mp hKfin
  have hz : IsAdelicCenterFinite F G hsmooth hcalc f :=
    (isCenterFiniteFunction_evaluate_iff F G hsmooth hcalc f).mp hZfin
  obtain ⟨n, r, X, Ptop, Plow, _, hr, htop, hlow, hsym, hsol⟩ :=
    exists_elliptic_slice_annihilator adelicAdaptedCasimir F G Kinf hsmooth hcalc hG
      hK.isMaximalCompact_comap_ofInfinite f hk hz
  let μInf : Measure (InfiniteAdelicGroupPoints F G) := Measure.haar
  obtain ⟨V, C, hV, hC, hest⟩ := exists_lieWord_derivative_l2_evaluation μInf hr X Ptop Plow
    htop hlow hsym (fun i : Fin D.length => D.get i) (List.finRange D.length)
  obtain ⟨L, hLo, hL⟩ := hΦ.2.2
  obtain ⟨S, c, hSc, hlift⟩ := exists_lintegral_infiniteSlice_le F G L hLo hV
  refine ⟨S, C.toNNReal ^ 2 * c, hSc, fun g => ?_⟩
  -- the pointwise bound along the archimedean slice through `g`
  have hpt : ‖adelicIteratedDirectionalValue hsmooth D Φ g‖ₑ ≤
      C * eLpNorm (fun x => Φ (g * ofInfinite F G x)) 2 (μInf.restrict V) := by
    let a := infinite F G g
    let b := finite F G g
    let ψ := (finitePlotSmoothSlice F G b f).val
    have hψ : ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞ ψ :=
      (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth ψ).mp
        (finitePlotSmoothSlice F G b f).property
    have he : (fun x => ψ (a * x)) = fun x => Φ (g * ofInfinite F G x) := by
      funext x
      change Φ (pair F G (a * x) b) = _
      conv_rhs => rw [← pair_projections F G g, ofInfinite_eq_pair, AdelicGroupPoints.pair_mul,
        mul_one]
    have hu : ContMDiff 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) 𝓘(ℝ, ℂ) ∞
        (fun x => Φ (g * ofInfinite F G x)) := by
      rw [← he]
      exact hψ.comp (contMDiff_const.mul contMDiff_id)
    have husol : ∀ x, lieWordAction X (Ptop + Plow) (fun x => Φ (g * ofInfinite F G x)) x = 0 := by
      intro x
      rw [← he, lieWordAction_leftTranslation]
      exact hsol b (a * x)
    have h1 := hest _ hu husol
    rw [← foldr_groupDirectionalValue_eq_lieWordDerivative] at h1
    have h2 := adelicIteratedDirectionalValue_mul_ofInfinite hsmooth D Φ g 1
    rw [map_one, mul_one] at h2
    rw [h2]
    exact h1
  -- square, and pass to the adelic integral
  have hsq : eLpNorm (fun x => Φ (g * ofInfinite F G x)) 2 (μInf.restrict V) ^ 2 =
      ∫⁻ x in V, ‖Φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf := by
    have h : eLpNorm (fun x => Φ (g * ofInfinite F G x)) ((2 : ℝ≥0) : ℝ≥0∞)
        (μInf.restrict V) ^ ((2 : ℝ≥0) : ℝ) =
        ∫⁻ x in V, ‖Φ (g * ofInfinite F G x)‖ₑ ^ ((2 : ℝ≥0) : ℝ) ∂μInf :=
      eLpNorm_nnreal_pow_eq_lintegral two_ne_zero
        (hΦ.1.comp (continuous_const.mul (ofInfinite F G).continuous)).aestronglyMeasurable
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using h
  calc ‖adelicIteratedDirectionalValue hsmooth D Φ g‖ₑ ^ 2
      ≤ (C * eLpNorm (fun x => Φ (g * ofInfinite F G x)) 2 (μInf.restrict V)) ^ 2 :=
        pow_le_pow_left₀ zero_le hpt 2
    _ = C ^ 2 * ∫⁻ x in V, ‖Φ (g * ofInfinite F G x)‖ₑ ^ 2 ∂μInf := by rw [mul_pow, hsq]
    _ ≤ C ^ 2 * ((c : ℝ≥0∞) * ∫⁻ s in S, ‖Φ (g * s)‖ₑ ^ 2
          ∂(Measure.haar : Measure (AdelicGroupPoints F G))) :=
        mul_le_mul_right (hlift Φ hΦ.1 hL g) _
    _ = ((C.toNNReal ^ 2 * c : ℝ≥0) : ℝ≥0∞) * ∫⁻ s in S, ‖Φ (g * s)‖ₑ ^ 2
          ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
        rw [ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_toNNReal hC, mul_assoc]

end Langlands.Global

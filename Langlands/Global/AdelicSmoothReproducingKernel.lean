import Langlands.Global.AdelicLocalFinitenessStatement
import Langlands.Global.AdelicMaximalCompactFactors
import Langlands.Global.InfiniteAdelicModularCharacter
import Langlands.Global.InfiniteAdelicLinearRealization
import Langlands.Global.AdelicHaarUnimodularityProof
import Langlands.Representation.Unitary.CentralQuotientForm
import Langlands.Automorphic.GroupSchemeInvariantFunctionGrowth
import Langlands.Geometry.Manifold.EllipticLineDerivativeBounds
import Langlands.Analysis.SmoothKernelFromLocalFunctionals

/-! # A smooth compactly supported reproducing kernel on reductive adelic groups

`exists_adelicTestFunction_rightConvolution_eq` constructs an adelic test function `α` with
`φ(g) = ∫ α(a) φ(g a) da` for a smooth, `K_∞`-finite and `𝔷`-finite function `φ` on `G(𝔸)`.
The construction combines smooth reproduction at the archimedean places (Harish-Chandra
1966, §8, Theorem 1) with the idempotent of a compact open subgroup at the finite places. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped Classical CategoryTheory.MonObj ContDiff ENNReal Manifold NNReal Pointwise
  Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Geometry.Manifold Langlands.Analysis.CompactFunctional

section Construction

variable (F : Type) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "AInf" => InfiniteAdelicGroupPoints F G
local notation "Af" => FiniteAdelicGroupPoints F G
local notation "A" => AdelicGroupPoints F G

/-- The product decomposition transfers right invariance of the adelic Haar measure to its
archimedean factor. -/
theorem infiniteHaar_isMulRightInvariant (hG : IsConnectedReductive G) :
    (Measure.haar : Measure AInf).IsMulRightInvariant := by
  let haarAd : Measure A := Measure.haar
  have : haarAd.IsMulRightInvariant := adelicHaarUnimodularity.2 F G hG
  have hmod (a : AInf) : Measure.modularCharacter a = 1 := by
    rw [← Langlands.ProductMeasure.modularCharacter_prod_one (H := Af),
      ← show (split F G) (ofInfinite F G a) = (a, 1) by simp,
      Langlands.Aubert.General.modularCharacter_continuousMulEquiv]
    apply NNReal.coe_injective
    change (Measure.modularCharacterFun (ofInfinite F G a) : ℝ) = 1
    obtain ⟨test, ht⟩ := exists_continuous_nonneg_pos (1 : A)
    rw [Measure.modularCharacterFun_eq_haarScalarFactor haarAd,
      Measure.haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos _ _ ht,
      map_mul_right_eq_self,
      ← Measure.haarScalarFactor_eq_integral_div_of_continuous_nonneg_pos haarAd haarAd ht,
      Measure.haarScalarFactor_self, NNReal.coe_one]
  exact Langlands.Haar.isMulRightInvariant_of_modularCharacter_eq_one hmod _

/-- A smooth compactly supported archimedean reproducer and a common open finite level give an
adelic test function reproducing the function for the Haar measure of `G(𝔸)`. -/
theorem exists_adelicTestFunction_of_infiniteReproducer {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (φ : A → ℂ) (hφ : Continuous φ)
    (L : Subgroup Af) (hLo : IsOpen (L : Set Af))
    (hL : ∀ l ∈ L, ∀ g : A, φ (g * ofFinite F G l) = φ g)
    (κ : AInf → ℂ) (hκp : κ ∈ InfinitePlotSmoothFunctions F G) (hκc : HasCompactSupport κ)
    (hrep : ∀ g : A, φ g = ∫ a, φ (g * ofInfinite F G a) * κ a ∂(Measure.haar : Measure AInf)) :
    ∃ α : A → ℂ, IsAdelicTestFunction F G α ∧ rightConvolution F G α φ = φ := by
  classical
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  have hκs := (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth κ).mp hκp
  have hκ := hκs.continuous
  let : MeasurableSpace Af := borel Af
  have : BorelSpace Af := ⟨rfl⟩
  let U := L ⊓ (FiniteAdelicGroupPoints.compactOpenSubgroup F G).toSubgroup
  have hUo : IsOpen (U : Set Af) :=
    hLo.inter (FiniteAdelicGroupPoints.compactOpenSubgroup F G).isOpen
  have hUclosed := U.isClosed_of_isOpen hUo
  have hUc : IsCompact (U : Set Af) :=
    (FiniteAdelicGroupPoints.isCompact_compactOpenSubgroup F G).of_isClosed_subset
      hUclosed inter_subset_right
  let μInf : Measure AInf := Measure.haar
  let μf : Measure Af := Measure.haar
  let haarAd : Measure A := Measure.haar
  let t := (μf (U : Set Af)).toReal
  have ht : 0 < t := ENNReal.toReal_pos
    (hUo.measure_pos μf ⟨1, U.one_mem⟩).ne' hUc.measure_lt_top.ne
  let χ := (U : Set Af).indicator (fun _ => ((t⁻¹ : ℝ) : ℂ))
  have hχ : Continuous χ := IsClopen.continuous_indicator ⟨hUclosed, hUo⟩ continuous_const
  have hχ0 {b : Af} (hb : b ∉ U) : χ b = 0 := indicator_of_notMem hb _
  have hχint : ∫ b, χ b ∂μf = 1 := by
    rw [integral_indicator_const _ hUo.measurableSet, measureReal_def]
    change t • ((t⁻¹ : ℝ) : ℂ) = 1
    rw [Complex.real_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ ht.ne', Complex.ofReal_one]
  let e := split F G
  let B (p : AInf × Af) := κ p.1 * χ p.2
  have hBc : Continuous B := (hκ.comp continuous_fst).mul (hχ.comp continuous_snd)
  have hBs : HasCompactSupport B := by
    apply HasCompactSupport.of_support_subset_isCompact (hκc.prod hUc)
    intro p hp
    refine ⟨subset_tsupport κ ?_, ?_⟩
    · exact fun h => hp (mul_eq_zero_of_left h _)
    · by_contra h
      exact hp (by simp [B, hχ0 h])
  let ν := (μInf.prod μf).map e.symm
  have : ν.IsHaarMeasure := e.symm.isHaarMeasure_map _
  let c := Measure.haarScalarFactor ν haarAd
  have hν : ν = (c : ℝ≥0∞) • haarAd := Measure.isMulLeftInvariant_eq_smul ν haarAd
  let K₀ := B ∘ e
  have hK₀c : Continuous K₀ := hBc.comp e.continuous
  have hK₀s : HasCompactSupport K₀ := hBs.comp_homeomorph e.toHomeomorph
  let α (a : A) := (c : ℂ) * K₀ a
  have hχ_mul (l : Af) (hl : l ∈ U) (b : Af) : χ (b * l) = χ b := by
    have hm : b * l ∈ U ↔ b ∈ U := by
      constructor
      · intro hb
        simpa only [mul_inv_cancel_right] using U.mul_mem hb (U.inv_mem hl)
      · intro hb
        exact U.mul_mem hb hl
    unfold χ
    by_cases hb : b ∈ U
    · rw [indicator_of_mem (hm.mpr hb), indicator_of_mem hb]
    · rw [indicator_of_notMem (hm.not.mpr hb), indicator_of_notMem hb]
  have hχ_mul' (l : Af) (hl : l ∈ U) (b : Af) : χ (l * b) = χ b := by
    have hm : l * b ∈ U ↔ b ∈ U := by
      constructor
      · intro hb
        simpa only [inv_mul_cancel_left] using U.mul_mem (U.inv_mem hl) hb
      · intro hb
        exact U.mul_mem hl hb
    unfold χ
    by_cases hb : b ∈ U
    · rw [indicator_of_mem (hm.mpr hb), indicator_of_mem hb]
    · rw [indicator_of_notMem (hm.not.mpr hb), indicator_of_notMem hb]
  have hα : IsAdelicTestFunction F G α := by
    refine ⟨⟨continuous_const.mul hK₀c, ?_, U, hUo, ?_⟩,
      hK₀s.mul_left, U, hUo, ?_⟩
    · intro b
      apply (InfiniteAdelicGroupPoints.isPlotSmooth_iff_contMDiff F G hsmooth _).2
      have hb (a : AInf) : functionInfiniteSlice F G α b a = (c : ℂ) * (κ a * χ b) := by
        change (c : ℂ) * B (e (e.symm (a, b))) = _
        rw [e.apply_symm_apply]
      let M : ℂ →L[ℝ] ℂ := (ContinuousLinearMap.mul ℝ ℂ (c : ℂ)).comp
        ((ContinuousLinearMap.mul ℝ ℂ).flip (χ b))
      exact (M.contDiff.contMDiff.comp hκs).congr hb
    · intro l hl g
      change (c : ℂ) * B (e (g * ofFinite F G l)) = (c : ℂ) * B (e g)
      rw [map_mul, show e (ofFinite F G l) = (1, l) from by simp [e]]
      simp only [B, Prod.fst_mul, Prod.snd_mul, mul_one, hχ_mul l hl]
    · intro l hl g
      change (c : ℂ) * B (e (ofFinite F G l * g)) = (c : ℂ) * B (e g)
      rw [map_mul, show e (ofFinite F G l) = (1, l) from by simp [e]]
      simp only [B, Prod.fst_mul, Prod.snd_mul, one_mul, hχ_mul' l hl]
  refine ⟨α, hα, funext fun g => ?_⟩
  symm
  rw [rightConvolution]
  simp_rw [mul_comm (α _)]
  let integrand (p : AInf × Af) := φ (g * e.symm p) * B p
  have hIntc : Continuous integrand :=
    (hφ.comp (continuous_const.mul e.symm.continuous)).mul hBc
  have hInt : Integrable integrand (μInf.prod μf) :=
    hIntc.integrable_of_hasCompactSupport hBs.mul_left
  have hfib (a : AInf) (b : Af) :
      integrand (a, b) = (φ (g * ofInfinite F G a) * κ a) * χ b := by
    by_cases hb : b ∈ U
    · have hpair : e.symm (a, b) = ofInfinite F G a * ofFinite F G b := by
        simp [e, pair, ← map_mul]
      change φ (g * e.symm (a, b)) * (κ a * χ b) = _
      rw [hpair, ← mul_assoc g, hL b hb.1, mul_assoc]
    · simp [integrand, B, hχ0 hb]
  have hProd : (∫ p, integrand p ∂(μInf.prod μf)) = φ g := by
    rw [integral_prod _ hInt, hrep g]
    apply integral_congr_ae (ae_of_all _ fun a => ?_)
    simp only [hfib, integral_const_mul, hχint, mul_one]
  calc
    φ g = ∫ p, integrand p ∂(μInf.prod μf) := hProd.symm
    _ = ∫ a, φ (g * a) * K₀ a ∂ν := by
      change _ = ∫ a, φ (g * a) * K₀ a
        ∂((μInf.prod μf).map e.symm.toHomeomorph.toMeasurableEquiv)
      rw [integral_map_equiv]
      apply integral_congr_ae (ae_of_all _ fun p => ?_)
      change φ (g * e.symm p) * B p = φ (g * e.symm p) * B (e (e.symm p))
      rw [e.apply_symm_apply]
    _ = ∫ a, φ (g * a) * ((c : ℂ) * K₀ a) ∂haarAd := by
      rw [hν, integral_smul_measure]
      change (c : ℝ) • (∫ a, φ (g * a) * K₀ a ∂haarAd) = _
      rw [Complex.real_smul, ← integral_const_mul]
      apply integral_congr_ae (ae_of_all _ fun a => ?_)
      change (c : ℂ) * (φ (g * a) * K₀ a) = _
      ring

open InfiniteAdelicGroupPoints in
/-- A function on `G(𝔸)` with smooth infinite slices that is `K_∞`-finite and `𝔷`-finite is
reproduced, on every infinite slice and at every adelic point, by one smooth compactly supported
kernel on the archimedean points. -/
theorem exists_smoothInfiniteReproducer (hG : IsConnectedReductive G)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (K : Subgroup AInf) (hK : CompactIwasawa.IsMaximalCompact K)
    (φ : A → ℂ) (hs : ∀ b, functionInfiniteSlice F G φ b ∈ InfinitePlotSmoothFunctions F G)
    (hfK : IsInfiniteSubgroupFiniteFunction F G K φ)
    (hfZ : IsCenterFiniteFunction F G hsmooth
      (adelicDifferentialCommutator_of_smooth F G hsmooth) φ) :
    ∃ κ : AInf → ℂ, κ ∈ InfinitePlotSmoothFunctions F G ∧ HasCompactSupport κ ∧
      ∀ g : A, φ g = ∫ a, φ (g * ofInfinite F G a) * κ a ∂(Measure.haar : Measure AInf) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hsmooth
  let := smoothLieGroup F G hsmooth
  let I := 𝓘(ℝ, smoothModel F d)
  let hcalc := adelicDifferentialCommutator_of_smooth F G hsmooth
  let measure : Measure AInf := Measure.haar
  let : measure.IsMulRightInvariant := infiniteHaar_isMulRightInvariant F G hG
  obtain ⟨n, r, X, Ptop, Plow, _, hr, htop, hlow, hsym, hsol⟩ :=
    exists_elliptic_functionInfiniteSlices F G hsmooth hcalc hG K hK φ hs hfK hfZ
  let T := plotSmoothEnvelopingAction F G hsmooth hcalc (wordHom F G hsmooth X (Ptop + Plow))
  let C : InfinitePlotSmoothFunctions F G →ₗ[ℂ] C(AInf, ℂ) :=
    { toFun := fun f => ⟨f.val,
        ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp f.property).continuous⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let S := (LinearMap.ker T).map C
  have hS (f : C(AInf, ℂ)) : f ∈ S ↔ ContMDiff I 𝓘(ℝ, ℂ) ∞ f ∧
      ∀ x, lieWordAction X (Ptop + Plow) f x = 0 := by
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨(isPlotSmooth_iff_contMDiff F G hsmooth _).mp u.property, fun x => ?_⟩
      change lieWordAction X (Ptop + Plow) u.val x = 0
      rw [← plotSmoothEnvelopingAction_wordHom F G hsmooth hcalc, show T u = 0 from hu]
      rfl
    · rintro ⟨hf, he⟩
      let u : InfinitePlotSmoothFunctions F G :=
        ⟨f, (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr hf⟩
      refine ⟨u, LinearMap.mem_ker.mpr (Subtype.ext ?_), rfl⟩
      change (plotSmoothEnvelopingAction F G hsmooth hcalc
        (wordHom F G hsmooth X (Ptop + Plow)) u).val = 0
      rw [plotSmoothEnvelopingAction_wordHom]
      exact funext he
  have hshift (a : AInf) (f : C(AInf, ℂ)) (hf : f ∈ S) : shift a f ∈ S := by
    obtain ⟨hsmoothf, he⟩ := (hS f).mp hf
    refine (hS (shift a f)).mpr ⟨hsmoothf.comp (contMDiff_const.mul contMDiff_id), fun x => ?_⟩
    change lieWordAction X (Ptop + Plow) (fun y => f (a * y)) x = 0
    rw [lieWordAction_leftTranslation]
    exact he (a * x)
  obtain ⟨κ, hκ, hκc, hκrep⟩ := exists_smoothCompact_reproducer measure
    (isClosedLinearRealization_matrixRealization_of_smooth F G hsmooth rho hρ)
    S (fun f hf => ((hS f).mp hf).1) hshift (fun B q hq h0 ha ε _ =>
      lineDerivativeBounds_of_wordEquation hr X Ptop Plow htop hlow hsym S (fun f => (hS f).mp)
        hshift B q hq h0 ha ε)
  refine ⟨κ, (isPlotSmooth_iff_contMDiff F G hsmooth _).mpr hκ, hκc, fun g => ?_⟩
  let a := infinite F G g
  let b := finite F G g
  let f : C(AInf, ℂ) := ⟨functionInfiniteSlice F G φ b,
    ((isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hs b)).continuous⟩
  have hf : f ∈ S := (hS f).mpr ⟨(isPlotSmooth_iff_contMDiff F G hsmooth _).mp (hs b), hsol b⟩
  have he (x : AInf) : (shift a f) x = φ (g * ofInfinite F G x) := by
    change φ (pair F G (a * x) b) = _
    conv_rhs => rw [← pair_projections F G g, ofInfinite_eq_pair, pair_mul, mul_one]
  have hone : shift a f 1 = φ g := by simpa only [map_one, mul_one] using he 1
  simpa only [hone, he, mul_comm (κ _)] using hκrep (shift a f) (hshift a f hf)

end Construction

/-- **A smooth reproducing kernel for functions finite under the centre and the compact subgroup** (Harish-Chandra
1966, §8, Theorem 1, at the archimedean places, with the idempotent of a compact open subgroup at
the finite places). Let `G` be a connected reductive group over a number field `F`, `K` a maximal
compact subgroup of `G(𝔸)` with archimedean part `K_∞`, and `rho` a closed matrix embedding. A
smooth function `φ` on `G(𝔸)` (`IsAdelicSmoothFunction`) that is `K_∞`-finite and `𝔷`-finite
satisfies `rightConvolution F G α φ = φ`, that is `φ(g) = ∫ α(a) φ(g a) da` for every `g`, for an
adelic test function `α` (`IsAdelicTestFunction`), which is smooth, compactly supported and
bi-invariant under an open subgroup of `G(𝔸_f)`. -/
theorem exists_adelicTestFunction_rightConvolution_eq
    {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsMaximalCompactSubgroup F G K)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hρ : IsClosedSubgroup rho)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
    (φ : AdelicGroupPoints F G → ℂ) (hφ : IsAdelicSmoothFunction F G φ)
    (hfK : IsInfiniteSubgroupFiniteFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ)
    (hfZ : IsCenterFiniteFunction F G hsmooth hcalc φ) :
    ∃ α : AdelicGroupPoints F G → ℂ, IsAdelicTestFunction F G α ∧
      rightConvolution F G α φ = φ := by
  obtain ⟨hc, hs, L, hLo, hL⟩ := hφ
  obtain ⟨κ, hκ, hκc, hrep⟩ := exists_smoothInfiniteReproducer F G hG rho hρ hsmooth
    (K.comap (ofInfinite F G).toMonoidHom) hK.isMaximalCompact_comap_ofInfinite φ hs hfK hfZ
  exact exists_adelicTestFunction_of_infiniteReproducer F G hsmooth φ hc L hLo hL κ hκ hκc hrep

end Langlands.Global

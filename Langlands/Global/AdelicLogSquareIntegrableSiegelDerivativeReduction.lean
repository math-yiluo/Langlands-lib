import Langlands.Global.AdelicLogSquareIntegrableSiegelDerivativeBounds
import Langlands.Global.AdelicLocalL2DerivativeBoundStatement
import Langlands.Global.AdelicSiegelRationalConjugateCountingStatement
import Langlands.Global.LeftCosetSupportMeasure

/-! # Reduction of the logarithmic Siegel bounds to a local `L²` bound and a Siegel count

`logSquareIntegrableSiegelDerivativeBounds_of_reduction` derives
`LogSquareIntegrableSiegelDerivativeBoundsStatement` (Delorme 2023, Proposition 3.5) from
`AdelicLocalL2DerivativeBoundStatement` (local `L²` control of every derivative of a `K_∞`- and
`𝔷`-finite function) and `SiegelRationalConjugateCountingStatement` (the number of rational points
in `x E x⁻¹` is `≪ δ_{P₀}(a)` at the Siegel points `x` with torus coordinate `a`). The proof folds
the local `L²` integral of `Φ` onto `[G]`, bounds the multiplicity of the folding by the count, and
bounds the weight on the translated compact set by a power of the logarithmic height of the point.
The folding step is that of the proof of Mœglin–Waldspurger I.2.5 (b) and of Bernstein's Key Lemma
as Delorme applies it in the proof of Proposition 3.5. Bernstein and Delorme fold the local
integral of a sum of squares of derivatives and use the weighted square-integrability of every
derivative; the local bound of every derivative by `Φ` itself, a consequence of Harish-Chandra's
smooth kernel, lets this proof fold the local `L²` integral of `Φ` and use only the weighted
square-integrability of `Φ`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj ENNReal NNReal Pointwise

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  InfiniteAdelicGroupPoints AdelicSiegelFactors

section Height

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]

/-- Right translation by the points of a compact set multiplies the logarithmic height
`σ(x) = 1 + log max(1, ‖x‖)` by at most a fixed factor: `σ(x s) ≤ L σ(x)`. -/
theorem exists_adelicLogHeight_mul_le {N : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hrho : IsClosedSubgroup rho) {S : Set (AdelicGroupPoints F G)} (hS : IsCompact S) :
    ∃ L : ℝ, 1 ≤ L ∧ ∀ x : AdelicGroupPoints F G, ∀ s ∈ S,
      adelicLogHeight F G rho (x * s) ≤ L * adelicLogHeight F G rho x := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · -- A closed embedding into `GL_0` makes `G(𝔸)` trivial.
    subst hN
    have hsub : Subsingleton (AdelicGroupPoints F G) :=
      ⟨fun _ _ => (RepresentationGrowth.isClosedEmbedding_adelicMatrix F G rho hrho).injective
        (Units.ext (Matrix.ext fun i => Fin.elim0 i))⟩
    refine ⟨1, le_rfl, fun x s _ => ?_⟩
    rw [Subsingleton.elim (x * s) x, one_mul]
  · obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
      (RepresentationGrowth.continuous_adelicHeight F G rho hN).continuousOn
    set M' : ℝ := max 1 M with hM'
    have hM'1 : 1 ≤ M' := le_max_left _ _
    have hlogM := Real.log_nonneg hM'1
    refine ⟨1 + Real.log M', by linarith, fun x s hs => ?_⟩
    set c₀ : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult) with hc₀def
    have hc₀ : 0 < c₀ := pow_pos (by exact_mod_cast hN) _
    have hHs : RepresentationGrowth.adelicHeight F G rho s ≤ M' :=
      (le_abs_self _).trans ((hM s hs).trans (le_max_right _ _))
    have hx0 := (RepresentationGrowth.adelicSourceNorm_pos F G rho hN x).le
    have hsn : RepresentationGrowth.adelicSourceNorm F G rho (x * s) ≤
        RepresentationGrowth.adelicSourceNorm F G rho x * M' := by
      have h1 := RepresentationGrowth.adelicHeight_mul_le F G rho hN x s
      rw [RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho (x * s),
        RepresentationGrowth.adelicHeight_eq_scalar_mul_sourceNorm F G rho x] at h1
      have h2 : c₀ * RepresentationGrowth.adelicSourceNorm F G rho (x * s) ≤
          c₀ * (RepresentationGrowth.adelicSourceNorm F G rho x * M') := by
        calc c₀ * RepresentationGrowth.adelicSourceNorm F G rho (x * s)
            ≤ c₀ * RepresentationGrowth.adelicSourceNorm F G rho x *
                RepresentationGrowth.adelicHeight F G rho s := h1
          _ ≤ c₀ * RepresentationGrowth.adelicSourceNorm F G rho x * M' :=
              mul_le_mul_of_nonneg_left hHs (mul_nonneg hc₀.le hx0)
          _ = c₀ * (RepresentationGrowth.adelicSourceNorm F G rho x * M') := by ring
      exact le_of_mul_le_mul_left h2 hc₀
    have hmax : max 1 (RepresentationGrowth.adelicSourceNorm F G rho (x * s)) ≤
        max 1 (RepresentationGrowth.adelicSourceNorm F G rho x) * M' := by
      refine max_le (one_le_mul_of_one_le_of_one_le (le_max_left _ _) hM'1) ?_
      exact hsn.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith))
    have hpos : 0 < max 1 (RepresentationGrowth.adelicSourceNorm F G rho (x * s)) :=
      lt_max_of_lt_left one_pos
    have hpos' : 0 < max 1 (RepresentationGrowth.adelicSourceNorm F G rho x) :=
      lt_max_of_lt_left one_pos
    have hlog := Real.log_le_log hpos hmax
    rw [Real.log_mul hpos'.ne' (by linarith)] at hlog
    have hσ1 := one_le_adelicLogHeight rho x
    unfold adelicLogHeight at hσ1 ⊢
    nlinarith

end Height

/-- **Reduction.** A local `L²` bound for the derivatives of `K_∞`- and `𝔷`-finite functions
(`AdelicLocalL2DerivativeBoundStatement`) and the count of rational points in conjugates of
compact sets by Siegel points (`SiegelRationalConjugateCountingStatement`) imply the logarithmic
Siegel bounds of `LogSquareIntegrableSiegelDerivativeBoundsStatement`, with the exponent `m` of
the weighted `L²` hypothesis for every word. -/
theorem logSquareIntegrableSiegelDerivativeBounds_of_reduction
    (hA : AdelicLocalL2DerivativeBoundStatement)
    (hB : SiegelRationalConjugateCountingStatement) :
    LogSquareIntegrableSiegelDerivativeBoundsStatement := by
  intro F _ _ G _ _ _ hred K N d rho hsmooth hcalc hKmax hrho 𝓕 _hIw Φ hΦ T i ν T₀ j hS C t Ω hΩ
  obtain ⟨⟨hleft, hsm, hKfin, hZfin, -⟩, -, m, hL2⟩ := hΦ
  refine ⟨m, fun D => ?_⟩
  classical
  obtain ⟨S, c, hSc, hloc⟩ := hA F G hred K hsmooth hcalc hKmax Φ hleft hsm hKfin hZfin D
  obtain ⟨B, hB0, hcount⟩ := hB F G hred T i ν T₀ j hS C t Ω hΩ (S * S⁻¹) (hSc.mul hSc.inv)
  obtain ⟨L, hL1, hLσ⟩ := exists_adelicLogHeight_mul_le rho hrho hSc
  have hΓd : IsDiscrete (rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
    isDiscrete_rationalSubgroup F G
  have : Countable (rationalSubgroup F G) := LeftCosetSpace.countable_of_isDiscrete _ hΓd
  set μG : Measure (RationalQuotient F G) :=
    LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F G) hΓd Measure.haar with hμG
  set f : RationalQuotient F G → ℂ :=
    fun y => Φ y.out / (rationalLogHeight F G rho y : ℂ) ^ m with hfdef
  have hf : MemLp f 2 μG := hL2
  have hSmeas : MeasurableSet S := hSc.isClosed.measurableSet
  -- `f` is measurable on `[G]`.
  have hΦmeas : Measurable (fun y : RationalQuotient F G => Φ y.out) := by
    have hcomp : (fun y : RationalQuotient F G => Φ y.out) ∘
        (LeftCosetSpace.mk (rationalSubgroup F G)) = Φ := by
      funext g
      obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) g
      change Φ (LeftCosetSpace.mk (rationalSubgroup F G) g).out = Φ g
      rw [hout, hleft q hq]
    have hm : Measurable ((fun y : RationalQuotient F G => Φ y.out) ∘
        (LeftCosetSpace.mk (rationalSubgroup F G))) := by
      rw [hcomp]
      exact hsm.1.measurable
    exact measurable_from_quotient.mpr hm
  have hfmeas : Measurable f :=
    hΦmeas.div ((Complex.measurable_ofReal.comp (measurable_rationalLogHeight rho)).pow_const m)
  have hf2meas : Measurable fun y => ‖f y‖ₑ ^ 2 := hfmeas.enorm.pow_const 2
  -- The weighted `L²` mass of `f`.
  set I : ℝ≥0∞ := ∫⁻ y, ‖f y‖ₑ ^ 2 ∂μG with hI
  have hIfin : I ≠ ∞ := by
    have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (two_ne_zero)
      ENNReal.ofNat_ne_top hf.eLpNorm_lt_top
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two] at h
    exact h.ne
  -- On a translate of `S`, the value of `Φ` is controlled by `f` and the height of `x`.
  have hpt (x s : AdelicGroupPoints F G) (hs : s ∈ S) :
      ‖Φ (x * s)‖ ≤ (L * adelicLogHeight F G rho x) ^ m *
        ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * s))‖ := by
    set y := LeftCosetSpace.mk (rationalSubgroup F G) (x * s) with hy
    obtain ⟨q, hq, hout⟩ := out_mk_eq_rational_mul (F := F) (G := G) (x * s)
    have hΦy : Φ y.out = Φ (x * s) := by
      change Φ (LeftCosetSpace.mk (rationalSubgroup F G) (x * s)).out = Φ (x * s)
      rw [hout, hleft q hq]
    have hσ1 := one_le_rationalLogHeight rho y
    have hσpos : 0 < rationalLogHeight F G rho y := zero_lt_one.trans_le hσ1
    have hσ : rationalLogHeight F G rho y ≤ L * adelicLogHeight F G rho x :=
      (rationalLogHeight_mk_le rho (x * s)).trans (hLσ x s hs)
    have hfy : ‖f y‖ * rationalLogHeight F G rho y ^ m = ‖Φ (x * s)‖ := by
      rw [hfdef]
      simp only
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hσpos.le, hΦy,
        div_mul_cancel₀ _ (pow_ne_zero _ hσpos.ne')]
    rw [← hfy, mul_comm]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hσpos.le hσ m) (norm_nonneg _)
  -- Folding: the translate `x S` covers `[G]` with multiplicity at most `#(G(F) ∩ x S S⁻¹ x⁻¹)`.
  have hdom (x : AdelicGroupPoints F G) :
      Measure.map (fun s => LeftCosetSpace.mk (rationalSubgroup F G) (x * s))
          ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict S) ≤
        (((rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
          ((fun y => x * y * x⁻¹) '' (S * S⁻¹))).encard : ℝ≥0∞) • μG := by
    let l : AdelicGroupPoints F G ≃ₜ AdelicGroupPoints F G := Homeomorph.mulLeft x
    let A' := l '' S
    have hD : ∀ a ∈ A', ∀ c ∈ A', a * c⁻¹ ∈ (fun y => x * y * x⁻¹) '' (S * S⁻¹) := by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨c, hc, rfl⟩
      have hi : c⁻¹ ∈ S⁻¹ := by simpa using hc
      exact ⟨a * c⁻¹, mul_mem_mul ha hi, by simp [l, mul_assoc]⟩
    have hA'c : IsCompact A' := hSc.image l.continuous
    have hm := LeftCosetSpace.leftCosetSupportMeasure (rationalSubgroup F G)
      (Measure.haar : Measure (AdelicGroupPoints F G))
      (LeftCosetSpace.isFundamentalDomain (rationalSubgroup F G) hΓd Measure.haar)
      hA'c.isClosed.measurableSet MeasurableSet.univ (subset_univ _) hD
    rw [Measure.restrict_univ] at hm
    have htrans : Measure.map (fun s => LeftCosetSpace.mk (rationalSubgroup F G) (x * s))
        ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict S) =
        Measure.map (LeftCosetSpace.mk (rationalSubgroup F G))
          ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict A') := by
      change Measure.map (LeftCosetSpace.mk (rationalSubgroup F G) ∘ l) _ = _
      rw [← Measure.map_map (LeftCosetSpace.measurable_mk _) l.continuous.measurable]
      congr 1
      calc
        _ = ((Measure.haar : Measure (AdelicGroupPoints F G)).map l).restrict A' := by
          have heq := (l.toMeasurableEquiv.restrict_map
            (Measure.haar : Measure (AdelicGroupPoints F G)) A').symm
          change Measure.map l (Measure.restrict _ (l ⁻¹' A')) = _ at heq
          rwa [show l ⁻¹' A' = S from preimage_image_eq _ l.injective] at heq
        _ = (Measure.haar : Measure (AdelicGroupPoints F G)).restrict A' := by
          rw [show (Measure.haar : Measure (AdelicGroupPoints F G)).map l = Measure.haar from
            map_mul_left_eq_self _ x]
    rw [htrans]
    exact hm
  -- The constant.
  have hδ0 : ∀ a : PositiveRealTorus.intrinsicSubgroup F T₀,
      0 ≤ siegelModulus F G T i ν T₀ j a := fun a => by
    unfold siegelModulus
    exact finprod_nonneg fun β => finprod_nonneg fun _ => pow_nonneg (NNReal.coe_nonneg _) _
  have hcBI : 0 ≤ (c : ℝ) * B * I.toReal := by positivity
  refine ⟨Real.sqrt ((c : ℝ) * B * I.toReal) * L ^ m, by positivity, fun a x hx => ?_⟩
  obtain ⟨hPfin, hPcard⟩ := hcount a x hx
  set σx := adelicLogHeight F G rho x with hσx
  have hσx1 : 1 ≤ σx := one_le_adelicLogHeight rho x
  set δ := siegelModulus F G T i ν T₀ j a with hδdef
  have hδ := hδ0 a
  set W : ℝ := (L * σx) ^ m with hW
  have hW0 : 0 ≤ W := pow_nonneg (mul_nonneg (zero_le_one.trans hL1) (zero_le_one.trans hσx1)) m
  -- The count, in `ℝ≥0∞`.
  have hmult : (((rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
      ((fun y => x * y * x⁻¹) '' (S * S⁻¹))).encard : ℝ≥0∞) ≤ ENNReal.ofReal (B * δ) := by
    rw [← Set.Finite.cast_ncard_eq hPfin, ENat.toENNReal_coe]
    have h := ENNReal.ofReal_le_ofReal hPcard
    rwa [ENNReal.ofReal_natCast] at h
  -- The main estimate in `ℝ≥0∞`.
  have hmain : ‖adelicIteratedDirectionalValue hsmooth D Φ x‖ₑ ^ 2 ≤
      (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 * (ENNReal.ofReal (B * δ) * I)) := by
    have hqx : Measurable fun s => LeftCosetSpace.mk (rationalSubgroup F G) (x * s) :=
      (LeftCosetSpace.measurable_mk _).comp (measurable_const_mul x)
    calc ‖adelicIteratedDirectionalValue hsmooth D Φ x‖ₑ ^ 2
        ≤ (c : ℝ≥0∞) * ∫⁻ s in S, ‖Φ (x * s)‖ₑ ^ 2
            ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := hloc x
      _ ≤ (c : ℝ≥0∞) * ∫⁻ s in S, ENNReal.ofReal W ^ 2 *
            ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * s))‖ₑ ^ 2
            ∂(Measure.haar : Measure (AdelicGroupPoints F G)) := by
          refine mul_le_mul_right (setLIntegral_mono' hSmeas fun s hs => ?_) _
          rw [← mul_pow]
          refine pow_le_pow_left₀ zero_le ?_ 2
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hW0]
          exact ENNReal.ofReal_le_ofReal (hpt x s hs)
      _ = (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 *
            ∫⁻ s in S, ‖f (LeftCosetSpace.mk (rationalSubgroup F G) (x * s))‖ₑ ^ 2
              ∂(Measure.haar : Measure (AdelicGroupPoints F G))) := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
      _ = (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 *
            ∫⁻ y, ‖f y‖ₑ ^ 2 ∂(Measure.map (fun s => LeftCosetSpace.mk
              (rationalSubgroup F G) (x * s))
                ((Measure.haar : Measure (AdelicGroupPoints F G)).restrict S))) := by
          rw [lintegral_map hf2meas hqx]
      _ ≤ (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 *
            ∫⁻ y, ‖f y‖ₑ ^ 2 ∂((((rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
              ((fun y => x * y * x⁻¹) '' (S * S⁻¹))).encard : ℝ≥0∞) • μG)) :=
          mul_le_mul_right (mul_le_mul_right (lintegral_mono' (hdom x) le_rfl) _) _
      _ = (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 *
            ((((rationalSubgroup F G : Set (AdelicGroupPoints F G)) ∩
              ((fun y => x * y * x⁻¹) '' (S * S⁻¹))).encard : ℝ≥0∞) * I)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ ≤ (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 * (ENNReal.ofReal (B * δ) * I)) :=
          mul_le_mul_right (mul_le_mul_right (mul_le_mul_left hmult _) _) _
  -- Back to real numbers.
  have hfin : (c : ℝ≥0∞) * (ENNReal.ofReal W ^ 2 * (ENNReal.ofReal (B * δ) * I)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hIfin))
  have hsq : ‖adelicIteratedDirectionalValue hsmooth D Φ x‖ ^ 2 ≤
      (c : ℝ) * W ^ 2 * (B * δ) * I.toReal := by
    have h := ENNReal.toReal_mono hfin hmain
    have hBδ : 0 ≤ B * δ := mul_nonneg hB0 hδ
    simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, toReal_enorm, ENNReal.coe_toReal,
      ENNReal.toReal_ofReal hW0, ENNReal.toReal_ofReal hBδ] at h
    linarith
  have hK0 : 0 ≤ Real.sqrt ((c : ℝ) * B * I.toReal) * L ^ m * Real.sqrt δ * σx ^ m := by
    positivity
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) hK0 two_ne_zero).mp ?_
  calc ‖adelicIteratedDirectionalValue hsmooth D Φ x‖ ^ 2
      ≤ (c : ℝ) * W ^ 2 * (B * δ) * I.toReal := hsq
    _ = (Real.sqrt ((c : ℝ) * B * I.toReal) * L ^ m * Real.sqrt δ * σx ^ m) ^ 2 := by
      rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hcBI, Real.sq_sqrt hδ, hW, mul_pow]
      ring

end Langlands.Global

import Langlands.Global.RankinSelberg.RealJacquetTestDistribution
import Langlands.Analysis.HolomorphicLinearContinuation
import Langlands.Representation.Archimedean.RealDiscreteSeparatedSource

/-! # Order-zero Jacquet distributions on the real reversal cell -/

noncomputable section

open Set MeasureTheory TopologicalSpace
open Langlands.Archimedean Langlands.GeneralLinear Langlands.HarmonicAnalysis Langlands.Whittaker
open scoped ContDiff Distributions Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquetTestDistribution

open RealGodement RealBorelTestAverage RealBorelRightHaar RealPrincipalSeriesDistribution
open RealBruhatDistributionRestriction RealJacquetFrobenius GramFormula PartialJacquet

variable {r : ℕ}
local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ
local notation "G" => Langlands.GeneralLinear (r + 1) ℝ
local notation "B" => upperTriangularSubgroup (r + 1) ℝ
local notation "U" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℝ
local notation "H" => U × B
local notation "O" => longestBruhatCell ℝ r
local notation "P" => (Fin (r + 1) → ℂ)
local notation "Signs" => (Fin (r + 1) → Fin 2)
local notation "dx" => rightBorelMeasure r
local notation "p₀(" K ")" => ContDiffMapSupportedIn.supSeminorm ℝ M ℝ ⊤ K 0

local instance : MeasurableSpace B := borel B
local instance : BorelSpace B := ⟨rfl⟩
local instance : MeasurableSpace U := borel U
local instance : BorelSpace U := ⟨rfl⟩
local instance : LocallyCompactSpace G := Units.isOpenEmbedding_val.locallyCompactSpace
local instance : LocallyCompactSpace B := (isClosed_upperTriangularSubgroup (r + 1) ℝ).locallyCompactSpace
local instance : SecondCountableTopology M :=
  inferInstanceAs (SecondCountableTopology (Fin (r + 1) → Fin (r + 1) → ℝ))
local instance : SecondCountableTopology G :=
  (show Topology.IsOpenEmbedding (Units.val : G → M) from Units.isOpenEmbedding_val).isInducing.secondCountableTopology
local instance : SecondCountableTopology B :=
  (show Topology.IsInducing (Subtype.val : B → G) from Topology.IsInducing.subtypeVal).secondCountableTopology

/-- The absolute inverse inducing density is a product of real powers of the diagonal. -/
theorem norm_inverseWeight_positionBorelCharacter (s : P) (e : Signs) (b : B) :
    ‖inverseWeight (positionBorelCharacter s e) b‖ =
      ∏ i : Fin (r + 1), |b.val.val i i| ^ (-(s i).re) := by
  have he : inverseWeight (positionBorelCharacter s e) b = (diagChar s e b.val.val)⁻¹ := rfl
  rw [he, norm_inv, diagChar, norm_prod, ← Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hx : 0 < |b.val.val i i| := abs_pos.mpr (diag_ne_zero b.property b.val.isUnit i)
  unfold RealJacquetFrobenius.charFun
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_abs, div_self hx.ne',
    one_pow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.rpow_neg hx.le]

private theorem continuous_norm_inverseWeight_family (e : Signs) :
    Continuous (fun q : P × B => ‖inverseWeight (positionBorelCharacter q.1 e) q.2‖) := by
  simp_rw [norm_inverseWeight_positionBorelCharacter]
  refine continuous_finsetProd _ fun i _ => ?_
  let x (q : P × B) := q.2.val.val i i
  have hx : Continuous x := ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i i).comp continuous_snd
  have hn (q : P × B) : 0 < |x q| := abs_pos.mpr (diag_ne_zero q.2.property q.2.val.isUnit i)
  have he : (fun q : P × B => |x q| ^ (-(q.1 i).re)) =
      fun q => Real.exp (Real.log |x q| * (-(q.1 i).re)) := funext fun q => Real.rpow_def_of_pos (hn q) _
  rw [he]
  exact Real.continuous_exp.comp ((hx.abs.log fun q => (hn q).ne').mul
    (Complex.continuous_re.comp ((continuous_apply i).comp continuous_fst)).neg)

private theorem norm_test_le_supSeminorm (K : Compacts M) (f : 𝓓_{K}(M, ℝ)) (x : M) :
    ‖f x‖ ≤ p₀(K) f := by
  have h := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ
    (f := f) (i := 0) (x := x)
  rw [norm_iteratedFDeriv_zero] at h
  exact h.trans ((Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℝ M ℝ ⊤ K)
    (Finset.mem_Iic.mpr (le_refl 0))) f)

private theorem exists_bound_reversalIntegral (a : ℝˣ) (e : Signs) {S : Set P} (hS : IsCompact S)
    (K : Compacts M) (hK : (K : Set M) ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ f : 𝓓_{K}(M, ℝ),
      ‖∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx)‖ ≤ C * p₀(K) f := by
  let : (upperStepHaar r a).IsHaarMeasure := upperStepHaar_isHaar r a
  let : SigmaFinite (upperStepHaar r a) := upperStepHaar_sigmaFinite r a
  let μ := (upperStepHaar r a).prod dx
  let V := (fun p : H => (jacquetOrbit r p).val) ⁻¹' (K : Set M)
  have hC : IsCompact (Subtype.val ⁻¹' (K : Set M) : Set (O : Set M)) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' K.isCompact (by simpa using hK)
  have hV : IsCompact V := (jacquetOrbit r).isCompact_preimage.mpr hC
  let : IsFiniteMeasure (μ.restrict V) := isFiniteMeasure_restrict.mpr hV.measure_lt_top.ne
  have hc := (continuous_norm_inverseWeight_family e).comp
    (continuous_fst.prodMk (continuous_snd.comp continuous_snd) : Continuous (fun q : P × H => (q.1, q.2.2)))
  obtain ⟨A, hA⟩ := (hS.prod hV).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max A 0 * μ.real V, mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg, fun s hs f => ?_⟩
  have hZero (p : H) (hp : p ∉ V) : jacquetOrbitKernel a s e f p = 0 := by
    rw [jacquetOrbitKernel, show f ((jacquetOrbit r p).val) = 0 from f.zero_on_compl hp,
      Complex.ofReal_zero, mul_zero, zero_mul]
  change ‖∫ p, jacquetOrbitKernel a s e f p ∂μ‖ ≤ _
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hZero]
  have hBound : ∀ᵐ p ∂μ.restrict V, ‖jacquetOrbitKernel a s e f p‖ ≤ max A 0 * p₀(K) f :=
    ae_restrict_of_forall_mem hV.measurableSet fun p hp => by
      simp only [jacquetOrbitKernel, norm_mul, Complex.norm_real, norm_standardCharacter, mul_one]
      have hb := hA (s, p) ⟨hs, hp⟩
      change ‖‖inverseWeight (positionBorelCharacter s e) p.2‖‖ ≤ A at hb
      rw [Real.norm_of_nonneg (norm_nonneg _)] at hb
      exact mul_le_mul (hb.trans (le_max_left _ _)) (norm_test_le_supSeminorm K f _)
        (norm_nonneg _) (le_max_right _ _)
  simpa only [Measure.real, Measure.restrict_apply_univ, mul_right_comm (max A 0)] using
    norm_integral_le_of_norm_le_const hBound

/-- The joint integral determines a distribution on the reversal cell at each exponent. -/
def reversalDistribution (a : ℝˣ) (s : P) (e : Signs) : 𝓓'(O, ℂ) := by
  let μ := (upperStepHaar r a).prod dx
  let L : 𝓓(O, ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun f => ∫ p, jacquetOrbitKernel a s e f p ∂μ
      map_add' := by
        intro f g
        change (∫ p, jacquetOrbitKernel a s e (f + g : 𝓓(O, ℝ)) p ∂μ) = _
        rw [show jacquetOrbitKernel a s e (f + g : 𝓓(O, ℝ)) =
          (fun p => jacquetOrbitKernel a s e f p + jacquetOrbitKernel a s e g p) by
            funext p
            simp only [jacquetOrbitKernel, add_apply, Complex.ofReal_add, mul_add, add_mul],
          integral_add (integrable_jacquetOrbitKernel a s e f) (integrable_jacquetOrbitKernel a s e g)]
      map_smul' := by
        intro c f
        change (∫ p, jacquetOrbitKernel a s e (c • f : 𝓓(O, ℝ)) p ∂μ) = _
        rw [show jacquetOrbitKernel a s e (c • f : 𝓓(O, ℝ)) =
          (fun p => c • jacquetOrbitKernel a s e f p) by
            funext p
            simp only [jacquetOrbitKernel, smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.real_smul]
            ring, integral_smul]
        rfl }
  refine ContinuousLinearMap.toUniformConvergenceCLM (RingHom.id ℝ) ℂ {S : Set 𝓓(O, ℝ) | IsCompact S}
    ⟨L, (TestFunction.continuous_iff_continuous_comp L).mpr (fun K hK => ?_)⟩
  obtain ⟨C, hC, hBound⟩ := exists_bound_reversalIntegral a e (isCompact_singleton (x := s)) K hK
  let F := L.comp (TestFunction.ofSupportedInCLM ℝ hK).toLinearMap
  change Continuous F
  refine WithSeminorms.continuous_normedSpace_rng ℂ (ContDiffMapSupportedIn.withSeminorms' ℝ M ℝ ⊤ K)
    F ⟨{0}, ⟨C, hC⟩, fun f => ?_⟩
  rw [Finset.sup_singleton, smul_apply]
  change ‖∫ p, jacquetOrbitKernel a s e f p ∂μ‖ ≤ C * p₀(K) f
  exact hBound s (mem_singleton s) f

@[simp] theorem reversalDistribution_apply (a : ℝˣ) (s : P) (e : Signs) (f : 𝓓(O, ℝ)) :
    reversalDistribution a s e f = ∫ p : H, jacquetOrbitKernel a s e f p ∂((upperStepHaar r a).prod dx) := rfl

/-- The reversal-cell family has uniformly bounded order zero on compact parameter
and test supports. -/
theorem reversalDistribution_uniform_order_zero (a : ℝˣ) (e : Signs) {S : Set P} (hS : IsCompact S)
    (K : Compacts M) (hK : (K : Set M) ⊆ O) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ f, ‖reversalDistribution a s e (TestFunction.ofSupportedIn hK f)‖ ≤
      C * p₀(K) f :=
  exists_bound_reversalIntegral a e hS K hK

open RealBruhatChartVanishing RealWhittakerTranslationDistribution

/-- The spectral family of reversal-cell distributions is entire on every test. -/
theorem differentiable_reversalDistribution (a : ℝˣ) (e : Signs) (f : 𝓓(O, ℝ)) :
    Differentiable ℂ (fun s : P => reversalDistribution a s e f) :=
  differentiable_reversalIntegral a e f

/-- The reversal-cell family agrees with the restriction of the full distribution in the chamber. -/
theorem reversalDistribution_eq_dominant (a : ℝˣ) (s : P) (e : Signs)
    (hDom : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r) (f : 𝓓(O, ℝ)) :
    reversalDistribution a s e f = dominantDistribution a s e hDom (TestFunction.monoCLM ℝ f) :=
  (dominantDistribution_reversalIntegral a s e hDom f).symm

/-- The strict-dominance region in the exponents of the actual Borel character. -/
def normalizedDominantChamber (e : Signs) : Set P :=
  {s | IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks s e)) r}

theorem realPositionExponent_normalizedCharacterBlocks (s : P) (e : Signs) (i : Fin (r + 1)) :
    realPositionExponent (normalizedCharacterBlocks s e) i = expo s i := by
  rw [normalizedCharacterBlocks, RealDiscreteSeparated.realPositionExponent_map_character _ _ (by simpa only [List.length_ofFn] using i.isLt),
    List.getElem_ofFn]
  rfl

private theorem normalizedDominantChamber_eq (e : Signs) : normalizedDominantChamber e =
    ⋂ i : Fin r, {s : P | (expo s i.succ).re < (expo s i.castSucc).re} := by
  ext s
  rw [normalizedDominantChamber, mem_ofPred_eq, mem_iInter]
  constructor
  · intro hs i
    change (expo s i.succ).re < (expo s i.castSucc).re
    rw [← realPositionExponent_normalizedCharacterBlocks _ e, ← realPositionExponent_normalizedCharacterBlocks _ e]
    exact hs i i.isLt
  · intro hs j hj
    let i : Fin r := ⟨j, hj⟩
    change (realPositionExponent (normalizedCharacterBlocks s e) i.succ).re <
      (realPositionExponent (normalizedCharacterBlocks s e) i.castSucc).re
    have h : (expo s i.succ).re < (expo s i.castSucc).re := hs i
    simpa only [realPositionExponent_normalizedCharacterBlocks] using h

theorem isOpen_normalizedDominantChamber (e : Signs) : IsOpen (normalizedDominantChamber e) := by
  rw [normalizedDominantChamber_eq]
  have hc (i : Fin (r + 1)) : Continuous (fun s : P => (expo s i).re) :=
    Complex.continuous_re.comp (((continuous_apply i).sub continuous_const).add continuous_const)
  exact isOpen_iInter_of_finite fun i => isOpen_lt (hc _) (hc _)

theorem normalizedDominantChamber_nonempty (e : Signs) : (normalizedDominantChamber e).Nonempty := by
  let s (i : Fin (r + 1)) : ℂ := -((i.val : ℂ) + (i.val : ℂ))
  refine ⟨s, ?_⟩
  rw [normalizedDominantChamber_eq, mem_iInter]
  intro i
  change (expo s i.succ).re < (expo s i.castSucc).re
  simp only [expo, s, Complex.add_re, Complex.sub_re, Complex.natCast_re,
    Complex.neg_re, Complex.one_re, Fin.val_succ, Fin.val_castSucc, Nat.cast_add, Nat.cast_one]
  linarith

private theorem monoCLM_smoothVectorFieldDerivativeTest {Ω Ω' : Opens M} (h : Ω' ≤ Ω)
    (V : M → M) (hV : ContDiff ℝ ∞ V) (f : 𝓓(Ω', ℝ)) :
    (TestFunction.monoCLM ℝ (smoothVectorFieldDerivativeTest hV.contDiffOn f) : 𝓓(Ω, ℝ)) =
      smoothVectorFieldDerivativeTest hV.contDiffOn (TestFunction.monoCLM ℝ f) := by
  have he (g : 𝓓(Ω', ℝ)) : ((TestFunction.monoCLM ℝ g : 𝓓(Ω, ℝ)) : M → ℝ) = g := by simp [h]
  ext x
  rw [congrFun (he _) x]
  simp only [smoothVectorFieldDerivativeTest_apply, he]

/-- The infinitesimal upper-unipotent laws hold on reversal-cell tests at every exponent. -/
theorem reversalDistribution_infinitesimal (a : ℝˣ) (s : P) (e : Signs) (j : DirectionIndex r)
    (f : 𝓓(O, ℝ)) :
    reversalDistribution a s e (smoothVectorFieldDerivativeTest (ambientField j).contDiff.contDiffOn f) =
      infinitesimalScalar (-a) * (characterWeight j • reversalDistribution a s e f) := by
  let g := smoothVectorFieldDerivativeTest (ambientField j).contDiff.contDiffOn f
  have hDiff : Differentiable ℂ (fun q : P => infinitesimalScalar (-a) *
      (characterWeight j • reversalDistribution a q e f)) := by
    simp only [Complex.real_smul]
    exact ((differentiable_reversalDistribution a e f).const_mul _).const_mul _
  refine congrFun (Langlands.Analysis.eq_of_differentiable_eqOn_open
    (differentiable_reversalDistribution a e g) hDiff (isOpen_normalizedDominantChamber e)
      (normalizedDominantChamber_nonempty e) ?_) s
  intro q hq
  have hD : IsStrictlyDominant (realPositionExponent (normalizedCharacterBlocks q e)) r := hq
  let T := dominantDistribution a q e hD
  have hT := infinitesimal_of_unipotent_covariance T (-a) (dominantDistribution_covariant a q e hD)
  change reversalDistribution a q e g = infinitesimalScalar (-a) * (characterWeight j • reversalDistribution a q e f)
  rw [reversalDistribution_eq_dominant a q e hD g, reversalDistribution_eq_dominant a q e hD f]
  have hOpen : O ≤ invertibleDomain r := by
    rintro X ⟨x, _, rfl⟩
    exact ⟨x, rfl⟩
  dsimp only [g]
  rw [monoCLM_smoothVectorFieldDerivativeTest hOpen _ (ambientField j).contDiff]
  exact hT j _

/-- The reversal-cell Jacquet distributions have entire evaluations, bounded order zero on
compact parameter and test supports, and infinitesimal Whittaker covariance. -/
def RealJacquetReversalDistributionStatement : Prop :=
  ∀ (a : ℝˣ) (e : Signs),
    (∀ f : 𝓓(O, ℝ), Differentiable ℂ (fun s : P => reversalDistribution a s e f)) ∧
    (∀ (S : Set P), IsCompact S → ∀ (K : Compacts M) (hK : (K : Set M) ⊆ O),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ S, ∀ f, ‖reversalDistribution a s e (TestFunction.ofSupportedIn hK f)‖ ≤ C * p₀(K) f) ∧
    ∀ (s : P) (j : DirectionIndex r) (f : 𝓓(O, ℝ)),
      reversalDistribution a s e (smoothVectorFieldDerivativeTest (ambientField j).contDiff.contDiffOn f) =
        infinitesimalScalar (-a) * (characterWeight j • reversalDistribution a s e f)

theorem realJacquetReversalDistribution : RealJacquetReversalDistributionStatement (r := r) := by
  intro a e
  exact ⟨differentiable_reversalDistribution a e, fun _ => reversalDistribution_uniform_order_zero a e,
    fun s => reversalDistribution_infinitesimal a s e⟩

end Langlands.Global.RankinSelbergGlobal.RealJacquetTestDistribution

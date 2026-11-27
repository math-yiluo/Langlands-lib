import Langlands.Global.AdelicEisensteinAmbientShiftStatement
import Langlands.Global.AdelicEisensteinCentralCovariance
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Global.AdelicRestrictionSplitCentreFiniteVolumeProof
import Langlands.Global.LeftCosetImageMajorant
import Langlands.Global.AdelicSpectralDecompositionReduction
import Langlands.Global.AdelicFullRationalQuotientProduct
import Langlands.Global.AdelicPrincipalQuotientProduct
import Langlands.Global.AdelicRelativeAmbientParameterProduct
import Langlands.Global.AdelicSpectralCoordinateProduct
import Langlands.Global.AdelicNonAssociateWavePacketOrthogonality
import Langlands.Global.AdelicWavePacketCompletenessReduction
import Langlands.Analysis.CompactLinearParameterIntegralProof
import Mathlib.MeasureTheory.Function.LpSeminorm.Prod
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # Compression of full wave packets along the split centre -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter
open scoped CategoryTheory.MonObj ContDiff ComplexConjugate ENNReal

set_option autoImplicit false

namespace Langlands.Global

namespace WavePacketCentreCompression

section Product

variable {A Y : Type*} [MeasurableSpace A] [MeasurableSpace Y]
  {muA : Measure A} {muY : Measure Y} [SFinite muA] [SFinite muY]
  {S : Set A}

private theorem prod_restrict_centre :
    (muA.prod muY).restrict (S ×ˢ (univ : Set Y)) = (muA.restrict S).prod muY := by
  rw [← Measure.prod_restrict, Measure.restrict_univ]

private theorem memLp_indicator_snd (hS : MeasurableSet S) (hSf : muA S < ⊤) {f : Y → ℂ} (hf : MemLp f 2 muY) :
    MemLp ((S ×ˢ (univ : Set Y)).indicator (fun q => f q.2)) 2 (muA.prod muY) := by
  let : Fact (muA S < ⊤) := ⟨hSf⟩
  rw [memLp_indicator_iff_restrict (hS.prod MeasurableSet.univ).nullMeasurableSet,
    prod_restrict_centre]
  exact hf.comp_snd (muA.restrict S)

private theorem ae_eq_zero_of_indicator_snd (hS : MeasurableSet S) (hSf : muA S < ⊤)
    {f : Y → ℂ} (hSn : muA S ≠ 0)
    (hf : (S ×ˢ (univ : Set Y)).indicator (fun q => f q.2) =ᵐ[muA.prod muY] 0) :
    f =ᵐ[muY] 0 := by
  let : Fact (muA S < ⊤) := ⟨hSf⟩
  have hf' := hf.filter_mono (ae_mono (Measure.restrict_le_self (s := S ×ˢ (univ : Set Y))))
  rw [prod_restrict_centre] at hf'
  have hmem : ∀ᵐ (q : A × Y) ∂(muA.restrict S).prod muY, q.1 ∈ S :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hS)
  have hzero : ∀ᵐ (q : A × Y) ∂(muA.restrict S).prod muY, f q.2 = 0 := by
    filter_upwards [hf', hmem] with q hq hqS
    simpa only [indicator_of_mem (mk_mem_prod hqS (mem_univ _)), Pi.zero_apply] using hq
  have hR : muA.restrict S ≠ 0 := fun he => hSn (Measure.restrict_eq_zero.mp he)
  let : NeBot (ae (muA.restrict S)) := ae_neBot.mpr hR
  have hswap := ((Measure.measurePreserving_swap («μ» := muY) (ν := muA.restrict S)).quasiMeasurePreserving.ae hzero)
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with y hy
  exact hy.exists.choose_spec

private theorem sq_norm_integral_le {muS : Measure A} [IsFiniteMeasure muS]
    {w : A → ℂ} (hw : MemLp w 2 muS) :
    ‖∫ x, w x ∂muS‖ ^ 2 ≤ muS.real univ * ∫ x, ‖w x‖ ^ 2 ∂muS := by
  have hle := integral_mul_norm_le_Lp_mul_Lq («μ» := muS) Real.HolderConjugate.two_two
    (f := w) (g := fun _ => (1 : ℝ)) (by simpa using hw) (by simp [memLp_const])
  have h1 : ‖∫ x, w x ∂muS‖ ≤ Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂muS) * Real.sqrt (muS.real univ) := by
    refine (norm_integral_le_integral_norm _).trans ?_
    simpa [Real.rpow_two, Real.sqrt_eq_rpow, smul_eq_mul] using hle
  calc
    _ ≤ (Real.sqrt (∫ x, ‖w x‖ ^ 2 ∂muS) * Real.sqrt (muS.real univ)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = _ := by
      rw [mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _),
        Real.sq_sqrt (by positivity), mul_comm]

private theorem memLp_integral_centre (hSf : muA S < ⊤) {w : A × Y → ℂ} (hw : MemLp w 2 (muA.prod muY)) :
    MemLp (fun y => ∫ a in S, w (a, y) ∂muA) 2 muY := by
  let : Fact (muA S < ⊤) := ⟨hSf⟩
  let muS := muA.restrict S
  have hw' : MemLp w 2 (muS.prod muY) := by
    rw [← prod_restrict_centre]
    exact hw.restrict _
  have ha : AEStronglyMeasurable (fun y => ∫ a, w (a, y) ∂muS) muY :=
    hw'.aestronglyMeasurable.prod_swap.integral_prod_right'
  have hsqi := (memLp_two_iff_integrable_sq_norm hw'.aestronglyMeasurable).1 hw'
  refine (memLp_two_iff_integrable_sq_norm ha).2
    ((hsqi.integral_prod_right.const_mul (muS.real univ)).mono'
      (ha.norm.pow 2) ?_)
  filter_upwards [hw'.aestronglyMeasurable.prodMk_right, hsqi.prod_left_ae] with y hymeas hyint
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact sq_norm_integral_le ((memLp_two_iff_integrable_sq_norm hymeas).2 hyint)

private theorem integral_indicator_mul_conj (hS : MeasurableSet S) (hSf : muA S < ⊤)
    {f : Y → ℂ} {w : A × Y → ℂ}
    (hf : MemLp f 2 muY) (hw : MemLp w 2 (muA.prod muY)) :
    ∫ q, (S ×ˢ (univ : Set Y)).indicator (fun q => f q.2) q * conj (w q) ∂(muA.prod muY) =
      ∫ y, f y * conj (∫ a in S, w (a, y) ∂muA) ∂muY := by
  let : Fact (muA S < ⊤) := ⟨hSf⟩
  let muS := muA.restrict S
  have hw' : MemLp w 2 (muS.prod muY) := by
    rw [← prod_restrict_centre]
    exact hw.restrict _
  have hf' : MemLp (fun q : A × Y => f q.2) 2 (muS.prod muY) := hf.comp_snd muS
  have hi : Integrable (fun q : A × Y => f q.2 * conj (w q)) (muS.prod muY) := by
    have hwstar : MemLp (fun q : A × Y => conj (w q)) 2 (muS.prod muY) := hw'.star
    exact hf'.integrable_mul hwstar
  have hind := funext fun q => (indicator_mul_left (S ×ˢ (univ : Set Y)) (fun q => f q.2)
    (fun q => conj (w q)) (i := q)).symm
  rw [hind]
  rw [integral_indicator (hS.prod MeasurableSet.univ), prod_restrict_centre,
    integral_prod_symm _ hi]
  simp only [integral_const_mul, integral_conj, muS]

end Product

section Coefficients

variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] [MeasurableSpace Z] [BorelSpace Z]
  {muZ : Measure Z} [IsFiniteMeasureOnCompacts muZ]

private theorem smooth_compact_integrated_coefficient {c : X × Z → ℂ} {b : Z → ℂ}
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hk : HasCompactSupport c) (hb : Continuous b) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ∫ z, b z * c (x, z) ∂muZ) ∧
      HasCompactSupport (fun x => ∫ z, b z * c (x, z) ∂muZ) := by
  let T := Prod.snd '' tsupport c
  have hT : IsCompact T := hk.image continuous_snd
  have hzero (x : X) {z : Z} (hz : z ∉ T) : c (x, z) = 0 := by
    by_contra hn
    exact hz ⟨(x, z), subset_tsupport _ hn, rfl⟩
  have hrestrict (x : X) : ∫ z in T, b z * c (x, z) ∂muZ = ∫ z, b z * c (x, z) ∂muZ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz => by rw [hzero x hz, mul_zero]
  constructor
  · rw [← contDiffOn_univ, contDiffOn_infty]
    intro n
    have hn := Langlands.Analysis.CompactLinearParameterIntegral.contDiffOn_integral_nat
      («μ» := muZ) (s := (univ : Set X)) hT isOpen_univ hb n (X × Z) univ isOpen_univ
      (fun _ => ContinuousLinearMap.inl ℝ X Z) continuous_const
      (fun z => (0, z)) (continuous_const.prodMk continuous_id) c hc.contDiffOn
      (fun _ _ _ _ => mem_univ _)
    apply hn.congr
    intro x _
    simp [hrestrict]
  · apply HasCompactSupport.intro (hk.image continuous_fst)
    intro x hx
    have hz (z : Z) : c (x, z) = 0 := by
      by_contra hn
      exact hx ⟨(x, z), subset_tsupport _ hn, rfl⟩
    simp only [hz, mul_zero, integral_zero]

end Coefficients

section FourierIntegral

variable {X Z A : Type*} [TopologicalSpace X] [T2Space X] [TopologicalSpace Z] [T2Space Z]
  [TopologicalSpace A] [SecondCountableTopology X] [SecondCountableTopology Z] [SecondCountableTopology A]
  [MeasurableSpace X] [OpensMeasurableSpace X]
  [MeasurableSpace Z] [OpensMeasurableSpace Z] [MeasurableSpace A] [OpensMeasurableSpace A]
  {muA : Measure A} [IsFiniteMeasure muA] {muX : Measure X} {muZ : Measure Z}
  [SFinite muX] [SFinite muZ] [IsFiniteMeasureOnCompacts muX] [IsFiniteMeasureOnCompacts muZ]

omit [T2Space Z] [SecondCountableTopology A] [MeasurableSpace Z] [OpensMeasurableSpace Z] in
private theorem continuous_centre_integral {phase : A × Z → ℂ} (hc : Continuous phase)
    (hb : ∀ q, ‖phase q‖ ≤ 1) : Continuous (fun z => ∫ a, phase (a, z) ∂muA) :=
  continuous_of_dominated
    (fun _z => (hc.comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable)
    (fun z => Eventually.of_forall fun a => hb (a, z)) (integrable_const (1 : ℝ))
    (Eventually.of_forall fun _a => hc.comp (continuous_const.prodMk continuous_id))

omit [T2Space X] in
private theorem centre_spectral_integral {k : ℕ}
    {coeff : Fin k → X × Z → ℂ} {v : Fin k → X → ℂ} {phase : A × Z → ℂ}
    (hcoeff : ∀ j, Continuous (coeff j)) (hcompact : ∀ j, HasCompactSupport (coeff j))
    (hv : ∀ j, Continuous (v j)) (hphase : Continuous phase) (hb : ∀ q, ‖phase q‖ ≤ 1) :
    (∫ a, ∫ p, ∑ j, phase (a, p.2) * coeff j p * v j p.1 ∂(muX.prod muZ) ∂muA) =
      ∫ x, ∑ j, (∫ z, (∫ a, phase (a, z) ∂muA) * coeff j (x, z) ∂muZ) * v j x ∂muX := by
  let b (z : Z) := ∫ a, phase (a, z) ∂muA
  have hbc : Continuous b := continuous_centre_integral hphase hb
  let f (j : Fin k) (q : A × (X × Z)) := phase (q.1, q.2.2) * coeff j q.2 * v j q.2.1
  have hi (j : Fin k) : Integrable (f j) (muA.prod (muX.prod muZ)) := by
    let g (p : X × Z) := coeff j p * v j p.1
    have hg : Integrable g (muX.prod muZ) :=
      ((hcoeff j).mul ((hv j).comp continuous_fst)).integrable_of_hasCompactSupport
        (hcompact j).mul_right
    have hi := hg.norm.comp_snd muA
    refine hi.mono' ?_ (Eventually.of_forall fun q => ?_)
    · exact (((hphase.comp (continuous_fst.prodMk (continuous_snd.snd))).mul
        ((hcoeff j).comp continuous_snd)).mul ((hv j).comp continuous_snd.fst)).aestronglyMeasurable
    · change ‖phase (q.1, q.2.2) * coeff j q.2 * v j q.2.1‖ ≤ ‖coeff j q.2 * v j q.2.1‖
      rw [mul_assoc, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
  have hsum : Integrable (fun q => ∑ j, f j q) (muA.prod (muX.prod muZ)) :=
    integrable_finsetSum _ fun j _ => hi j
  have ha (p : X × Z) (j : Fin k) : Integrable (fun a => f j (a, p)) muA := by
    have hp : Continuous (fun a => f j (a, p)) := by
      change Continuous (fun a => phase (a, p.2) * coeff j p * v j p.1)
      exact ((hphase.comp (continuous_id.prodMk continuous_const)).mul
        continuous_const).mul continuous_const
    refine (integrable_const (‖coeff j p * v j p.1‖ : ℝ)).mono' hp.aestronglyMeasurable
      (Eventually.of_forall fun a => ?_)
    change ‖phase (a, p.2) * coeff j p * v j p.1‖ ≤ ‖coeff j p * v j p.1‖
    rw [mul_assoc, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hb _)
  have heq (p : X × Z) : (∫ a, ∑ j, f j (a, p) ∂muA) =
      ∑ j, (b p.2 * coeff j p) * v j p.1 := by
    rw [integral_finsetSum _ (fun j _ => ha p j)]
    simp only [f, integral_mul_const, b]
  have hz (x : X) (j : Fin k) : Integrable (fun z => b z * coeff j (x, z) * v j x) muZ := by
    refine ((hbc.mul ((hcoeff j).comp (continuous_const.prodMk continuous_id))).mul
      continuous_const).integrable_of_hasCompactSupport ?_
    apply HasCompactSupport.intro ((hcompact j).image continuous_snd)
    intro z hz
    have hc : coeff j (x, z) = 0 := by
      by_contra hn
      exact hz ⟨(x, z), subset_tsupport _ hn, rfl⟩
    change b z * coeff j (x, z) * v j x = 0
    rw [hc, mul_zero, zero_mul]
  change (∫ a, ∫ p, ∑ j, f j (a, p) ∂(muX.prod muZ) ∂muA) =
    ∫ x, ∑ j, (∫ z, b z * coeff j (x, z) ∂muZ) * v j x ∂muX
  rw [← integral_prod _ hsum, integral_prod_symm _ hsum]
  simp only [heq]
  have hsum' := hsum.integral_prod_right
  simp only [heq] at hsum'
  rw [integral_prod _ hsum']
  apply integral_congr_ae (Eventually.of_forall fun x => ?_)
  rw [integral_finsetSum _ fun j _ => hz x j]
  simp only [integral_mul_const]

end FourierIntegral

open GroupScheme AdelicGroupPoints PositiveRealTorus RestrictionSplitCentre
  Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic
open scoped TensorProduct

section CharacterPower

variable {F : Type} [Field F] [NumberField F] {H : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
private theorem pairing_imaginary (x : RealCharacterParameter F H) (y : RealCharacterDual F H) :
    complexParameterPairing F H (imaginaryParameter F H x) y =
      Complex.I * (realParameterPairing F H x y : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change complexParameterPairing F H (((r : ℂ) * Complex.I) ⊗ₜ[ℤ] χ) y = _
    simp only [complexParameterPairing_tmul, realParameterPairing_tmul, Complex.ofReal_mul]
    ring
  | add x x' hx hx' =>
    simp only [map_add, LinearMap.add_apply, hx, hx', Complex.ofReal_add, mul_add]

private theorem parameterPower_imaginary_norm (x : RealCharacterParameter F H) (g : AdelicGroupPoints F H) :
    ‖parameterPower F H (imaginaryParameter F H x) g‖ = 1 := by
  rw [parameterPower, pairing_imaginary, Complex.norm_exp]
  simp [Complex.mul_re]

end CharacterPower

section Quotient

variable (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "Z₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hZG" => isSplitComponent_canonicalComponent F G
local notation "injectiveCentreRestriction" => canonical_characterRestrict_injective F G centralSplitTorusCharacter
local notation "hc₀" => IsCentralSplitTorus.isCentral (IsSplitComponent.isCentralSplitTorus hZG)
local notation "ACentre" => intrinsicSubgroup F Z₀
local notation "Yrel" => CanonicalQuotient F G
local notation "Yfull" => RationalQuotient F G
private def centreQuotientHaar (hG : IsConnectedReductive G) {I : Type} [Fintype I]
    (e : (Z₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) : Measure ACentre := by
  let := canonical_finiteIndex F G hG
  exact normalizedPositiveHaarMeasure F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀

private def centreQuotientCoordinates (hG : IsConnectedReductive G) {I : Type} [Fintype I]
    (e : (Z₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) : ACentre × Yrel ≃ᵐ Yfull := by
  let := canonical_finiteIndex F G hG
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  exact (((Homeomorph.refl ACentre).prodCongr (canonicalNormOneQuotientHomeomorph F G hG).symm).trans
    (rationalQuotientDecomposition F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀)).toMeasurableEquiv

variable (hG : IsConnectedReductive G)
local notation "normOneToCanonical" => canonicalNormOneQuotientHomeomorph F G hG
private theorem centreQuotientCoordinates_apply {I : Type} [Fintype I]
    (e : (Z₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (a : ACentre) (y : Yrel) :
    centreQuotientCoordinates F G hG (I := I) e (a, y) =
      LeftCosetSpace.mk (AdelicGroupPoints.rationalSubgroup F G)
        (positivePointMap F G Z₀ i₀ a * (((normOneToCanonical).symm y).out : normOneSubgroup F G)) := by
  let := canonical_finiteIndex F G hG
  change rationalQuotientDecomposition F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀ (a, (normOneToCanonical).symm y) = _
  conv_lhs => rw [← LeftCosetSpace.mk_out _ ((normOneToCanonical).symm y)]
  exact rationalQuotientDecomposition_mk F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀ a _

private theorem normOneRep_mk_canonical (y : Yrel) :
    LeftCosetSpace.mk (canonicalRationalSubgroup F G)
      ((((normOneToCanonical).symm y).out : normOneSubgroup F G) : AdelicGroupPoints F G) = y := by
  have he := (normOneToCanonical).apply_symm_apply y
  rw [← LeftCosetSpace.mk_out _ ((normOneToCanonical).symm y),
    coe_canonicalNormOneQuotientHomeomorph] at he
  exact he

private theorem measurePreserving_centreQuotientCoordinates {I : Type} [Fintype I]
    (e : (Z₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) :
    MeasurePreserving (centreQuotientCoordinates F G hG (I := I) e)
      ((centreQuotientHaar F G hG (I := I) e).prod (canonicalMeasure F G))
      (rationalQuotientHaarMeasure F G) := by
  let := canonical_finiteIndex F G hG
  let := canonicalQuotient_borelSpace F G centralSplitTorusCharacter hG
  let : SigmaFinite (centreQuotientHaar F G hG (I := I) e) :=
    normalizedPositiveHaarMeasure_sigmaFinite F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀
  let : IsFiniteMeasure (canonicalMeasure F G) := connectedReductiveQuotientFiniteVolume F G hG _ _
    (isSplitComponent_canonicalRestrictionComponent F G)
  have hY := (measurePreserving_canonicalNormOneQuotientHomeomorph F G hG).symm
    (e := (normOneToCanonical).toMeasurableEquiv)
  exact (measurePreserving_rationalQuotientDecomposition F G Z₀ i₀ (injectiveCentreRestriction hG) I e hc₀).comp
    ((MeasurePreserving.id (centreQuotientHaar F G hG (I := I) e)).prod hY)

end Quotient

section SpectralCharts

private instance spectralMeasure_isAddHaarMeasure (n : ℕ) : (spectralMeasure n).IsAddHaarMeasure := by
  unfold spectralMeasure
  refine Measure.IsAddHaarMeasure.smul _ (pow_ne_zero _ (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)) ?_
  exact ENNReal.pow_ne_top (by simp [Real.pi_pos])

private theorem spectralMeasure_map_to_product {n m h : ℕ}
    (L : (Fin h → ℝ) ≃L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ))) :
    ∃ c : NNReal, Measure.map L (spectralMeasure h) = c • ((spectralMeasure n).prod (spectralMeasure m)) :=
  ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}

private theorem continuous_parameterPower_in_imaginary_chart {m : ℕ} {A : Type*} [TopologicalSpace A]
    {s : A → AdelicGroupPoints F G} (hs : Continuous s)
    (e : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G) :
    Continuous fun p : A × (Fin m → ℝ) => parameterPower F G (imaginaryParameter F G (e p.2)) (s p.1) := by
  have hsum (z : Fin m → ℝ) : e z = ∑ j, z j • e (Pi.single j 1) := by
    have hrep : ∑ j, z j • Pi.single j 1 = z := by
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using (Pi.basisFun ℝ (Fin m)).sum_repr z
    calc
      e z = e (∑ j, z j • Pi.single j 1) := congrArg e hrep.symm
      _ = _ := by simp only [map_sum, map_smul]
  have heq (p : A × (Fin m → ℝ)) :
      parameterPower F G (imaginaryParameter F G (e p.2)) (s p.1) =
        Complex.exp (Complex.I * ((∑ j, p.2 j * realParameterPairing F G (e (Pi.single j 1))
          (characterLog F G (s p.1)) : ℝ) : ℂ)) := by
    rw [parameterPower, pairing_imaginary, hsum p.2]
    simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  simp_rw [heq]
  refine Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp ?_))
  refine continuous_finsetSum _ fun j _ => (continuous_apply j |>.comp continuous_snd).mul ?_
  exact (InducedInnerProductIntegrable.continuous_realParameterPairing _).comp
    ((continuous_characterLog F G).comp (hs.comp continuous_fst))

omit [NumberField F] in
private theorem continuous_meromorphic_real_linear {X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    {E : ComplexCharacterParameter F G → ℂ} {D : Set (ComplexCharacterParameter F G)}
    (hE : IsMeromorphicInCoordinatesOn E D) (L : X →ₗ[ℝ] ComplexCharacterParameter F G)
    (hL : ∀ x, L x ∈ D) : Continuous (fun x => E (L x)) := by
  let := hE.1
  let d := Module.finrank ℂ (ComplexCharacterParameter F G)
  let e : (Fin d → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F G :=
    (Module.finBasis ℂ (ComplexCharacterParameter F G)).equivFun.symm
  let T := ((e.symm.toLinearMap).restrictScalars ℝ).comp L
  have hcont : ContinuousOn (E ∘ e) (e ⁻¹' D) :=
    (differentiableOn_of_isHolomorphicOn (hE.2 d e).2.2.1).continuousOn
  have hTe (x : X) : e (T x) = L x := e.apply_symm_apply _
  have hm : MapsTo T (univ : Set X) (e ⁻¹' D) := fun x _ => by
    change e (T x) ∈ D
    rw [hTe]
    exact hL x
  have heq : (E ∘ e) ∘ T.toContinuousLinearMap = fun x => E (L x) := by
    funext x
    change E (e (T x)) = E (L x)
    rw [hTe]
  rw [← heq]
  exact continuousOn_univ.mp (hcont.comp T.toContinuousLinearMap.continuous.continuousOn hm)

end SpectralCharts

section Packets

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} {K : Subgroup (AdelicGroupPoints F G)}
  (r : ParabolicRootPresentation p l a) (hK : IsIwasawaCompact p K)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

local notation "Z₀" => canonicalTorus F G
local notation "i₀" => canonicalComponent F G
local notation "hZG" => isSplitComponent_canonicalComponent F G
local notation "hc₀" => IsCentralSplitTorus.isCentral (IsSplitComponent.isCentralSplitTorus hZG)
local notation "ACentre" => intrinsicSubgroup F Z₀
local notation "Yrel" => CanonicalQuotient F G

private theorem relativeContinuation_leftInvariant (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (heq : IsSplitComponentEquivariant p l φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK.eisensteinSeries φ lam)
    (x : relativeParameterSpace (F := F) p) (hxD : imaginaryParameter F P x.val ∈ D) :
    IsLeftInvariantUnder F G (canonicalRationalSubgroup F G) (E (imaginaryParameter F P x.val)) := by
  apply LeftCosetSpace.invariant_sup (canonicalSubgroup F G)
    (Δ := AdelicGroupPoints.rationalSubgroup F G)
  · intro b hb g
    rw [canonicalSubgroup_eq_imageSubgroup] at hb
    obtain ⟨z, hz, rfl⟩ := hb
    have hid : IsClosedSubgroup (𝟙 G) := by
      change IsClosedImmersion (𝟙 G.X.left)
      infer_instance
    let j : (Z₀).toGrp ⟶ M := r.intermediateCentralFactor (𝟙 G) hid (l ≫ p)
      (Category.comp_id _) i₀ hc₀
    have hj : j ≫ l ≫ p = i₀ :=
      r.intermediateCentralFactor_comp (𝟙 G) hid (l ≫ p) (Category.comp_id _) i₀ hc₀
    have hZ := (hZG).isCentralSplitTorus.isSplitSubtorus.1
    let z₀ : ACentre := ⟨z, hz⟩
    have hm : map F P G p (map F (Z₀).toGrp P (j ≫ l) z) ∈ canonicalSubgroup F G := by
      rw [← map_comp_apply_of_hom, Category.assoc, hj, canonicalSubgroup_eq_imageSubgroup]
      exact ⟨z, hz, rfl⟩
    have hx : ∀ q : AdelicGroupPoints F P, map F P G p q ∈ canonicalSubgroup F G →
        realParameterPairing F P x.val (characterLog F P q) = 0 := by
      simpa only [relativeParameterSpace, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] using x.property
    have hpow : parameterPower F (Z₀).toGrp (parameterRestrict (j ≫ l)
        (imaginaryParameter F P x.val)) z = 1 := by
      rw [parameterPower_parameterRestrict, parameterPower, pairing_imaginary, hx _ hm,
        Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    have hh := eisensteinContinuation_splitCentre_mul hK r hA hT hG heq hE hreg
      hZ hc₀ j hj z₀ hxD g
    change E (imaginaryParameter F P x.val) (map F (Z₀).toGrp G i₀ z * g) =
      parameterPower F (Z₀).toGrp (parameterRestrict (j ≫ l) (imaginaryParameter F P x.val)) z * _ at hh
    rw [hpow, one_mul] at hh
    exact hh
  · exact eisensteinContinuation_leftRationalInvariant hK hφ hU r hA hT hG hE hreg hxD

set_option maxHeartbeats 1800000 in
private theorem exists_relativeWavePacket_centreIntegral
    (hShift : EisensteinContinuationAmbientShiftStatement.{0}) (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {I : Type} [Fintype I] (eSplit : (Z₀).toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I)
    {S : Set ACentre} (hSf : centreQuotientHaar F G hG (I := I) eSplit S < ⊤)
    {N d : ℕ} {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {hcalc : AdelicDifferentialCommutator F G hsmooth}
    {Θ : AdelicGroupPoints F G → ℂ}
    (hΘ : IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ) :
    ∃ Ψ : AdelicGroupPoints F G → ℂ,
      IsRelativeWavePacket hK rho hsmooth hcalc iU l r hA hT Ψ ∧
      ∀ y : Yrel, Ψ y.out = ∫ b in S, Θ ((centreQuotientCoordinates F G hG (I := I) eSplit (b, y)).out)
          ∂(centreQuotientHaar F G hG (I := I) eSplit) := by
  obtain ⟨h, e, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘ⟩ := hΘ
  let muS := (centreQuotientHaar F G hG (I := I) eSplit).restrict S
  let : Fact (centreQuotientHaar F G hG (I := I) eSplit S < ⊤) := ⟨hSf⟩
  let : SecondCountableTopology ACentre := positiveSecondCountableTopology F Z₀ I eSplit
  let : FiniteDimensional ℝ (RealCharacterParameter F P) := e.finiteDimensional
  let n := Module.finrank ℝ (relativeParameterSpace (F := F) p)
  let m := Module.finrank ℝ (RealCharacterParameter F G)
  let eRel : (Fin n → ℝ) ≃ₗ[ℝ] relativeParameterSpace (F := F) p :=
    (Module.finBasis ℝ (relativeParameterSpace (F := F) p)).equivFun.symm
  let eG : (Fin m → ℝ) ≃ₗ[ℝ] RealCharacterParameter F G := ambientParameterChart hG
  let eProd := (eRel.prodCongr eG).trans (relativeAmbientParameterEquiv r hG)
  let L : (Fin h → ℝ) ≃L[ℝ] ((Fin n → ℝ) × (Fin m → ℝ)) :=
    (e.trans eProd.symm).toContinuousLinearEquiv
  obtain ⟨scale, hscale⟩ := spectralMeasure_map_to_product L
  let coeff (j : Fin k) (z : (Fin n → ℝ) × (Fin m → ℝ)) := c j (L.symm z)
  have hcoeff (j : Fin k) : ContDiff ℝ (⊤ : ℕ∞) (coeff j) :=
    (hc j).1.comp L.symm.toContinuousLinearMap.contDiff
  have hcompact (j : Fin k) : HasCompactSupport (coeff j) := by
    apply HasCompactSupport.intro ((hc j).2.image L.continuous)
    intro z hz
    by_contra hn
    exact hz ⟨L.symm z, subset_tsupport _ hn, L.apply_symm_apply z⟩
  let phase (bz : ACentre × (Fin m → ℝ)) : ℂ :=
    parameterPower F G (imaginaryParameter F G (eG bz.2)) (positivePointMap F G Z₀ i₀ bz.1)
  have hphase : Continuous phase :=
    continuous_parameterPower_in_imaginary_chart (positivePointMap F G Z₀ i₀).continuous eG
  have hbound (bz : ACentre × (Fin m → ℝ)) : ‖phase bz‖ ≤ 1 :=
    (parameterPower_imaginary_norm _ _).le
  let profile (z : Fin m → ℝ) := ∫ b, phase (b, z) ∂muS
  have hprofile : Continuous profile := continuous_centre_integral hphase hbound
  let c₀ (j : Fin k) (x : Fin n → ℝ) := ∫ z, profile z * coeff j (x, z) ∂(spectralMeasure m)
  let cRel (j : Fin k) (x : Fin n → ℝ) := (scale : ℝ) • c₀ j x
  have hRel (j : Fin k) : ContDiff ℝ (⊤ : ℕ∞) (cRel j) ∧ HasCompactSupport (cRel j) := by
    have hb := smooth_compact_integrated_coefficient (muZ := spectralMeasure m)
      (hcoeff j) (hcompact j) hprofile
    exact ⟨hb.1.const_smul (scale : ℝ),
      HasCompactSupport.smul_left (f := fun (_ : Fin n → ℝ) => (scale : ℝ)) hb.2⟩
  let lam (x : Fin n → ℝ) := imaginaryParameter F P (eRel x).val
  let Ψ (g : AdelicGroupPoints F G) := ∫ x, ∑ j, cRel j x * E j (lam x) g ∂(spectralMeasure n)
  refine ⟨Ψ, ⟨n, eRel, k, v, cRel, E, D, hv, hRel, hD, hE, hreg, rfl⟩, ?_⟩
  intro y
  let value (j : Fin k) (x : Fin n → ℝ) := E j (lam x) y.out
  have hvalue (j : Fin k) : Continuous (value j) := continuous_meromorphic_real_linear (hE j y.out)
    (((imaginaryParameter F P).comp (relativeParameterSpace (F := F) p).subtype).comp eRel.toLinearMap)
    (fun x => hD (mem_range_self (eRel x).val))
  let n₀ : normOneSubgroup F G := ((canonicalNormOneQuotientHomeomorph F G hG).symm y).out
  let g (b : ACentre) : AdelicGroupPoints F G := positivePointMap F G Z₀ i₀ b * n₀.val
  let fullLam (z : (Fin n → ℝ) × (Fin m → ℝ)) := imaginaryParameter F P (e (L.symm z))
  have hsplit (z : (Fin n → ℝ) × (Fin m → ℝ)) :
      fullLam z = lam z.1 + parameterRestrict p (imaginaryParameter F G (eG z.2)) := by
    have hL : e (L.symm z) = eProd z := e.apply_symm_apply _
    change imaginaryParameter F P (e (L.symm z)) = _
    rw [hL]
    exact imaginaryParameter_relativeAmbientParameterEquiv r hG (eRel z.1) (eG z.2)
  have hEval (j : Fin k) (b : ACentre) (z : (Fin n → ℝ) × (Fin m → ℝ)) :
      E j (fullLam z) ((centreQuotientCoordinates F G hG (I := I) eSplit (b, y)).out) =
        phase (b, z.2) * value j z.1 := by
    have hrelLam : lam z.1 ∈ D := hD (mem_range_self _)
    have hfull : fullLam z ∈ D := hD (mem_range_self _)
    have hrational := eisensteinContinuation_leftRationalInvariant hK (hv j).1.1 hU r hA hT hG
      (hE j) (hreg j) hfull
    rw [centreQuotientCoordinates_apply F G hG (I := I) eSplit,
      LeftCosetSpace.out_mk_of_invariant _ _ hrational]
    change E j (fullLam z) (g b) = _
    have hshift := hShift F G P M A p l a r hA hT hG K hK (v j) (g b)
      (fun w => E j w (g b)) D (hE j (g b))
      (by obtain ⟨R, hR⟩ := hreg j; exact ⟨R, fun w _ hw => congrFun (hR w hw) (g b)⟩)
      (imaginaryParameter F G (eG z.2)) (parameterRealPart_imaginaryParameter _)
      (lam z.1) hrelLam (hsplit z ▸ hfull)
    rw [hsplit, hshift]
    have hp : parameterPower F G (imaginaryParameter F G (eG z.2)) (g b) = phase (b, z.2) := by
      dsimp only [g]
      rw [InducedInnerProductIntegrable.parameterPower_mul,
        InducedInnerProductIntegrable.parameterPower_of_characterLog_eq_zero _
          ((characterLog_eq_zero_iff F G n₀.val).mpr n₀.property), mul_one]
    have hinv := relativeContinuation_leftInvariant r hK hA hT hG hU (hv j).1.1 (hv j).2.1
      (hE j) (hreg j) (eRel z.1) hrelLam
    have hb : positivePointMap F G Z₀ i₀ b ∈ canonicalRationalSubgroup F G := by
      apply Subgroup.mem_sup_left
      change positivePointMap F G Z₀ i₀ b ∈ canonicalSubgroup F G
      rw [canonicalSubgroup_eq_imageSubgroup]
      exact ⟨b.val, b.property, rfl⟩
    rw [hp]
    congr 1
    change E j (lam z.1) (positivePointMap F G Z₀ i₀ b * n₀.val) = E j (lam z.1) y.out
    rw [hinv _ hb, ← normOneRep_mk_canonical F G hG y,
      LeftCosetSpace.out_mk_of_invariant _ _ hinv]
  have hpacket (b : ACentre) :
      Θ ((centreQuotientCoordinates F G hG (I := I) eSplit (b, y)).out) =
        (scale : ℝ) • (∫ z, ∑ j, phase (b, z.2) * coeff j z * value j z.1
          ∂((spectralMeasure n).prod (spectralMeasure m))) := by
    rw [hΘ]
    let Q (z : (Fin n → ℝ) × (Fin m → ℝ)) := ∑ j, phase (b, z.2) * coeff j z * value j z.1
    calc
      _ = ∫ x, Q (L x) ∂(spectralMeasure h) := by
        apply integral_congr_ae (Eventually.of_forall fun x => ?_)
        apply Finset.sum_congr rfl
        intro j _
        have hl : fullLam (L x) = imaginaryParameter F P (e x) := by
          dsimp only [fullLam]
          rw [L.symm_apply_apply]
        rw [← hl, hEval j b (L x)]
        have hcoeffx : coeff j (L x) = c j x := congrArg (c j) (L.symm_apply_apply x)
        rw [hcoeffx]
        ring
      _ = ∫ z, Q z ∂(Measure.map L (spectralMeasure h)) :=
        (integral_map_equiv L.toHomeomorph.toMeasurableEquiv Q).symm
      _ = _ := by rw [hscale, integral_smul_nnreal_measure, NNReal.smul_def]
  change Ψ y.out = ∫ b, Θ ((centreQuotientCoordinates F G hG (I := I) eSplit (b, y)).out) ∂muS
  simp_rw [hpacket]
  rw [integral_smul]
  rw [centre_spectral_integral (fun j => (hcoeff j).continuous) hcompact hvalue hphase hbound]
  rw [← integral_smul]
  apply integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [cRel, c₀, profile, value, Finset.smul_sum, smul_mul_assoc]

end Packets

end WavePacketCentreCompression

open GroupScheme AdelicGroupPoints RestrictionSplitCentre PositiveRealTorus
  Langlands.Automorphic.GroupSchemeFunctions WavePacketCentreCompression

/-- Completeness on the full rational quotient with full packets of the presented parabolics
above the specified minimal parabolic as the tests. -/
def StandardWavePacketCompletenessStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    ∀ f : RationalQuotient F G → ℂ, MemLp f 2 (rationalQuotientHaarMeasure F G) →
      (∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
        (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
        [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
        LeviSubgroup.IsGeometricUnipotentRadical iU →
        ∀ (hK : IsIwasawaCompact p K) (Θ : AdelicGroupPoints F G → ℂ),
          IsParabolicWavePacket hK rho hsmooth hcalc iU l r hA hT Θ →
          ∫ y, f y * conj (Θ y.out) ∂rationalQuotientHaarMeasure F G = 0) →
      f =ᵐ[rationalQuotientHaarMeasure F G] 0

/-- Full packets are square integrable for the rational quotient Haar measure. -/
def WavePacketSquareIntegrabilityStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
      (_ : IsClosedImmersion p₀.hom.hom.left),
      IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ Θ : AdelicGroupPoints F G → ℂ, IsWavePacket F G K rho hsmooth hcalc Θ →
      MemLp (fun y : RationalQuotient F G => Θ y.out) 2 (rationalQuotientHaarMeasure F G)

/-- Exponent zero in the rapid decay estimate gives square integrability. -/
theorem wavePacketSquareIntegrability_of_rapidDecay (hDecay : WavePacketRapidDecayStatement) :
    WavePacketSquareIntegrabilityStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho hminData Θ hΘ
  simpa only [pow_zero, mul_one, rationalQuotientHaarMeasure,
    LeftCosetSpace.haarQuotientMeasure] using
    hDecay F G hG K rho hsmooth hcalc hKmax hrho hminData Θ hΘ 0

set_option maxHeartbeats 1400000 in
/-- Transfer completeness by lifting the orthogonal function with the indicator of a central
set of positive finite measure. The central integral of every full test is one relative test. -/
theorem relativeWavePacketCompleteness_of_standard_of_squareIntegrable
    (hFull : StandardWavePacketCompletenessStatement) (hSquare : WavePacketSquareIntegrabilityStatement)
    (hShift : EisensteinContinuationAmbientShiftStatement.{0}) : RelativeWavePacketCompletenessStatement := by
  intro F _ _ G _ _ _ hG K N d rho hsmooth hcalc hKmax hrho P₀ _ p₀ hp₀ hmin hK₀ f hf hOrth
  let Z := canonicalTorus F G
  let i := canonicalComponent F G
  have hZ := (isSplitComponent_canonicalComponent F G).isCentralSplitTorus
  obtain ⟨I, hI, ⟨e⟩⟩ := hZ.isSplitSubtorus.1
  let : Fintype I := Fintype.ofFinite I
  let := canonical_finiteIndex F G hG
  let hi := canonical_characterRestrict_injective F G centralSplitTorusCharacter hG
  let muA := centreQuotientHaar F G hG (I := I) e
  let muY := canonicalMeasure F G
  let muFull := rationalQuotientHaarMeasure F G
  let : SigmaFinite muA := normalizedPositiveHaarMeasure_sigmaFinite F G Z i hi I e hZ.isCentral
  let : muA.IsHaarMeasure := normalizedPositiveHaarMeasure_isHaarMeasure F G Z i hi I e hZ.isCentral
  let : IsFiniteMeasure muY := connectedReductiveQuotientFiniteVolume F G hG _ _
    (isSplitComponent_canonicalRestrictionComponent F G)
  obtain ⟨b, hb⟩ := (Measure.exists_measure_inter_spanningSets_pos («μ» := muA) univ).mpr
    (isOpen_univ.measure_pos muA univ_nonempty)
  let S := spanningSets muA b
  have hS : MeasurableSet S := measurableSet_spanningSets muA b
  have hSf : muA S < ⊤ := measure_spanningSets_lt_top muA b
  have hSne : muA S ≠ 0 := ne_of_gt (by simpa only [univ_inter] using hb)
  let eQ := centreQuotientCoordinates F G hG (I := I) e
  have hQ : MeasurePreserving eQ (muA.prod muY) muFull :=
    measurePreserving_centreQuotientCoordinates F G hG (I := I) e
  let fprod : intrinsicSubgroup F Z × CanonicalQuotient F G → ℂ :=
    (S ×ˢ univ).indicator (fun q => f q.2)
  let fFull : RationalQuotient F G → ℂ := fprod ∘ eQ.symm
  have hfprod : MemLp fprod 2 (muA.prod muY) := memLp_indicator_snd hS hSf hf
  have hfFull : MemLp fFull 2 muFull := hfprod.comp_measurePreserving (hQ.symm (e := eQ))
  have hminData : ∃ (Q : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine Q.X.left)
      (q : Q ⟶ G) (_ : IsClosedImmersion q.hom.hom.left),
      IsMinimalParabolicSubgroup q ∧ IsIwasawaCompact q K := ⟨P₀, inferInstance, p₀, hp₀, hmin, hK₀⟩
  have hFullZero : fFull =ᵐ[muFull] 0 := by
    apply hFull F G hG K rho hsmooth hcalc hKmax hrho P₀ p₀ hmin hK₀ fFull hfFull
    intro P M U A _ _ _ _ p hp iU l a r _ _ _ hA hT hle hU hK Θ hW
    let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType (j := p) hp
    have hUp : IsClosedImmersion (iU ≫ p).hom.hom.left := hU.1.isClosedSubgroup.comp hp
    have hΘ : IsWavePacket F G K rho hsmooth hcalc Θ := by
      obtain ⟨n, eP, k, v, c, E, D, hv, hc, hD, hE, hreg, hΘ⟩ := hW
      exact ⟨P, M, U, A, inferInstance, inferInstance, inferInstance, inferInstance, p, hp, iU, l,
        hUp, a, r, inferInstance, inferInstance, inferInstance, hA, hT, hU, hK, n, eP, k, v, c, E, D,
        hv, hc, hD, hE, hreg, hΘ⟩
    have hL : MemLp (fun y : RationalQuotient F G => Θ y.out) 2 muFull :=
      hSquare F G hG K rho hsmooth hcalc hKmax hrho hminData Θ hΘ
    let w (q : intrinsicSubgroup F Z × CanonicalQuotient F G) : ℂ := Θ ((eQ q).out)
    have hw : MemLp w 2 (muA.prod muY) := hL.comp_measurePreserving hQ
    obtain ⟨Ψ, hΨ, hrepr⟩ := exists_relativeWavePacket_centreIntegral r hK hA hT hShift hG hU
      (I := I) e hSf hW
    have hΨL : MemLp (fun y : CanonicalQuotient F G => Ψ y.out) 2 muY := by
      simp_rw [hrepr]
      exact memLp_integral_centre hSf hw
    calc
      _ = ∫ q, fprod q * conj (w q) ∂(muA.prod muY) := by
        rw [← hQ.integral_comp eQ.measurableEmbedding]
        simp only [fFull, Function.comp_apply, w, MeasurableEquiv.symm_apply_apply]
      _ = ∫ y, f y * conj (Ψ y.out) ∂muY := by
        rw [integral_indicator_mul_conj hS hSf hf hw]
        simp only [hrepr, w, eQ, muA, muY]
      _ = 0 := hOrth P M U A p iU l a r hA hT hle hU hK Ψ hΨ hΨL
  have hProdZero : fprod =ᵐ[muA.prod muY] 0 := by
    filter_upwards [hQ.quasiMeasurePreserving.ae_eq_comp hFullZero] with q hq
    simpa only [fFull, Function.comp_apply, MeasurableEquiv.symm_apply_apply, Pi.zero_apply] using hq
  exact ae_eq_zero_of_indicator_snd hS hSf hSne hProdZero

/-- Completeness for the standard family on the full quotient, rapid decay of full packets,
and the imaginary ambient shift imply completeness on the canonical quotient. -/
def RelativeWavePacketCompletenessTransferStatement : Prop :=
  StandardWavePacketCompletenessStatement → WavePacketRapidDecayStatement →
    EisensteinContinuationAmbientShiftStatement.{0} → RelativeWavePacketCompletenessStatement

/-- Transfer completeness using the square integrability consequence of rapid decay. -/
theorem relativeWavePacketCompleteness_of_standard : RelativeWavePacketCompletenessTransferStatement :=
  fun hFull hDecay =>
    relativeWavePacketCompleteness_of_standard_of_squareIntegrable hFull
      (wavePacketSquareIntegrability_of_rapidDecay hDecay)

end Langlands.Global

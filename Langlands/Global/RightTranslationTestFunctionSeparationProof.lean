import Langlands.Global.AdelicWavePacketTranslationReduction
import Langlands.Global.AdelicRationalQuotientL2RightAction
import Langlands.Global.FiniteAdelicGroupCompactOpenBasisProof
import Langlands.Analysis.CompactSubgroupAverageDuality
import Langlands.Global.AdelicArchimedeanFiniteWeights
import Langlands.Analysis.Local.CompactTestSeparationProof

/-! # Separation of right translates by left-finite adelic test functions

Proof of `Langlands.Global.RightTranslationTestFunctionSeparationStatement`. For
`f ∈ L²([G])` and a left `G(F)`-invariant `Θ` with `y ↦ Θ(y.out)` in `L²([G])`, the translate
pairing `Φ(h) = ∫ f(y) conj Θ(y.out h) dμG` is continuous on `G(𝔸)` (strong continuity of the
right regular representation on `L²([G])`). Fubini's theorem identifies the pairing of `f`
with `R(φ)Θ` with `∫ conj φ · Φ`. Averaging a compactly supported continuous function over
the archimedean part of `K` with a finite left-translation weight and then over a small compact
open subgroup of `G(𝔸_f)` gives left-finite test functions; with the density of finite weights
(Stone–Weierstrass) and the continuity of `Φ` this forces `Φ = 0`. A measure-preserving
substitution `y ↦ y g⁻¹` concludes. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj CompactlySupported ComplexConjugate

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

local notation "H" => AdelicGroupPoints F G
local notation "Q" => RationalQuotient F G
local notation "Γ" => rationalSubgroup F G
local notation "μQ" => rationalQuotientHaarMeasure F G
local notation "μH" => (Measure.haar : Measure (AdelicGroupPoints F G))

section Quotient

theorem rationalQuotient_rightTranslate_eq_mk_out_mul (h : H) (y : Q) :
    LeftCosetSpace.rightTranslate Γ h y = LeftCosetSpace.mk Γ (y.out * h) := by
  conv_lhs => rw [← Quotient.out_eq y]
  rfl

theorem rationalQuotient_mk_out (y : Q) : LeftCosetSpace.mk Γ y.out = y := Quotient.out_eq y

/-- A left `G(F)`-invariant function takes the same value at a point and at the chosen
representative of its class. -/
theorem leftInvariant_mk_out {Θ : H → ℂ} (hΘ : IsLeftInvariantUnder F G Γ Θ) (z : H) :
    Θ (LeftCosetSpace.mk Γ z).out = Θ z := by
  have hz : LeftCosetSpace.mk Γ z = LeftCosetSpace.mk Γ (LeftCosetSpace.mk Γ z).out :=
    (rationalQuotient_mk_out _).symm
  have hmem := (LeftCosetSpace.mk_eq_mk_iff Γ _ _).mp hz
  calc Θ (LeftCosetSpace.mk Γ z).out
      = Θ (((LeftCosetSpace.mk Γ z).out * z⁻¹) * z) := by rw [inv_mul_cancel_right]
    _ = Θ z := hΘ _ hmem z

/-- Null sets of the quotient measure pull back to Haar-null sets of `G(𝔸)`. -/
theorem haar_preimage_mk_eq_zero {Z : Set Q} (hZ : μQ Z = 0) :
    μH (LeftCosetSpace.mk Γ ⁻¹' Z) = 0 := by
  let hΓ := isDiscrete_rationalSubgroup F G
  set Z' := toMeasurable μQ Z
  have hZ'm : MeasurableSet Z' := measurableSet_toMeasurable _ _
  have hZ'0 : μQ Z' = 0 := by rw [measure_toMeasurable]; exact hZ
  apply measure_mono_null (preimage_mono (subset_toMeasurable μQ Z))
  have hD := LeftCosetSpace.isFundamentalDomain Γ hΓ μH
  apply hD.measure_zero_of_invariant
  · intro g₀
    refine Set.ext fun z => ?_
    rw [mem_smul_set_iff_inv_smul_mem, mem_preimage, mem_preimage]
    have : LeftCosetSpace.mk Γ (g₀⁻¹ • z) = LeftCosetSpace.mk Γ z :=
      LeftCosetSpace.mk_subgroup_mul Γ g₀⁻¹ z
    rw [this]
  · have h1 : μQ Z' = μH (LeftCosetSpace.mk Γ ⁻¹' Z' ∩ LeftCosetSpace.fundamentalDomain Γ hΓ) :=
      LeftCosetSpace.quotientMeasure_apply Γ μH _ hZ'm
    rw [← h1, hZ'0]

variable (hred : IsConnectedReductive G)
include hred

theorem haar_isMulRightInvariant_of_connectedReductive : (μH).IsMulRightInvariant :=
  (adelicHaarUnimodularity.{0}).2 F G hred

theorem measurePreserving_rationalQuotient_rightTranslate (h : H) :
    MeasurePreserving (LeftCosetSpace.rightTranslate Γ h) μQ μQ := by
  let := haar_isMulRightInvariant_of_connectedReductive hred
  exact measurePreserving_rightTranslate_rationalQuotientHaarMeasure F G h

omit hred in
/-- Right translation by `h` as a measurable equivalence of the quotient. -/
def rationalQuotientRightTranslateEquiv (h : H) : Q ≃ᵐ Q where
  toFun := LeftCosetSpace.rightTranslate Γ h
  invFun := LeftCosetSpace.rightTranslate Γ h⁻¹
  left_inv q := by
    rw [LeftCosetSpace.rightTranslate_mul, mul_inv_cancel, LeftCosetSpace.rightTranslate_one]
  right_inv q := by
    rw [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel, LeftCosetSpace.rightTranslate_one]
  measurable_toFun := LeftCosetSpace.measurable_rightTranslate Γ h
  measurable_invFun := LeftCosetSpace.measurable_rightTranslate Γ h⁻¹

theorem measurePreserving_rationalQuotientRightTranslateEquiv (h : H) :
    MeasurePreserving (rationalQuotientRightTranslateEquiv h) μQ μQ :=
  measurePreserving_rationalQuotient_rightTranslate hred h

end Quotient

section Pairing

/-- The pairing `Φ(h) = ∫ f(y) conj Θ(y.out h) dμQ` of `f` with the right translate of `Θ` by
`h`. -/
def translatePairing (f : Q → ℂ) (Θ : H → ℂ) (h : H) : ℂ :=
  ∫ y, f y * conj (Θ (y.out * h)) ∂μQ

/-- A strongly measurable representative of an `L²` function on the quotient. -/
abbrev borelRep {θ : Q → ℂ} (hθ : MemLp θ 2 μQ) : Q → ℂ := hθ.aestronglyMeasurable.mk θ

variable (hred : IsConnectedReductive G) {f : RationalQuotient F G → ℂ}
  (hf : MemLp f 2 (rationalQuotientHaarMeasure F G)) {Θ : AdelicGroupPoints F G → ℂ}
  (hΘ : IsLeftInvariantUnder F G (rationalSubgroup F G) Θ)
  (hθ : MemLp (fun y : RationalQuotient F G => Θ y.out) 2 (rationalQuotientHaarMeasure F G))

include hred hf hΘ hθ in
theorem translatePairing_eq_inner (h : H) :
    translatePairing f Θ h =
      inner ℂ (rationalQuotientL2RightAction hred h (hθ.toLp _)) (hf.toLp f) := by
  rw [MeasureTheory.L2.inner_def]
  unfold translatePairing
  apply integral_congr_ae
  have h1 := coeFn_rationalQuotientL2RightAction hred h (hθ.toLp _)
  have h2 : (fun x : Q => (hθ.toLp _ : Q → ℂ) (LeftCosetSpace.mk Γ (x.out * h))) =ᵐ[μQ]
      fun x => Θ (x.out * h) := by
    have hq := (measurePreserving_rationalQuotient_rightTranslate hred h).quasiMeasurePreserving
    have := hq.ae_eq_comp (MemLp.coeFn_toLp hθ)
    filter_upwards [this] with x hx
    simp only [Function.comp_apply, rationalQuotient_rightTranslate_eq_mk_out_mul] at hx
    rw [hx, leftInvariant_mk_out hΘ]
  filter_upwards [h1, h2, MemLp.coeFn_toLp hf] with x hx1 hx2 hx3
  rw [hx1, hx2, hx3, RCLike.inner_apply]

include hred hf hΘ hθ in
theorem continuous_translatePairing : Continuous (translatePairing f Θ) := by
  have : translatePairing f Θ = fun h =>
      inner ℂ (rationalQuotientL2RightAction hred h (hθ.toLp _)) (hf.toLp f) :=
    funext (translatePairing_eq_inner hred hf hΘ hθ)
  rw [this]
  exact ((continuous_rationalQuotientL2RightAction hred).comp
    (continuous_id.prodMk continuous_const)).inner continuous_const

include hΘ hθ in
theorem ae_leftInvariant_eq_borelRep (x : H) :
    ∀ᵐ h ∂μH, Θ (x * h) = borelRep hθ (LeftCosetSpace.mk Γ (x * h)) := by
  have hZ : μQ {y | Θ y.out ≠ borelRep hθ y} = 0 := by
    have := hθ.aestronglyMeasurable.ae_eq_mk
    rwa [Filter.EventuallyEq, ae_iff] at this
  have h0 := haar_preimage_mk_eq_zero hZ
  rw [ae_iff]
  have : {h | ¬ Θ (x * h) = borelRep hθ (LeftCosetSpace.mk Γ (x * h))} =
      (fun h => x * h) ⁻¹' (LeftCosetSpace.mk Γ ⁻¹' {y | Θ y.out ≠ borelRep hθ y}) := by
    refine Set.ext fun h => ?_
    change ¬ Θ (x * h) = borelRep hθ (LeftCosetSpace.mk Γ (x * h)) ↔
      Θ (LeftCosetSpace.mk Γ (x * h)).out ≠ borelRep hθ (LeftCosetSpace.mk Γ (x * h))
    rw [leftInvariant_mk_out hΘ]
  rw [this, measure_preimage_mul]
  exact h0

include hred hf hΘ hθ in
theorem translatePairing_eq_borelRep (h : H) :
    translatePairing f Θ h = ∫ y, borelRep hf y *
      conj (borelRep hθ (LeftCosetSpace.rightTranslate Γ h y)) ∂μQ := by
  apply integral_congr_ae
  have hq := (measurePreserving_rationalQuotient_rightTranslate hred h).quasiMeasurePreserving
  have h2 := hq.ae_eq_comp hθ.aestronglyMeasurable.ae_eq_mk
  filter_upwards [hf.aestronglyMeasurable.ae_eq_mk, h2] with y hy1 hy2
  simp only [Function.comp_apply] at hy2
  rw [hy1, ← leftInvariant_mk_out hΘ (y.out * h), ← rationalQuotient_rightTranslate_eq_mk_out_mul, hy2]

omit [IsAffineHom G.X.hom] in
theorem continuous_rationalQuotient_rightTranslate_uncurry :
    Continuous fun p : Q × H => LeftCosetSpace.rightTranslate Γ p.2 p.1 :=
  (continuous_smul.comp ((MulOpposite.continuous_op.comp continuous_snd).prodMk continuous_fst) :
    Continuous fun p : Q × H => MulOpposite.op p.2 • p.1)

include hred hf hΘ hθ in
/-- Fubini's theorem: pairing `f` with the right convolution `R(φ)Θ` equals integrating
`conj φ` against the translate pairing. -/
theorem integral_mul_conj_rightConvolution {φ : H → ℂ} (hφ : Continuous φ)
    (hφc : HasCompactSupport φ) :
    ∫ y, f y * conj (rightConvolution F G φ Θ y.out) ∂μQ =
      ∫ h, conj (φ h) * translatePairing f Θ h ∂μH := by
  set f₀ := borelRep hf with hf₀
  set θ₀ := borelRep hθ with hθ₀
  have hconv : ∀ y : Q, rightConvolution F G φ Θ y.out =
      ∫ h, φ h * θ₀ (LeftCosetSpace.rightTranslate Γ h y) ∂μH := by
    intro y
    apply integral_congr_ae
    filter_upwards [ae_leftInvariant_eq_borelRep hΘ hθ y.out] with h hh
    rw [hh, ← rationalQuotient_rightTranslate_eq_mk_out_mul]
  let J : Q → H → ℂ := fun y h =>
    f₀ y * (conj (φ h) * conj (θ₀ (LeftCosetSpace.rightTranslate Γ h y)))
  have hJm : StronglyMeasurable (Function.uncurry J) := by
    apply StronglyMeasurable.mul
    · exact hf.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable measurable_fst
    · apply StronglyMeasurable.mul
      · exact Complex.continuous_conj.comp_stronglyMeasurable
          (hφ.comp continuous_snd).stronglyMeasurable
      · exact Complex.continuous_conj.comp_stronglyMeasurable
          (hθ.aestronglyMeasurable.stronglyMeasurable_mk.comp_measurable continuous_rationalQuotient_rightTranslate_uncurry.measurable)
  have hf₀2 : MemLp f₀ 2 μQ := hf.ae_eq hf.aestronglyMeasurable.ae_eq_mk
  have hθ₀2 : MemLp θ₀ 2 μQ := hθ.ae_eq hθ.aestronglyMeasurable.ae_eq_mk
  have htr2 (h : H) : MemLp (fun y => θ₀ (LeftCosetSpace.rightTranslate Γ h y)) 2 μQ :=
    hθ₀2.comp_measurePreserving (measurePreserving_rationalQuotient_rightTranslate hred h)
  set B : ℝ := (∫ y, ‖f₀ y‖ ^ (2 : ℝ) ∂μQ) ^ (1 / (2 : ℝ)) *
    (∫ y, ‖θ₀ y‖ ^ (2 : ℝ) ∂μQ) ^ (1 / (2 : ℝ))
  have hbound (h : H) :
      ∫ y, ‖f₀ y‖ * ‖θ₀ (LeftCosetSpace.rightTranslate Γ h y)‖ ∂μQ ≤ B := by
    have h2 : ENNReal.ofReal 2 = 2 := by norm_num
    have := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two
      (h2.symm ▸ hf₀2) (h2.symm ▸ htr2 h)
    refine this.trans (le_of_eq ?_)
    congr 2
    exact (measurePreserving_rationalQuotientRightTranslateEquiv hred h).integral_comp'
      (fun y => ‖θ₀ y‖ ^ (2 : ℝ))
  have hJ : Integrable (Function.uncurry J) (Measure.prod μQ μH) := by
    rw [integrable_prod_iff' hJm.aestronglyMeasurable]
    constructor
    · refine Filter.Eventually.of_forall fun h => ?_
      have := hf₀2.integrable_mul ((htr2 h).star.const_mul (conj (φ h)))
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp [J, Pi.mul_apply]
    · have hm : StronglyMeasurable fun h => ∫ y, ‖Function.uncurry J (y, h)‖ ∂μQ :=
        hJm.norm.integral_prod_left'
      refine Integrable.mono' ((hφ.norm.integrable_of_hasCompactSupport hφc.norm).const_mul B)
        hm.aestronglyMeasurable (Filter.Eventually.of_forall fun h => ?_)
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : ∫ y, ‖Function.uncurry J (y, h)‖ ∂μQ =
          ‖φ h‖ * ∫ y, ‖f₀ y‖ * ‖θ₀ (LeftCosetSpace.rightTranslate Γ h y)‖ ∂μQ := by
        rw [← integral_const_mul]
        congr 1
        funext y
        simp only [Function.uncurry_apply_pair, J, norm_mul, Complex.norm_conj]
        ring
      rw [he, mul_comm B]
      exact mul_le_mul_of_nonneg_left (hbound h) (norm_nonneg _)
  calc ∫ y, f y * conj (rightConvolution F G φ Θ y.out) ∂μQ
      = ∫ y, ∫ h, J y h ∂μH ∂μQ := by
        apply integral_congr_ae
        filter_upwards [hf.aestronglyMeasurable.ae_eq_mk] with y hy
        rw [hy, hconv, ← integral_conj, ← integral_const_mul]
        congr 1
        funext h
        simp only [J, map_mul]
        rfl
    _ = ∫ h, ∫ y, J y h ∂μQ ∂μH := integral_integral_swap hJ
    _ = ∫ h, conj (φ h) * translatePairing f Θ h ∂μH := by
        congr 1
        funext h
        rw [translatePairing_eq_borelRep hred hf hΘ hθ h, ← integral_const_mul]
        congr 1
        funext y
        simp only [J]
        ring

end Pairing

section Separation

open Langlands.Analysis.CompactAverage Langlands.CompactRepresentativeWeights
  Langlands.FiniteVectors

/-- The archimedean part `K ∩ G(F_∞)` of a subgroup `K` of `G(𝔸)`. -/
def archimedeanPart (K : Subgroup (AdelicGroupPoints F G)) : Subgroup (AdelicGroupPoints F G) :=
  K ⊓ (ofInfinite F G).toMonoidHom.range

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
theorem finite_eq_one_of_mem_archimedeanPart {K : Subgroup (AdelicGroupPoints F G)} {c : H}
    (hc : c ∈ archimedeanPart K) : finite F G c = 1 := by
  obtain ⟨-, a, rfl⟩ := hc
  exact finite_ofInfinite F G a

omit [IsAffineHom G.X.hom] in
theorem isCompact_archimedeanPart {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsCompact (K : Set H)) : IsCompact (archimedeanPart K : Set H) := by
  have hcl : IsClosed ((ofInfinite F G).toMonoidHom.range : Set H) := by
    have : ((ofInfinite F G).toMonoidHom.range : Set H) = finite F G ⁻¹' {1} := by
      refine Set.ext fun x => ⟨?_, fun hx => ⟨infinite F G x, ?_⟩⟩
      · rintro ⟨a, rfl⟩
        exact finite_ofInfinite F G a
      · change pair F G (infinite F G x) 1 = x
        rw [← (show finite F G x = 1 from hx), pair_projections]
    rw [this]
    exact isClosed_singleton.preimage (finite F G).continuous
  exact hK.inter_right hcl

/-- A continuous function on `G(𝔸)` is zero if its integrals against the conjugates of all
continuous, compactly supported, left `K_∞`-finite functions that are invariant under left
translation by an open subgroup of `G(𝔸_f)` vanish. -/
theorem eq_zero_of_forall_leftFiniteTestFunction {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsCompact (K : Set H)) {Φ : H → ℂ} (hΦ : Continuous Φ)
    (horth : ∀ φ : H → ℂ,
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ →
        ∫ h, conj (φ h) * Φ h ∂μH = 0)
    (h₀ : H) : Φ h₀ = 0 := by
  set C₁ := archimedeanPart K with hC₁def
  have hC₁ : IsCompact (C₁ : Set H) := isCompact_archimedeanPart hK
  have : CompactSpace C₁ := isCompact_iff_compactSpace.mp hC₁
  set ν₁ := compactHaarProbability F G C₁ hC₁
  by_contra hne
  have hε : 0 < ‖Φ h₀‖ / 2 := by
    have := norm_pos_iff.mpr hne
    linarith
  set ε := ‖Φ h₀‖ / 2 with hεdef
  have hU : {l : FiniteAdelicGroupPoints F G | ‖Φ (ofFinite F G l * h₀) - Φ h₀‖ < ε} ∈
      nhds (1 : FiniteAdelicGroupPoints F G) := by
    have hc : Continuous fun l : FiniteAdelicGroupPoints F G =>
        ‖Φ (ofFinite F G l * h₀) - Φ h₀‖ :=
      ((hΦ.comp ((ofFinite F G).continuous.mul continuous_const)).sub continuous_const).norm
    have h0 : ‖Φ (ofFinite F G 1 * h₀) - Φ h₀‖ = 0 := by
      rw [map_one, one_mul, sub_self, norm_zero]
    exact (hc.continuousAt (x := 1)).preimage_mem_nhds (t := Set.Iio ε)
      (by rw [h0]; exact Iio_mem_nhds hε)
  obtain ⟨L, hLc, hLU⟩ := ((finiteAdelicGroupCompactOpenBasis.{0} F G).2).mem_iff.mp hU
  set C₂ : Subgroup H := (L : Subgroup (FiniteAdelicGroupPoints F G)).map
    (ofFinite F G).toMonoidHom with hC₂def
  have hC₂ : IsCompact (C₂ : Set H) := by
    rw [hC₂def, Subgroup.coe_map]
    exact hLc.image (ofFinite F G).continuous
  have : CompactSpace C₂ := isCompact_iff_compactSpace.mp hC₂
  set ν₂ := compactHaarProbability F G C₂ hC₂
  have hcomm : ∀ (c₂ : C₂) (c₁ : C₁), Commute (c₂ : H) (c₁ : H) := by
    rintro ⟨_, l, -, rfl⟩ ⟨c, -, a, rfl⟩
    exact (factors_commute F G a l).symm
  -- the averaged test functions
  have htest : ∀ w ∈ finiteWeights (K := C₁), ∀ ψ : C_c(H, ℂ),
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom)
        (weightedAverage ν₂ (fun _ => (1 : ℂ)) (weightedAverage ν₁ w ψ)) := by
    intro w hw ψ
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact continuous_weightedAverage ν₂ continuous_const
        (continuous_weightedAverage ν₁ w.continuous ψ.continuous)
    · exact hasCompactSupport_weightedAverage ν₂ _
        (hasCompactSupport_weightedAverage ν₁ _ ψ.hasCompactSupport)
    · have : Module.Finite ℂ (orbitSpan leftRegular w) := hw
      let T := averageLinearMap ν₂ ∘ₗ weightLinearMap ν₁ ψ.continuous
      apply Submodule.finiteDimensional_of_le (S₂ := (orbitSpan leftRegular w).map T)
      apply Submodule.span_le.mpr
      rintro _ ⟨k, rfl⟩
      let c₀ : C₁ := ⟨ofInfinite F G k, k.2, k, rfl⟩
      refine ⟨leftRegular c₀⁻¹ w, action_mem_orbitSpan leftRegular c₀⁻¹ w, ?_⟩
      funext h
      change weightedAverage ν₂ (fun _ => (1 : ℂ))
          (weightedAverage ν₁ (leftRegular c₀⁻¹ w) ψ) h =
        weightedAverage ν₂ (fun _ => (1 : ℂ)) (weightedAverage ν₁ w ψ) ((c₀ : H) * h)
      rw [weightedAverage_mul_left_of_commute ν₂ _ _ (fun c => hcomm c c₀)]
      refine congrArg (fun χ => weightedAverage ν₂ (fun _ => (1 : ℂ)) χ h) (funext fun x => ?_)
      rw [weightedAverage_mul_left ν₁]
      refine congrArg (fun a => weightedAverage ν₁ a ψ x) (funext fun c => ?_)
      simp only [leftRegular_apply, inv_inv]
    · refine ⟨(L : Subgroup (FiniteAdelicGroupPoints F G)), L.isOpen, fun l hl h => ?_⟩
      let c₀ : C₂ := ⟨ofFinite F G l, l, hl, rfl⟩
      change weightedAverage ν₂ (fun _ => (1 : ℂ)) _ ((c₀ : H) * h) = _
      rw [weightedAverage_mul_left ν₂]
  -- the dual averages of `Φ`
  set Ψ₁ : H → ℂ := fun z => ∫ c, (starRingEnd ℂ) ((fun _ : C₂ => (1 : ℂ)) c) *
    Φ ((c : H) * z) ∂ν₂ with hΨ₁def
  have hΨ₁ : Continuous Ψ₁ :=
    continuous_integral_mul_left ν₂ (Complex.continuous_conj.comp continuous_const) hΦ
  have hΨ₂zero : ∀ w ∈ finiteWeights (K := C₁),
      ∫ c, (starRingEnd ℂ) (w c) * Ψ₁ ((c : H) * h₀) ∂ν₁ = 0 := by
    intro w hw
    set Ψ₂ : H → ℂ := fun h => ∫ c, (starRingEnd ℂ) (w c) * Ψ₁ ((c : H) * h) ∂ν₁
    have hΨ₂ : Continuous Ψ₂ :=
      continuous_integral_mul_left ν₁ (Complex.continuous_conj.comp w.continuous) hΨ₁
    have hkey : ∀ ψ : C_c(H, ℂ), ∫ h, star (ψ h) * Ψ₂ h ∂μH = 0 := by
      intro ψ
      have d1 := integral_conj_weightedAverage_mul ν₂ μH (a := fun _ => (1 : ℂ)) continuous_const
        (continuous_weightedAverage ν₁ w.continuous ψ.continuous)
        (hasCompactSupport_weightedAverage ν₁ _ ψ.hasCompactSupport) hΦ
      have d2 := integral_conj_weightedAverage_mul ν₁ μH w.continuous ψ.continuous
        ψ.hasCompactSupport hΨ₁
      exact d2.symm.trans (d1.symm.trans (horth _ (htest w hw ψ)))
    have hae := ((Langlands.Analysis.compactTestSeparation.{0} μH Ψ₂
      hΨ₂.locallyIntegrable).2).2 hkey
    exact congrFun ((hΨ₂.ae_eq_iff_eq μH continuous_const).mp hae) h₀
  let Ξ : C(C₁, ℂ) := ⟨fun c => Ψ₁ ((c : H) * h₀), hΨ₁.comp (continuous_subtype_val.mul
    continuous_const)⟩
  have hℓ := (continuous_integral_conj_mul ν₁ Ξ).ext_on
    (dense_archimedean_finiteWeights F G C₁ fun c hc => finite_eq_one_of_mem_archimedeanPart hc)
    continuous_const (fun w hw => hΨ₂zero w hw)
  have hΞ1 : Ψ₁ h₀ = 0 := by
    have := eq_zero_of_integral_conj_mul_self ν₁ Ξ (congrFun hℓ Ξ) 1
    simpa [Ξ] using this
  -- `Φ h₀` is within `ε` of its average over `C₂`, which vanishes
  have hbound : ‖Φ h₀‖ ≤ ε := by
    have hint1 : Integrable (fun _ : C₂ => Φ h₀) ν₂ := integrable_const _
    have hint2 : Integrable (fun c : C₂ => (starRingEnd ℂ) ((fun _ : C₂ => (1 : ℂ)) c) *
        Φ ((c : H) * h₀)) ν₂ :=
      integrable_of_continuous ν₂ (continuous_const.mul
        (hΦ.comp (continuous_subtype_val.mul continuous_const)))
    have he : Φ h₀ = ∫ c : C₂, (Φ h₀ - (starRingEnd ℂ) ((fun _ : C₂ => (1 : ℂ)) c) *
        Φ ((c : H) * h₀)) ∂ν₂ := by
      rw [integral_sub hint1 hint2]
      have : ∫ c : C₂, (starRingEnd ℂ) ((fun _ : C₂ => (1 : ℂ)) c) * Φ ((c : H) * h₀) ∂ν₂ =
          Ψ₁ h₀ := rfl
      rw [this, hΞ1, integral_const, probReal_univ, one_smul, sub_zero]
    rw [he]
    refine (norm_integral_le_of_norm_le_const (C := ε)
      (Filter.Eventually.of_forall fun c => ?_)).trans (by rw [probReal_univ, mul_one])
    obtain ⟨_, l, hl, rfl⟩ := c
    have hlU : ‖Φ (ofFinite F G l * h₀) - Φ h₀‖ < ε := hLU hl
    simp only [map_one, one_mul]
    rw [norm_sub_rev]
    exact hlU.le
  linarith

end Separation

section Assembly

variable (hred : IsConnectedReductive G) {f : RationalQuotient F G → ℂ}
  (hf : MemLp f 2 (rationalQuotientHaarMeasure F G)) {Θ : AdelicGroupPoints F G → ℂ}
  (hΘ : IsLeftInvariantUnder F G (rationalSubgroup F G) Θ)
  (hθ : MemLp (fun y : RationalQuotient F G => Θ y.out) 2 (rationalQuotientHaarMeasure F G))

include hred hf hΘ hθ in
/-- The translate pairing vanishes identically when `f` is orthogonal to every right
convolution of `Θ` by a left-finite test function. -/
theorem translatePairing_eq_zero {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsCompact (K : Set H))
    (horth : ∀ φ : H → ℂ,
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ →
        ∫ y, f y * conj (rightConvolution F G φ Θ y.out) ∂μQ = 0) (h : H) :
    translatePairing f Θ h = 0 :=
  eq_zero_of_forall_leftFiniteTestFunction hK (continuous_translatePairing hred hf hΘ hθ)
    (fun φ hφ => (integral_mul_conj_rightConvolution hred hf hΘ hθ hφ.1 hφ.2.1).symm.trans
      (horth φ hφ)) h

include hred hΘ in
/-- Substituting `y ↦ y g⁻¹` identifies the pairing of the right translate of `f` by `g` with
`Θ` with the translate pairing at `g⁻¹`. -/
theorem integral_rightTranslate_mul_conj (g : H) :
    ∫ y, f (LeftCosetSpace.rightTranslate Γ g y) * conj (Θ y.out) ∂μQ =
      translatePairing f Θ g⁻¹ := by
  rw [← (measurePreserving_rationalQuotientRightTranslateEquiv hred g⁻¹).integral_comp'
    (fun y => f (LeftCosetSpace.rightTranslate Γ g y) * conj (Θ y.out))]
  unfold translatePairing
  congr 1
  funext y
  change f (LeftCosetSpace.rightTranslate Γ g (LeftCosetSpace.rightTranslate Γ g⁻¹ y)) *
      conj (Θ (LeftCosetSpace.rightTranslate Γ g⁻¹ y).out) = f y * conj (Θ (y.out * g⁻¹))
  rw [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel, LeftCosetSpace.rightTranslate_one,
    rationalQuotient_rightTranslate_eq_mk_out_mul, leftInvariant_mk_out hΘ]

end Assembly

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

/-- Separation of right translates by left-finite adelic test functions:
`RightTranslationTestFunctionSeparationStatement` holds. -/
theorem rightTranslationTestFunctionSeparation :
    RightTranslationTestFunctionSeparationStatement := by
  intro F _ _ G _ _ _ hred K hK μG f hf Θ hΘ hθ horth g
  exact (AdelicGroupPoints.integral_rightTranslate_mul_conj hred hΘ g).trans
    (AdelicGroupPoints.translatePairing_eq_zero hred hf hΘ hθ hK.1 horth g⁻¹)

end Langlands.Global

import Langlands.Representation.RankinSelberg.HighlyRamified.CoreModel
import Langlands.Representation.RankinSelberg.HighlyRamified.AdjacentComparison

/-!
# The core of the adjacent-rank step

Jacquet and Shalika 1985, §4.4 (printed pages 327–331), for candidates `π₁, π₂` of rank `m + 3`
and a test `σ` of rank `m + 2`. The candidates come with level-`f` vectors `w₁, w₂` that agree
on the mirabolic subgroup, take the value `1` at the identity, and share a central character
`ω` trivial on `1 + 𝔭^f`. The twist is a quasicharacter `χ`. The other inputs are a test vector
`f'` of `σ` on the shell `N GL_(m+1)(O) ϖ^(-c)`, and the monomial gamma factors
`C(ω_τ) X^(c(m+1))` of `(σ^ι ⊗ χ⁻¹ ∘ det, τ)` for every generic `τ` of rank `m + 1` with a
level-`f` vector. Under these hypotheses every gamma factor of `(π₁ ⊗ χ ∘ det, σ)` equals
every gamma factor of `(π₂ ⊗ χ ∘ det, σ)`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear

universe uF uX

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coreStepFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coreStepValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance coreStepLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance coreStepFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance coreStepFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance coreStepGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance coreStepGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreStepUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance coreStepUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreStepQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance coreStepQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- A model function transforms by the central character under left scalar multiplication. -/
theorem model_scalar_mul {m : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    {N : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier)} {θ : N →* ℂˣ}
    (π : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) V)
    (ω : F.Carrierˣ →* ℂˣ) (hω : Classification.HasGLCentralCharacter F.Carrier (m + 1) π ω)
    (ℓ : functionals N θ π) (w : (coefficientModel π ℓ).toSubmodule) (z : F.Carrierˣ)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    w.val.val (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) z * g) = (ω z : ℂ) * w.val.val g := by
  rw [Matrix.GeneralLinearGroup.scalar_commute]
  exact model_mul_scalar π ω hω ℓ w z g

/-- The core of the adjacent-rank step (Jacquet–Shalika 1985, §4.4). -/
theorem core_gamma_eq (hT1 : WhittakerCompletenessStatement.{uF, uX})
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ0 : F.canonicalTopologicalData.additiveConductor ψ = 0)
    (ν : AdditiveHaarMeasure F.Carrier)
    {m f b c : ℕ} (hf : 0 < f) (hb : 0 < b) (hcb : f + b ≤ c) (hcf : f + f ≤ c)
    {ω : F.Carrierˣ →* ℂˣ} (hω : TrivialOnPrincipalUnits ω f)
    {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    {π₁ : Representation ℂ (Langlands.GeneralLinear (m + 2 + 1) F.Carrier) V₁}
    {π₂ : Representation ℂ (Langlands.GeneralLinear (m + 2 + 1) F.Carrier) V₂}
    (hπ₁ : IsGeneric ψ (m + 2) π₁) (hπ₂ : IsGeneric ψ (m + 2) π₂)
    (hc₁ : Classification.HasGLCentralCharacter F.Carrier (m + 2 + 1) π₁ ω)
    (hc₂ : Classification.HasGLCentralCharacter F.Carrier (m + 2 + 1) π₂ ω)
    (ℓ₁ : glFunctionals ψ (m + 2) π₁) (hℓ₁ : ℓ₁.val ≠ 0)
    (ℓ₂ : glFunctionals ψ (m + 2) π₂) (hℓ₂ : ℓ₂.val ≠ 0)
    (w₁ : (coefficientModel π₁ ℓ₁).toSubmodule) (w₂ : (coefficientModel π₂ ℓ₂).toSubmodule)
    (hw₁ : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f →
      w₁.val.val (g * k) = w₁.val.val g)
    (hw₂ : ∀ g k, k ∈ Conductor.levelSubgroup F.Carrier (m + 2) f →
      w₂.val.val (g * k) = w₂.val.val g)
    (hP : ∀ g : Langlands.GeneralLinear (m + 2 + 1) F.Carrier,
      (∀ j, g.val (Fin.last (m + 2)) j = if j = Fin.last (m + 2) then 1 else 0) →
      w₁.val.val g = w₂.val.val g)
    (hw₁1 : w₁.val.val 1 = 1) (hw₂1 : w₂.val.val 1 = 1)
    {W : Type*} [AddCommGroup W] [Module ℂ W]
    {σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) W}
    (hσ : IsGeneric ψ (m + 1) σ) {ωσ : F.Carrierˣ →* ℂˣ} (hσb : TrivialOnPrincipalUnits ωσ b)
    (ℓ' : glInverseFunctionals ψ (m + 1) σ) (hℓ' : ℓ'.val ≠ 0)
    (χ : Quasicharacter F.Carrier) (hχb : TrivialOnPrincipalUnits (χ : F.Carrierˣ →* ℂˣ) b)
    (ϖ : F.Carrierˣ) (hϖ : F.canonicalTopologicalData.ord (ϖ : F.Carrier) = 1)
    (f' : (coefficientModel σ ℓ').toSubmodule) {κ₁ : ℂ} (hκ₁ : κ₁ ≠ 0)
    (hsupp : ∀ B : Langlands.GeneralLinear (m + 1) F.Carrier, f'.val.val (rankInclusion 1 B) ≠ 0 →
      ∃ u : upperUnipotent (m + 1) F.Carrier,
        IsIntegralMatrix (u.val * B * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)))
    (hval : ∀ k : Langlands.GeneralLinear (m + 1) F.Carrier, IsIntegralMatrix k →
      f'.val.val (rankInclusion 1 (k * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (ϖ ^ c)⁻¹)) =
        κ₁ * (((χ : F.Carrierˣ →* ℂˣ) (determinant k) : ℂ))⁻¹)
    (hequiv : ∀ (g : Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
      (c' : lowerTriangularSubgroup 1 F.Carrier), IsIntegralUnit (c'.val 0 0) →
        f'.val.val (g * lowerBlockPair (1 : Langlands.GeneralLinear (m + 1) F.Carrier) 0 c') =
          ((ωσ * (χ : F.Carrierˣ →* ℂˣ) ^ (m + 1)) (determinant c'.val) : ℂ) * f'.val.val g)
    (C : (F.Carrierˣ →* ℂˣ) → ℂˣ)
    (hGall : ∀ (X : Type uX) [AddCommGroup X] [Module ℂ X]
      (τ : Representation ℂ (Langlands.GeneralLinear (m + 1) F.Carrier) X)
      (ωτ : F.Carrierˣ →* ℂˣ), IsGeneric ψ m τ → HasPrincipalLevelVector F τ f →
      Classification.HasGLCentralCharacter F.Carrier (m + 1) τ ωτ →
      ∃ G : RationalFunctions, IsPadicPairGammaFactor F ψ ν
          (Langlands.twist (((χ : F.Carrierˣ →* ℂˣ))⁻¹.comp determinant)
            (inverseTransposePullback σ)) τ G ∧
        G = rationalEpsilonMonomial (C ωτ) ((c * (m + 1) : ℕ) : ℤ))
    {G₁ G₂ : RationalFunctions}
    (h₁ : IsPadicPairGammaFactor F ψ ν
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₁) σ G₁)
    (h₂ : IsPadicPairGammaFactor F ψ ν
      (Langlands.twist ((χ : F.Carrierˣ →* ℂˣ).comp determinant) π₂) σ G₂) :
    G₁ = G₂ := by
  classical
  set χh : F.Carrierˣ →* ℂˣ := (χ : F.Carrierˣ →* ℂˣ) with hχh
  have hψ := hasIntegerConductorAt_of_additiveConductor_eq_zero F ψ hψ0
  have hϖ1 : InPow 1 (ϖ : F.Carrier) := inPow_one_of_ord_eq_one F ϖ.ne_zero hϖ
  have hϖO : (ϖ : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer := hϖ1.integral
  have hscale : ∀ o ∈ (ValuativeRel.valuation F.Carrier).integer,
      InPow f ((ϖ : F.Carrier) ^ c * o) :=
    fun o ho => (inPow_pow_mul hϖ1 c ho).mono (by omega)
  -- representatives for `Φ₂`
  obtain ⟨T₂, hT₂K, hT₂, hcov₂⟩ := exists_finset_addCosetReps (scaledLattice F (ϖ : F.Carrier) c m)
    (integerLattice F m) (isCompact_scaledLattice F ϖ.ne_zero c) (isOpen_integerLattice F)
  have hcovW : ∀ y, dualWeight ω (ϖ : F.Carrier) c f y ≠ 0 →
      ∃ t ∈ T₂, y - t ∈ integerLattice F m :=
    fun y hy => hcov₂ y (dualWeight_support F hy)
  -- `S₁` and `Φ₁`
  set μ : F.Carrierˣ →* ℂˣ := ωσ * χh ^ (m + 1) with hμ
  set S1 : F.Carrier → ℂ := unitCharWeight (μ * χh) with hS1def
  have hμχ : TrivialOnPrincipalUnits (μ * χh) b := (hσb.mul (hχb.pow _)).mul hχb
  set a : F.Carrierˣ := ϖ ^ b with ha_def
  have haval : (a : F.Carrier) = (ϖ : F.Carrier) ^ b := by rw [ha_def, Units.val_pow_eq_pow_val]
  have ha : (a : F.Carrier) ∈ (ValuativeRel.valuation F.Carrier).integer := by
    rw [haval]; exact pow_mem hϖO b
  have hper : ∀ ξ ∈ (ValuativeRel.valuation F.Carrier).integer, ∀ δ ∈ scaledIntegers F a⁻¹,
      S1 (ξ + δ) = S1 ξ := by
    intro ξ _ δ hδ
    rw [mem_scaledIntegers] at hδ
    have hδe : δ = (ϖ : F.Carrier) ^ b * (((a⁻¹ : F.Carrierˣ) : F.Carrier) * δ) := by
      rw [← mul_assoc, ← haval, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    rw [hδe]
    exact unitCharWeight_add hb hμχ ξ (inPow_pow_mul hϖ1 b hδ)
  obtain ⟨T₁, hT₁K, Φ₁, hΦ₁⟩ := exists_unit_inversion F ψ hψ ν a ha S1 hper
  -- the test data
  set T := productTest T₁ T₂ with hTdef
  set Φ := productWeight Φ₁ (dualWeight ω (ϖ : F.Carrier) c f) with hΦdef
  set S2 := integralFourier ψ T₂ (dualWeight ω (ϖ : F.Carrier) c f) with hS2def
  have hfac : ∀ ξ : Fin (m + 2) → F.Carrier,
      (∀ k, ξ k ∈ (ValuativeRel.valuation F.Carrier).integer) →
      finiteFourier ψ T Φ ξ = S1 (ξ 0) * S2 (fun k => ξ k.succ) :=
    fun ξ hξ => finiteFourier_product_eq ψ T₁ T₂ Φ₁ _ S1 hΦ₁ ξ hξ
  have hS1 : ∀ c, S1 c ≠ 0 → c ∈ (ValuativeRel.valuation F.Carrier).integer ∧ c ≠ 0 ∧
      c⁻¹ ∈ (ValuativeRel.valuation F.Carrier).integer := by
    intro t ht
    by_cases hu : IsIntegralUnit t
    · exact ⟨hu.2.1, hu.1, hu.2.2⟩
    · exfalso
      apply ht
      rw [hS1def]
      unfold unitCharWeight
      exact dite_eq_right_of_eq_false (eq_false hu)
  have hS2 : ∀ v, S2 v ≠ 0 → ∀ k, InPow f (v k) :=
    integralFourier_dualWeight_inPow F ψ hψ ν hf hω ϖ.ne_zero hϖ1 hcf T₂ hT₂K hT₂ hcov₂
  have hdeep : ∀ z ∈ T, Φ z ≠ 0 → IsDeepFirstRow f z := by
    intro z hz hΦz
    refine productTest_isDeepFirstRow hϖ1 hcb T₁ (fun u hu => ?_) T₂ Φ₁ z hz hΦz
    have := hT₁K hu
    rw [SetLike.mem_coe, mem_scaledIntegers, haval] at this
    exact this
  -- the candidate model vectors
  obtain ⟨ℓ₁χ, hℓ₁χ, fc₁, hfc₁⟩ := exists_candidateTest_model ψ χh π₁ ℓ₁ w₁ T Φ
  obtain ⟨ℓ₂χ, hℓ₂χ, fc₂, hfc₂⟩ := exists_candidateTest_model ψ χh π₂ ℓ₂ w₂ T Φ
  have hℓ₁χ' : ℓ₁χ.val ≠ 0 := by rw [hℓ₁χ]; exact hℓ₁
  have hℓ₂χ' : ℓ₂χ.val ≠ 0 := by rw [hℓ₂χ]; exact hℓ₂
  have hZ₁ : ∀ (z : F.Carrierˣ) g, w₁.val.val (Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) z * g) =
      (ω z : ℂ) * w₁.val.val g := fun z g => model_scalar_mul F π₁ ω hc₁ ℓ₁ w₁ z g
  have hZ₂ : ∀ (z : F.Carrierˣ) g, w₂.val.val (Matrix.GeneralLinearGroup.scalar (Fin (m + 3)) z * g) =
      (ω z : ℂ) * w₂.val.val g := fun z g => model_scalar_mul F π₂ ω hc₂ ℓ₂ w₂ z g
  have hP' : ∀ q : GeneralLinearGroup (Fin (m + 1 + 2)) F.Carrier,
      (∀ j, q (Fin.last (m + 1 + 1)) j =
        (1 : Matrix (Fin (m + 1 + 2)) (Fin (m + 1 + 2)) F.Carrier) (Fin.last (m + 1 + 1)) j) →
      w₁.val.val q = w₂.val.val q := by
    intro q hq
    apply hP q
    intro j
    rw [hq j, Matrix.one_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rfl
  -- the forward side
  have hI : ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier (m + 1)) fc₁.val f'.val s =
        corankOneIntegral ψ abv (unipotentQuotientHaar F.Carrier (m + 1)) fc₂.val f'.val s := by
    refine ⟨0, fun s _ => ?_⟩
    unfold corankOneIntegral
    congr 1
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      rw [corankOneIntegrand_mk, corankOneIntegrand_mk]
      congr 2
      change fc₁.val.val (rankInclusion 1 g) = fc₂.val.val (rankInclusion 1 g)
      rw [hfc₁, hfc₂]
      unfold candidateTest
      congr 1
      exact testValue_eq_at_weyl ω w₁.val.val w₂.val.val hw₁ hw₂ hZ₁ hZ₂ hP' T Φ hdeep g
  -- the twisted smeared function and its shell identities
  have hPigen := isGeneric_twist_inverseTransposePullback F ψ σ hσ ℓ' hℓ' χh χ.continuous
  obtain ⟨ℓF, hℓF, Fbig, hFbig, LF, hFL⟩ := exists_twistedSmear_model F ψ ν σ hσ ℓ' hℓ' f' χh
    χ.continuous (dualWeightFourier F ψ ω (ϖ : F.Carrier) c f T₂)
    (dualWeightFourier_isLocallyConstant F ψ hψ ω _ c f T₂)
    (dualWeightFourier_hasCompactSupport F ψ ω _ c f T₂)
  have hFbig' : ∀ g, Fbig.val.val g = twistedSmear F ψ ν χh ω (ϖ : F.Carrier) c f T₂ f'.val g :=
    fun g => by rw [hFbig g]; rfl
  have hshell := shell_discharge F hf ψ hψ ν ν χh hω ϖ hϖ hscale T₂ hT₂ hcovW f'.val κ₁ hsupp hval
    (isOfWhittakerType_of_isGeneric F hPigen) ℓF hℓF Fbig hFbig' LF hFL C hGall ω⁻¹
    (fun z _ => rfl)
  set c₀ := shellConstant F ν χh ω ϖ c f m κ₁ C ω⁻¹ with hc₀
  have havgA := rightAverage_eq_target_of_shells F hf hT1 ψ hψ hω
    (corankRestriction F ψ Fbig.val)
    (LF.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous ⊓
      Conductor.levelOpenSubgroup F.Carrier m 0)
    (corankRestriction_mul F ψ Fbig.val LF hFL) (corankRestriction_unipotent F ψ Fbig.val)
    (corankRestriction_shell_compact F ψ Fbig.val LF hFL) c₀ hshell
  -- the dual side
  obtain ⟨C', hC', hJval⟩ := dual_integral_value F (m := m) hf ν
  have hη := secondDual_lowerBlockPair F ψ f'.val μ hequiv
  have hκ := lastWeight_unitCharWeight F χh μ
  have hU : ∀ A : Langlands.GeneralLinear (m + 1) F.Carrier,
      ∫ x, S2 (fun k => x 0 k.rev) * (secondDualFunction ψ (m + 1) f'.val).val
        (lowerBlockPair A x 1 : GeneralLinear (m + 1 + 1) F.Carrier)
        ∂rectangularMeasure ν 1 (m + 1) =
      (χh (determinant A) : ℂ) * Fbig.val.val (rankInclusion 1 A) := by
    intro A
    rw [hFbig']
    exact integral_integralFourier_eq F ψ ν χh ω (ϖ : F.Carrier) c f T₂ f'.val A
  have hπ₁χ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₁
  have hπ₂χ := isGeneric_quasicharacter_twist F.canonicalTopologicalData ψ χ hπ₂
  obtain ⟨a₁, ha₁⟩ := dual_integrand_measurable_integrable F ψ ν hπ₁χ hσ ℓ₁χ hℓ₁χ' ℓ' hℓ' fc₁ f'
  obtain ⟨a₂, ha₂⟩ := dual_integrand_measurable_integrable F ψ ν hπ₂χ hσ ℓ₂χ hℓ₂χ' ℓ' hℓ' fc₂ f'
  have hJ : ∃ (a : ℝ) (cJ : ℂ), cJ ≠ 0 ∧ ∀ s : ℂ, a < s.re →
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier (m + 1))
          (firstDualFunction ψ (m + 1 + 1) fc₁.val) (secondDualFunction ψ (m + 1) f'.val) s =
        cJ ∧
      corankOneIntegral (ψ.scale (-1)) abv (unipotentQuotientHaar F.Carrier (m + 1))
          (firstDualFunction ψ (m + 1 + 1) fc₂.val) (secondDualFunction ψ (m + 1) f'.val) s =
        cJ := by
    refine ⟨max a₁ a₂, (C' : ℂ) * ((χh (determinant (weylLong (m + 3) F.Carrier)) : ℂ) * c₀ * 1),
      ?_, fun s hs => ⟨?_, ?_⟩⟩
    · refine mul_ne_zero (Complex.ofReal_ne_zero.mpr hC'.ne') (mul_ne_zero (mul_ne_zero
        (Units.ne_zero _) (shellConstant_ne_zero F ν χh ω ϖ c f hκ₁ C ω⁻¹)) one_ne_zero)
    · have hs₁ := ha₁ s ((le_max_left _ _).trans_lt hs)
      rw [hJval ψ hψ χh hω w₁.val hw₁ hZ₁ T Φ fc₁.val hfc₁ S1 S2 (invCharWeight μ) f'.val hfac
        hS1 hS2 hη hκ Fbig.val hU LF hFL c₀ havgA s hs₁.1 hs₁.2, hw₁1]
    · have hs₂ := ha₂ s ((le_max_right _ _).trans_lt hs)
      rw [hJval ψ hψ χh hω w₂.val hw₂ hZ₂ T Φ fc₂.val hfc₂ S1 S2 (invCharWeight μ) f'.val hfac
        hS1 hS2 hη hκ Fbig.val hU LF hFL c₀ havgA s hs₂.1 hs₂.2, hw₂1]
  exact gamma_eq_of_adjacent_tests F ψ ν h₁ h₂ ℓ₁χ hℓ₁χ' ℓ₂χ hℓ₂χ' ℓ' hℓ' fc₁ fc₂ f' hI hJ

end Langlands.RankinSelberg.HighlyRamified

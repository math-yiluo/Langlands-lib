import Langlands.Representation.RankinSelberg.UnitaryWhittakerTorusSum
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionReduction

/-!
# The restriction estimate for unitary generic Whittaker functions

For an irreducible admissible unitarizable representation `π` of `GL_(n+k+2)(F)` over a
p-adic field and a Whittaker function `W` of its coefficient model,

`∫_{N_(n+1) \ GL_(n+1)} |W(diag(g, 1_(k+1)))|² |det g|^(-k) dg < ∞`.

For `k = 0` this is the square-integrability of `W` on `N \ P` (Jacquet–Shalika, *Euler
products I*, (1.3.1)). The proof follows the published reduction
`SquareIntegrableWhittakerRestriction.of_torusSum` of the square-integrable case, with the
weight `|det g|^(-k)` in place of `|det g|^(-(k+1))` and the unitary torus sum
`summable_density_mul_norm_sq` in place of the square-integrable one.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open SquareIntegrableWhittakerRestriction

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

section Canonical

local instance restrictionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance restrictionFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance restrictionFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField

/-- The torus sum for coefficient-model vectors. -/
theorem summable_density_mul_model_sq (k : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ρ : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (hadm : IsAdmissible ρ) (hirr : Representation.IsIrreducible ρ) (hunit : IsUnitarizable ρ)
    (ℓ : glFunctionals ψ (k + 1) ρ) (f : (coefficientModel ρ ℓ).toSubmodule)
    (ϖ : F.Carrierˣ)
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ) :
    Summable (fun lam : Fin (k + 1) → ℤ =>
      QuotientTorusEnvelope.density F F.canonicalTopologicalData ϖ lam *
        ‖f.val.val (Iwasawa.torus ϖ (Fin.snoc lam 0))‖ ^ 2) := by
  obtain ⟨v, rfl⟩ := modelMap_surjective ρ ℓ f
  exact summable_density_mul_norm_sq F k ψ ρ hadm hirr hunit ℓ v ϖ hϖ

end Canonical

/-- The inverse modulus of a zero-padded exponent vector: padding `a` by `k` zeros
multiplies the inverse modulus by `|det ϖ^a|^(-k)`. -/
theorem density_extendExp (T : F.TopologicalData) (ϖ : F.Carrierˣ) (n k : ℕ)
    (a : Fin (n + 1) → ℤ) :
    QuotientTorusEnvelope.density F T ϖ (n := n + (0 + k)) (extendExp n (0 + k + 1) a) =
      QuotientTorusEnvelope.density F T ϖ a *
        normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ a).val) ^
          (-(((0 + k : ℕ) : ℝ))) := by
  let g : ℤ → ℝ := fun z => T.normalizedAbs ((ϖ ^ z : F.Carrierˣ) : F.Carrier)
  have hdiv (x y : ℤ) :
      T.normalizedAbs ((ϖ ^ x / ϖ ^ y : F.Carrierˣ) : F.Carrier) = g x / g y := by
    rw [Units.val_div_eq_div_val]
    exact map_div₀ (normalizedAbsoluteValue T) _ _
  have hg0 : g 0 = 1 := by
    simp only [g, zpow_zero, Units.val_one]
    exact T.normalizedAbs_one
  have hdet : normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ a).val) =
      ∏ i, g (a i) := by
    rw [Iwasawa.torus_val, Matrix.det_diagonal, map_prod]
    rfl
  have hpos : 0 ≤ ∏ i, g (a i) := Finset.prod_nonneg fun i _ => T.normalizedAbs_nonneg _
  have hmod := modulus_padZero g hg0 n (0 + k) a
  unfold QuotientTorusEnvelope.density
  simp only [hdiv]
  change (∏ i : Fin (n + (0 + k) + 1),
      ∏ j ∈ Finset.univ.filter (fun j : Fin (n + (0 + k) + 1) => i < j),
        g (if h : i.val < n + 1 then a ⟨i.val, h⟩ else 0) /
          g (if h : j.val < n + 1 then a ⟨j.val, h⟩ else 0))⁻¹ = _
  rw [hmod, hdet, Real.rpow_neg hpos, Real.rpow_natCast, mul_inv]

set_option maxHeartbeats 2000000 in
/-- **The unitary restriction estimate.** For an irreducible admissible unitarizable
representation `π` of `GL_(n+k+2)(F)`, every compatible quotient measure `μ` on
`N_(n+1) \ GL_(n+1)(F)` and every coefficient-model vector `f`, the function
`q ↦ |W(diag(g, 1_(k+1)))|² |det g|^(-k)` is `μ`-integrable. -/
theorem unitaryWhittakerRestriction (n k : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := borel F.Carrier
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)],
      ∀ μ : Measure (LeftUnipotentQuotient n F.Carrier),
        IsCompatible (upperUnipotent (n + 1) F.Carrier)
          (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
        ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V],
        ∀ π : Representation ℂ
            (Langlands.GeneralLinear (n + (0 + k + 1) + 1) F.Carrier) V,
          IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
          ∀ (ℓ : glFunctionals ψ (n + (0 + k + 1)) π)
            (f : (coefficientModel π ℓ).toSubmodule),
            Integrable
              (fun q : LeftUnipotentQuotient n F.Carrier =>
                restrictedWhittakerNorm ψ k f.val q ^ 2 *
                  quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n q ^
                    (-(((0 + k : ℕ) : ℝ)))) μ := by
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ _ μ hμ V _ _ π hadm hirr hunit ℓ f
  let := borel (GeneralLinear (n + 1) F.Carrier)
  have : BorelSpace (GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement F.Carrier
  have hd : 0 < 0 + k + 1 := by omega
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let dk : Measure (GeneralLinear (n + 1) F.Carrier) :=
    (generalLinearHaar F.Carrier n).restrict (K : Set (GeneralLinear (n + 1) F.Carrier))
  let qLam : (Fin (n + 1) → ℤ) → GeneralLinear (n + 1) F.Carrier →
      LeftUnipotentQuotient n F.Carrier := fun lam x =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam * x)
  have hμeq : μ = Measure.sum (fun lam : Fin (n + 1) → ℤ =>
      ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) • Measure.map (qLam lam) dk) :=
    QuotientTorusEnvelope.quotientMeasure_eq_sum_torus F T n μ hμ ϖ hϖ
  -- Right smoothness of the Whittaker function and a finite cover of `K`.
  have hsmooth := hadm.1
  obtain ⟨L, hL⟩ := model_isSmooth π hsmooth ℓ f
  have hLinv : ∀ y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier, ∀ l ∈ L,
      f.val.val (y * l) = f.val.val y := fun y l hl =>
    congrArg (fun w : (coefficientModel π ℓ).toSubmodule => w.val.val y) (hL ⟨l, hl⟩)
  let e := appendIdentity (F := F.Carrier) n (0 + k + 1)
  have he : Continuous e := continuous_appendIdentity n _
  let H := L.comap e he
  have hKzero : (Conductor.levelOpenSubgroup F.Carrier n 0 :
      Set (GeneralLinear (n + 1) F.Carrier)) = (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    change (Conductor.levelSubgroup F.Carrier n 0 : Set (GeneralLinear (n + 1) F.Carrier)) =
      (K : Set (GeneralLinear (n + 1) F.Carrier))
    rw [Conductor.levelSubgroup_zero]
  have hKcompact : IsCompact (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier n 0
  have hKmeas : MeasurableSet (K : Set (GeneralLinear (n + 1) F.Carrier)) := by
    rw [← hKzero]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  have hdet (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      normalizedAbsoluteValue T (Matrix.det x.val) = 1 := by
    have hv := Conductor.valuation_det_of_mem_integralSubgroup hx
    have hx0 : Matrix.det x.val ≠ 0 := by
      intro hx0
      rw [hx0, map_zero] at hv
      exact zero_ne_one hv
    have hd1 : T.discreteValuation (Matrix.det x.val) = 1 := by
      change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
        (ValuativeRel.valuation F.Carrier (Matrix.det x.val)) = 1
      rw [hv, map_one]
    rw [normalizedAbsoluteValue_apply, T.normalizedAbs_of_ne_zero hx0]
    simp [PadicField.TopologicalData.ord, hd1]
  obtain ⟨S, hS⟩ := hKcompact.elim_finite_subcover
    (fun ρ : GeneralLinear (n + 1) F.Carrier =>
      (fun x => ρ⁻¹ * x) ⁻¹' (H : Set (GeneralLinear (n + 1) F.Carrier)))
    (fun ρ => H.isOpen.preimage (continuous_const.mul continuous_id))
    (fun x _ => Set.mem_iUnion.mpr ⟨x, by
      show x⁻¹ * x ∈ H
      rw [inv_mul_cancel]
      exact H.one_mem⟩)
  have hcover (y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier)
      (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      ‖f.val.val (y * e x)‖ ^ 2 ≤ ∑ ρ ∈ S, ‖f.val.val (y * e ρ)‖ ^ 2 := by
    have hxS := hS hx
    simp only [Set.mem_iUnion, Set.mem_preimage] at hxS
    obtain ⟨ρ, hρS, hρ⟩ := hxS
    have hl : e (ρ⁻¹ * x) ∈ L := hρ
    have hxρ := hLinv (y * e ρ) _ hl
    rw [mul_assoc, ← map_mul e, mul_inv_cancel_left] at hxρ
    rw [hxρ]
    exact Finset.single_le_sum (f := fun ρ => ‖f.val.val (y * e ρ)‖ ^ 2)
      (fun i _ => sq_nonneg _) hρS
  -- Continuity of the integrand on the quotient.
  let Φ : LeftUnipotentQuotient n F.Carrier → ℝ := fun q =>
    restrictedWhittakerNorm ψ k f.val q ^ 2 *
      quotientDeterminantAbs (normalizedAbsoluteValue T) n q ^ (-(((0 + k : ℕ) : ℝ)))
  have hΦnn (q : LeftUnipotentQuotient n F.Carrier) : 0 ≤ Φ q :=
    mul_nonneg (pow_nonneg (restrictedWhittakerNorm_nonneg ψ k f.val q) 2)
      (Real.rpow_nonneg (quotientDeterminantAbs_nonneg _ n q) _)
  have hWc : Continuous (fun y : GeneralLinear (n + (0 + k + 1) + 1) F.Carrier => f.val.val y) :=
    continuous_of_rightInvariant _ L.toSubgroup L.isOpen hLinv
  have hdetc : Continuous (fun g : GeneralLinear (n + 1) F.Carrier =>
      normalizedAbsoluteValue T (Matrix.det g.val)) :=
    (NNReal.continuous_coe.comp (Units.continuous_val.comp
      (T.determinantNormContinuous (n + 1)).continuous)).congr fun x => rfl
  have hΦc : Continuous Φ := by
    have hW : Continuous (restrictedWhittakerNorm ψ k f.val) :=
      Continuous.quotient_lift (continuous_norm.comp (hWc.comp he)) _
    have hD : Continuous (quotientDeterminantAbs (normalizedAbsoluteValue T) n) :=
      Continuous.quotient_lift hdetc _
    exact (hW.pow 2).mul
      (hD.rpow_const fun q => Or.inl (quotientDeterminantAbs_pos _ n q).ne')
  have hΦm : Measurable (fun q => ENNReal.ofReal (Φ q)) :=
    ENNReal.measurable_ofReal.comp hΦc.measurable
  have hqc (lam : Fin (n + 1) → ℤ) : Continuous (qLam lam) :=
    (leftQuotient_isOpenQuotientMap _).continuous.comp (continuous_const.mul continuous_id)
  -- The pointwise bound on each compact orbit.
  let C : (Fin (n + 1) → ℤ) → ℝ := fun lam =>
    (∑ ρ ∈ S, ‖f.val.val (e (Iwasawa.torus ϖ lam) * e ρ)‖ ^ 2) *
      normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ lam).val) ^
        (-(((0 + k : ℕ) : ℝ)))
  have hpt (lam : Fin (n + 1) → ℤ) (x : GeneralLinear (n + 1) F.Carrier) (hx : x ∈ K) :
      Φ (qLam lam x) ≤ C lam := by
    change ‖f.val.val (e (Iwasawa.torus ϖ lam * x))‖ ^ 2 *
        normalizedAbsoluteValue T (Matrix.det (Iwasawa.torus ϖ lam * x).val) ^
          (-(((0 + k : ℕ) : ℝ))) ≤ C lam
    rw [map_mul e, Units.val_mul, Matrix.det_mul, map_mul (normalizedAbsoluteValue T),
      hdet x hx, mul_one]
    exact mul_le_mul_of_nonneg_right (hcover _ x hx)
      (Real.rpow_nonneg (AbsoluteValue.nonneg _ _) _)
  -- The lattice terms for the finitely many right translates.
  let a : GeneralLinear (n + 1) F.Carrier → (Fin (n + 1) → ℤ) → ℝ := fun ρ lam =>
    QuotientTorusEnvelope.density F T ϖ (n := n + (0 + k)) (extendExp n (0 + k + 1) lam) *
      ‖f.val.val (Iwasawa.torus ϖ (Fin.snoc (extendExp n (0 + k + 1) lam) 0 :
        Fin (n + (0 + k + 1) + 1) → ℤ) * e ρ)‖ ^ 2
  have ha_nn (ρ : GeneralLinear (n + 1) F.Carrier) (lam : Fin (n + 1) → ℤ) : 0 ≤ a ρ lam :=
    mul_nonneg (QuotientTorusEnvelope.density_pos F T ϖ _).le (sq_nonneg _)
  have hasum (ρ : GeneralLinear (n + 1) F.Carrier) : Summable (a ρ) := by
    have hB := summable_density_mul_model_sq F (n + (0 + k)) ψ π hadm hirr hunit ℓ
      (modelRepresentation π ℓ (e ρ) f) ϖ hϖ
    have hC := hB.comp_injective (extendExp_injective n (0 + k + 1) hd)
    exact hC
  have hbound (lam : Fin (n + 1) → ℤ) :
      ∫⁻ q, ENNReal.ofReal (Φ q) ∂(ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) •
        Measure.map (qLam lam) dk) ≤ ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := by
    rw [lintegral_smul_measure, lintegral_map hΦm (hqc lam).measurable, smul_eq_mul]
    calc ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) *
          ∫⁻ x, ENNReal.ofReal (Φ (qLam lam x)) ∂dk
        ≤ ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam) *
            ∫⁻ _x, ENNReal.ofReal (C lam) ∂dk := by
          exact mul_le_mul_of_nonneg_left
            (lintegral_mono_ae (ae_restrict_of_forall_mem hKmeas fun x hx =>
              ENNReal.ofReal_le_ofReal (hpt lam x hx))) zero_le
      _ = ENNReal.ofReal (QuotientTorusEnvelope.density F T ϖ lam * C lam) := by
          rw [lintegral_const]
          simp only [dk, K, Measure.restrict_apply_univ, generalLinearHaar_integralSubgroup,
            mul_one]
          rw [← ENNReal.ofReal_mul (QuotientTorusEnvelope.density_pos F T ϖ lam).le]
      _ = ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := by
          congr 1
          simp only [a, C, e]
          rw [density_extendExp F T ϖ n k lam,
            appendIdentity_torus_snoc n _ hd ϖ lam, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun ρ _ => ?_
          ring
  -- Assemble.
  show Integrable Φ μ
  rw [hμeq]
  refine ⟨hΦc.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hΦnn), lintegral_sum_measure]
  calc ∑' lam, ∫⁻ q, ENNReal.ofReal (Φ q) ∂(ENNReal.ofReal
          (QuotientTorusEnvelope.density F T ϖ lam) • Measure.map (qLam lam) dk)
      ≤ ∑' lam, ENNReal.ofReal (∑ ρ ∈ S, a ρ lam) := ENNReal.tsum_le_tsum hbound
    _ = ENNReal.ofReal (∑' lam, ∑ ρ ∈ S, a ρ lam) :=
      (ENNReal.ofReal_tsum_of_nonneg (fun lam => Finset.sum_nonneg fun ρ _ => ha_nn ρ lam)
        (summable_sum fun ρ _ => hasum ρ)).symm
    _ < ⊤ := ENNReal.ofReal_lt_top

end Langlands.RankinSelberg.UnitaryGeneric

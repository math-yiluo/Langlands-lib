import Langlands.Representation.RankinSelberg.UnitaryWhittakerRestriction
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareReduction
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationProof

/-!
# The weighted Whittaker square estimate for unitary generic representations

For an irreducible admissible unitarizable representation `π` of `GL_(n+1)(F)` over a p-adic
field (canonical topology), every Whittaker function `W` of a coefficient model for the standard
or the inverse standard character, every Schwartz–Bruhat function `Φ` and every real
`a ≥ 1/2`,

`∫_{N \ GL_(n+1)} |W(x)|² |Φ(e_(n+1) x)|² |det x|^(2a) dx < ∞`.

The proof follows the published reduction `weightedWhittakerSquare_of` of the square-integrable
case (JPSS 1983, §8.3, p. 449) and reuses its public helper lemmas. The differences:

* the unitary central character comes from the invariant positive form and Schur's lemma
  (`nonempty_unitaryCentralCharacter_of_unitarizable`);
* the corank-one input is the unitary restriction estimate
  `unitaryWhittakerRestriction` at `k = 0`, i.e. `∫ |W(diag(g,1))|² dg < ∞` (weight
  `|det g|^0`), in place of the square-integrable one (weight `|det g|^(-1)`);
* hence the determinant weight `|det g|^(2a-1)` must be bounded on the support of
  `W(diag(g,1))`, which needs `2a - 1 ≥ 0`.
-/

noncomputable section

namespace Langlands.RankinSelberg.UnitaryGeneric

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- An irreducible admissible unitarizable representation has a unitary central character.
Schur's lemma gives a locally constant central character; the invariant positive form forces
it to have absolute value one. -/
theorem nonempty_unitaryCentralCharacter_of_unitarizable {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V} :
    letI := F.canonicalTopologicalData.topology
    IsAdmissible ρ → Representation.IsIrreducible ρ → IsUnitarizable ρ →
      Nonempty (UnitaryCentralCharacter ρ) := by
  let T := F.canonicalTopologicalData
  let := T.topology
  intro hadm hirr hunit
  have := T.generalLinearTopologicalGroup n
  obtain ⟨χ, ⟨hlc, hact⟩, -⟩ := admissibleSchur_centralCharacter ρ hadm hirr
  obtain ⟨b⟩ := hunit
  let := hirr
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Langlands.GeneralLinear n F.Carrier)) ρ.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  refine ⟨⟨χ, ?_, ?_, hact⟩⟩
  · have h := hlc.isOpen_fiber 1
    convert h using 1
    ext x
    simp [MonoidHom.mem_ker]
  · intro z
    have h := b.invariant (z : Langlands.GeneralLinear n F.Carrier) v v
    rw [hact z v] at h
    set c : ℂ := (χ z : ℂ)
    have hsmul_right : b.inner v (c • v) = c * b.inner v v := by
      rw [← b.conj_inner_symm, b.smul_left, map_mul, Complex.conj_conj, b.conj_inner_symm]
    rw [b.smul_left, hsmul_right, ← mul_assoc, Complex.conj_mul'] at h
    have hI : b.inner v v ≠ 0 := fun h0 => hv (b.definite v h0)
    have h1 : ((‖c‖ ^ 2 : ℝ) : ℂ) = 1 := by
      have := mul_right_cancel₀ hI (h.trans (one_mul _).symm)
      exact_mod_cast this
    have h2 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h1
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg c) two_ne_zero).1 h2

/-- The standard-character weighted square estimate for unitary generic representations, in a
fixed rank `n + 1`, for the canonical topology and every `a ≥ 1/2`. -/
def UnitaryStandardWeightedSquareAt (n : ℕ) : Prop :=
  letI := F.canonicalTopologicalData.topology
  letI := F.canonicalTopologicalData.valuativeRel
  letI := F.canonicalTopologicalData.localField
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
      ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V,
        IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
        ∀ (ℓ : glFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 1 / 2 ≤ a →
          Integrable (fun q => (whittakerNorm ψ f.val q) ^ 2 *
              ‖Φ (quotientLastRow n q)‖ ^ 2 *
              (quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n q) ^
                (2 * a)) μ

/-- Rank one: the Whittaker norm is constant and the determinant power is a geometric tail.
This is the proof of `standardWeightedSquare_zero` with the unitary central character. -/
theorem unitaryStandardWeightedSquare_zero : UnitaryStandardWeightedSquareAt.{uF, uV} F 0 := by
  let T := F.canonicalTopologicalData
  intro ψ _ μ hμ V _ _ π hadm hirr hunit ℓ f Φ a ha
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel (Langlands.GeneralLinear 1 F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (0 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (0 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient 0 F.Carrier) := ⟨rfl⟩
  have : IsTopologicalRing F.Carrier := inferInstance
  have : T2Space F.Carrier := T.fieldT2
  have hsmooth : IsSmooth π := hadm.1
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter_of_unitarizable F hadm hirr hunit
  have habv : Continuous (normalizedAbsoluteValue T) := continuous_normalizedAbs' T
  refine ⟨(continuous_weightedSquareIntegrand _ habv hsmooth ψ ℓ f Φ
    (2 * a)).aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM⟩ :=
    Φ.locallyConstant.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨R, hR⟩ := Φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn
    ((continuous_normalizedAbs' T).comp (continuous_apply (0 : Fin 1))).continuousOn
  obtain ⟨N, hN⟩ := exists_ord_lower_bound T R
  obtain ⟨hρ0, hρ1⟩ := residueCardinality_rpow_neg_mem T (by linarith : 0 < 2 * a)
  set ρ : ℝ := (T.residueCardinality : ℝ) ^ (-(2 * a)) with hρ
  have hbound : ∀ q, ‖(whittakerNorm ψ f.val q) ^ 2 * ‖Φ (quotientLastRow 0 q)‖ ^ 2 *
      (quotientDeterminantAbs (normalizedAbsoluteValue T) 0 q) ^ (2 * a)‖ₑ ≤
      ENNReal.ofReal (‖f.val.val 1‖ ^ 2 * M ^ 2) *
        {q | N ≤ determinantOrder T 0 q}.indicator
          (fun q => ENNReal.ofReal (ρ ^ determinantOrder T 0 q)) q := by
    intro q
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q
    change ‖‖f.val.val g‖ ^ 2 * ‖Φ (lastRow g)‖ ^ 2 *
      T.normalizedAbs (Matrix.det g.val) ^ (2 * a)‖ₑ ≤ _
    rw [norm_coefficientModel_rankOne c ψ ℓ f g]
    by_cases hΦ : Φ (lastRow g) = 0
    · simp [hΦ]
    have hdet : (GeneralLinear.determinant g : F.Carrier) = Matrix.det g.val :=
      Matrix.GeneralLinearGroup.val_det_apply _
    have hRg : T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) ≤ R := by
      have h := hR (lastRow g) (subset_tsupport _ (Function.mem_support.mpr hΦ))
      have hrow : lastRow g 0 = (GeneralLinear.determinant g : F.Carrier) := by
        rw [hdet, Matrix.det_fin_one]
        rfl
      simp only [Function.comp_apply, hrow, Real.norm_eq_abs] at h
      exact (le_abs_self _).trans h
    have hord : N ≤ determinantOrder T 0 (⟦g⟧) := hN _ (GeneralLinear.determinant g).ne_zero hRg
    rw [Set.indicator_of_mem (show ⟦g⟧ ∈ {q | N ≤ determinantOrder T 0 q} from hord),
      determinantOrder_mk, ← hdet,
      normalizedAbs_rpow_eq_zpow_ord T (GeneralLinear.determinant g).ne_zero,
      Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hM _) 2) (by positivity)) (zpow_nonneg hρ0.le _)
  let ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
  have hτord : ∀ q, determinantOrder T 0
      (rightTranslate (upperUnipotent 1 F.Carrier) (GeneralLinear.scalar ϖ) q) =
        determinantOrder T 0 q + 1 := by
    intro q
    rw [determinantOrder_rightTranslate T 0]
    have hs : (GeneralLinear.determinant (GeneralLinear.scalar ϖ :
        Langlands.GeneralLinear 1 F.Carrier) : F.Carrier) = ϖ := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_one]
      simp
    rw [hs, LocalFactor.PadicAbelian.uniformizerUnit_ord]
  have hmass : μ {q | determinantOrder T 0 q = 0} ≠ ⊤ := by
    have hK : IsCompact (GeneralLinearGroup.integralSubgroup (Fin 1) T.Integers :
        Set (Langlands.GeneralLinear 1 F.Carrier)) :=
      GeneralLinearGroup.isCompact_integralSubgroup _ _ T.isCompact_integers
    have hsub : {q | determinantOrder T 0 q = 0} ⊆
        leftQuotientMap (upperUnipotent 1 F.Carrier) ''
          (GeneralLinearGroup.integralSubgroup (Fin 1) T.Integers : Set _) := by
      intro q hq
      obtain ⟨g, rfl⟩ := Quotient.exists_rep q
      exact ⟨g, mem_integralSubgroup_rankOne_of_ord_eq_zero T hq, rfl⟩
    have := hμ.regular
    exact ((measure_mono hsub).trans_lt
      (hK.image (leftQuotient_isOpenQuotientMap _).continuous).measure_lt_top).ne
  rw [hasFiniteIntegral_iff_enorm]
  refine (lintegral_mono hbound).trans_lt ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr ?_)
  exact lintegral_indicator_zpow_ord_ne_top (fun m => measurableSet_determinantSlice T 0 m)
    (hμ.right_invariant _) hτord hmass hρ0 hρ1 N

set_option maxHeartbeats 2000000 in
/-- Rank `m + 2`: the proof of `standardWeightedSquare_succ` with the unitary restriction
estimate at `k = 0` and the weight `|det g|^(2a-1)`. -/
theorem unitaryStandardWeightedSquare_succ (m : ℕ) :
    UnitaryStandardWeightedSquareAt.{uF, uV} F (m + 1) := by
  classical
  let T := F.canonicalTopologicalData
  have h1 : RecursiveQuotientIntegrationStatement F T m := recursiveQuotientIntegration F T m
  intro ψ _ μ hμ V _ _ π hadm hirr hunit ℓ f Φ a ha
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : IsTopologicalRing F.Carrier := inferInstance
  have : T2Space F.Carrier := T.fieldT2
  have := T.secondCountableTopology
  have : SecondCountableTopology F.Carrierˣ := Units.isEmbedding_val₀.secondCountableTopology
  have hGL (r : ℕ) : SecondCountableTopology (Langlands.GeneralLinear r F.Carrier) := by
    have : SecondCountableTopology (Matrix (Fin r) (Fin r) F.Carrier) :=
      inferInstanceAs (SecondCountableTopology (Fin r → Fin r → F.Carrier))
    have : SecondCountableTopology (Matrix (Fin r) (Fin r) F.Carrier)ᵐᵒᵖ :=
      MulOpposite.opHomeomorph.symm.secondCountableTopology
    exact Units.isInducing_embedProduct.secondCountableTopology
  have : SecondCountableTopology (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) := hGL _
  have : SecondCountableTopology (LeftUnipotentQuotient m F.Carrier) := by
    have := hGL (m + 1)
    exact Topology.IsOpenQuotientMap.secondCountableTopology
      (leftQuotient_isOpenQuotientMap (upperUnipotent (m + 1) F.Carrier))
  let := borel F.Carrierˣ
  have : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (m + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (m + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient m F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient m F.Carrier) := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)
  have : BorelSpace (Langlands.GeneralLinear (m + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (m + 1 + 1) F.Carrier)
  have : BorelSpace (upperUnipotent (m + 1 + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient (m + 1) F.Carrier)
  have : BorelSpace (LeftUnipotentQuotient (m + 1) F.Carrier) := ⟨rfl⟩
  have hsmooth : IsSmooth π := hadm.1
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter_of_unitarizable F hadm hirr hunit
  have habv : Continuous (normalizedAbsoluteValue T) := continuous_normalizedAbs' T
  refine ⟨(continuous_weightedSquareIntegrand _ habv hsmooth ψ ℓ f Φ
    (2 * a)).aestronglyMeasurable, ?_⟩
  have ha' : 0 ≤ 2 * a - 1 := by linarith
  -- The recursive integration formula, with the actual smaller quotient measure.
  let μs := unipotentQuotientHaar F.Carrier m
  have hμs := unipotentQuotientHaar_isCompatible F.Carrier m
  have hrec := h1 μs μ hμs hμ
  -- The vector, its integral orbit, and the determinant bounds of the orbit.
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨S, hS⟩ := exists_finset_integralOrbit T (m + 1) π hsmooth v
  choose C hC using fun w : V =>
    exists_normalizedAbs_det_bound F T (m + 1) ψ V π hsmooth ℓ (modelMap π ℓ w)
  let D : V → ℝ := fun w => max (C w) 1 ^ (2 * a - 1)
  have hD (w : V) : 0 ≤ D w := Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) _
  let G : V → LeftUnipotentQuotient m F.Carrier → ℝ := fun w q =>
    restrictedWhittakerNorm ψ 0 (modelMap π ℓ w).val q ^ 2 *
      quotientDeterminantAbs (normalizedAbsoluteValue T) m q ^ (-(((0 + 0 : ℕ) : ℝ)))
  have hG (w : V) : Integrable (G w) μs :=
    unitaryWhittakerRestriction F m 0 ψ μs hμs V π hadm hirr hunit ℓ (modelMap π ℓ w)
  have hG0 (w : V) (q : LeftUnipotentQuotient m F.Carrier) : 0 ≤ G w q :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (quotientDeterminantAbs_nonneg _ _ _) _)
  let Pr : LeftUnipotentQuotient m F.Carrier → ℝ := fun q => ∑ w ∈ S, D w * G w q
  have hPr : Integrable Pr μs := integrable_finsetSum S fun w _ => (hG w).const_mul (D w)
  -- The scalar coordinate.
  obtain ⟨M, hM⟩ :=
    Φ.locallyConstant.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨N, hN⟩ := exists_ord_lower_bound_of_lastRow T (m + 1) Φ
  have hpos : 0 < ((m + 2 : ℕ) : ℝ) * (2 * a) := by
    have : (0 : ℝ) < ((m + 2 : ℕ) : ℝ) := by positivity
    have : (0 : ℝ) < 2 * a := by linarith
    positivity
  obtain ⟨hρ0, hρ1⟩ := residueCardinality_rpow_neg_mem T hpos
  set ρ : ℝ := (T.residueCardinality : ℝ) ^ (-(((m + 2 : ℕ) : ℝ) * (2 * a))) with hρ
  let Q : F.Carrierˣ → ENNReal := fun t => ENNReal.ofReal (M ^ 2) *
    {t : F.Carrierˣ | N ≤ T.ord (t : F.Carrier)}.indicator
      (fun t => ENNReal.ofReal (ρ ^ T.ord (t : F.Carrier))) t
  -- The integral factor.
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer (m + 1)
  have hdk : (generalLinearHaar F.Carrier (m + 1)).restrict
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) Set.univ = 1 := by
    rw [Measure.restrict_apply_univ]
    exact generalLinearHaar_integralSubgroup F.Carrier (m + 1)
  have : IsFiniteMeasure ((generalLinearHaar F.Carrier (m + 1)).restrict
      (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))) :=
    ⟨by rw [hdk]; exact ENNReal.one_lt_top⟩
  have hKopen : IsOpen (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) := by
    have h := (Conductor.levelOpenSubgroup F.Carrier (m + 1) 0).isOpen
    change IsOpen ((Conductor.levelSubgroup F.Carrier (m + 1) 0 : Subgroup _) :
      Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier)) at h
    rwa [Conductor.levelSubgroup_zero] at h
  have hdetq : Continuous (quotientDeterminantAbs (normalizedAbsoluteValue T) m) :=
    (leftQuotient_isOpenQuotientMap
      (upperUnipotent (m + 1) F.Carrier)).isQuotientMap.continuous_iff.mpr
      (habv.comp Units.continuous_val.matrix_det)
  rw [hasFiniteIntegral_iff_enorm, hrec]
  apply lt_top_iff_ne_top.mpr
  refine lintegral_map_withDensity_prod_ne_top (P := fun q => ENNReal.ofReal (Pr q)) (Q := Q)
    (S := (K : Set (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))) ?_
    (continuous_recursiveQuotientCoordinates m).measurable.aemeasurable
    (ae_restrict_mem hKopen.measurableSet) ?_ (fun _ => ENNReal.ofReal_ne_top)
    hPr.lintegral_lt_top.ne ?_ (by rw [hdk]; exact ENNReal.one_ne_top)
  · exact ((hdetq.measurable.inv).ennreal_ofReal).comp measurable_fst
  · intro q' t k hk
    obtain ⟨g, rfl⟩ := Quotient.exists_rep q'
    have hk1 : normalizedAbsoluteValue T (Matrix.det k.val) = 1 :=
      normalizedAbs_det_of_mem_integralSubgroup T hk
    change ENNReal.ofReal ((normalizedAbsoluteValue T (Matrix.det g.val))⁻¹) *
        ‖‖matrixCoefficient π ℓ.val v (recursiveQuotientRepresentative m g t k)‖ ^ 2 *
          ‖Φ (lastRow (recursiveQuotientRepresentative m g t k))‖ ^ 2 *
          normalizedAbsoluteValue T
            (Matrix.det (recursiveQuotientRepresentative m g t k).val) ^ (2 * a)‖ₑ ≤
      ENNReal.ofReal (Pr ⟦g⟧) * Q t
    by_cases hΦ : Φ (lastRow (recursiveQuotientRepresentative m g t k)) = 0
    · simp [hΦ]
    by_cases hW : matrixCoefficient π ℓ.val v (recursiveQuotientRepresentative m g t k) = 0
    · simp [hW]
    have hNt : N ≤ T.ord (t : F.Carrier) := by
      refine hN t k hk ?_
      rwa [recursiveQuotientRepresentative_lastRow] at hΦ
    have hWk := norm_matrixCoefficient_recursiveQuotientRepresentative c ℓ.val v g t k
    have hW' : (modelMap π ℓ (π k v)).val.val (rankInclusion 1 g) ≠ 0 := by
      intro h0
      apply hW
      rw [← norm_eq_zero, hWk]
      exact norm_eq_zero.mpr h0
    have hdg : normalizedAbsoluteValue T (Matrix.det g.val) ≤ C (π k v) := by
      have h := hC (π k v) (rankInclusion 1 g) (rankInclusion_one_lastRow g) hW'
      rw [det_rankInclusion] at h
      exact h
    have hdetR := recursiveQuotientRepresentative_det_abs m (normalizedAbsoluteValue T) g t k
    rw [hk1, mul_one] at hdetR
    have hGw : G (π k v) ⟦g⟧ = ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 := by
      change ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 *
          normalizedAbsoluteValue T (Matrix.det g.val) ^ (-(((0 + 0 : ℕ) : ℝ))) = _
      rw [show (((0 + 0 : ℕ) : ℝ)) = 0 by norm_num, neg_zero, Real.rpow_zero, mul_one]
    have hPge : D (π k v) * ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 ≤
        Pr ⟦g⟧ := by
      rw [← hGw]
      exact Finset.single_le_sum (f := fun w => D w * G w ⟦g⟧)
        (fun w _ => mul_nonneg (hD w) (hG0 w _)) (hS k hk)
    have hdpos : 0 < normalizedAbsoluteValue T (Matrix.det g.val) :=
      (normalizedAbsoluteValue T).pos (Matrix.det_ne_zero_of_left_inverse
        (Matrix.nonsing_inv_mul _ (by
          rw [← Matrix.GeneralLinearGroup.val_det_apply]
          exact (Matrix.GeneralLinearGroup.det g).isUnit)))
    have hdD : normalizedAbsoluteValue T (Matrix.det g.val) ^ (2 * a - 1) ≤ D (π k v) :=
      Real.rpow_le_rpow ((normalizedAbsoluteValue T).nonneg _)
        (hdg.trans (le_max_left _ _)) ha'
    have htρ : (normalizedAbsoluteValue T (t : F.Carrier) ^ (m + 2)) ^ (2 * a) =
        ρ ^ T.ord (t : F.Carrier) := by
      rw [← Real.rpow_natCast_mul ((normalizedAbsoluteValue T).nonneg _)]
      exact normalizedAbs_rpow_eq_zpow_ord T t.ne_zero _
    have hY : ‖Φ (lastRow (recursiveQuotientRepresentative m g t k))‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hM _) 2
    have hPr0 : 0 ≤ Pr ⟦g⟧ := Finset.sum_nonneg fun w _ => mul_nonneg (hD w) (hG0 w _)
    change _ ≤ ENNReal.ofReal (Pr ⟦g⟧) * (ENNReal.ofReal (M ^ 2) *
      {t : F.Carrierˣ | N ≤ T.ord (t : F.Carrier)}.indicator
        (fun t => ENNReal.ofReal (ρ ^ T.ord (t : F.Carrier))) t)
    rw [Set.indicator_of_mem (show t ∈ {t : F.Carrierˣ | N ≤ T.ord (t : F.Carrier)} from hNt),
      Real.enorm_eq_ofReal (by positivity),
      ← ENNReal.ofReal_mul (inv_nonneg.mpr ((normalizedAbsoluteValue T).nonneg _)),
      ← ENNReal.ofReal_mul (sq_nonneg M), ← ENNReal.ofReal_mul hPr0]
    apply ENNReal.ofReal_le_ofReal
    rw [hWk, hdetR, Real.mul_rpow ((normalizedAbsoluteValue T).nonneg _) (by positivity), htρ]
    set d := normalizedAbsoluteValue T (Matrix.det g.val)
    set X := ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖
    set Y := ‖Φ (lastRow (recursiveQuotientRepresentative m g t k))‖
    have hρo : 0 ≤ ρ ^ T.ord (t : F.Carrier) := zpow_nonneg hρ0.le _
    have hdd : d⁻¹ * d ^ (2 * a) = d ^ (2 * a - 1) := by
      rw [Real.rpow_sub hdpos, Real.rpow_one, inv_mul_eq_div]
    calc
      d⁻¹ * (X ^ 2 * Y ^ 2 * (d ^ (2 * a) * ρ ^ T.ord (t : F.Carrier)))
          = (X ^ 2 * (d⁻¹ * d ^ (2 * a))) * (Y ^ 2 * ρ ^ T.ord (t : F.Carrier)) := by ring
      _ = (X ^ 2 * d ^ (2 * a - 1)) * (Y ^ 2 * ρ ^ T.ord (t : F.Carrier)) := by rw [hdd]
      _ ≤ (D (π k v) * X ^ 2) * (M ^ 2 * ρ ^ T.ord (t : F.Carrier)) := by
        apply mul_le_mul _ (mul_le_mul_of_nonneg_right hY hρo) (by positivity)
          (mul_nonneg (hD _) (by positivity))
        rw [mul_comm (D (π k v))]
        exact mul_le_mul_of_nonneg_left hdD (by positivity)
      _ ≤ Pr ⟦g⟧ * (M ^ 2 * ρ ^ T.ord (t : F.Carrier)) :=
        mul_le_mul_of_nonneg_right hPge (by positivity)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_units_indicator_zpow_ord_ne_top T hρ0 hρ1 N)

/-- The standard-character estimate in every rank. -/
theorem unitaryStandardWeightedSquare (n : ℕ) : UnitaryStandardWeightedSquareAt.{uF, uV} F n := by
  cases n with
  | zero => exact unitaryStandardWeightedSquare_zero F
  | succ m => exact unitaryStandardWeightedSquare_succ F m

/-- **The unitary weighted Whittaker square estimate, both character signs.** For an
irreducible admissible unitarizable representation `π` of `GL_(n+1)(F)`, every compatible
quotient measure, every Schwartz–Bruhat function `Φ` and every `a ≥ 1/2`, the weighted squares
of the Whittaker functions of the coefficient models for the standard and for the inverse
standard character are integrable. -/
theorem unitaryWeightedWhittakerSquare (n : ℕ) :
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
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
        ∀ π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V,
          IsAdmissible π → Representation.IsIrreducible π → IsUnitarizable π →
          (∀ (ℓ : glFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
              (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 1 / 2 ≤ a →
            Integrable (fun q => (whittakerNorm ψ f.val q) ^ 2 *
                ‖Φ (quotientLastRow n q)‖ ^ 2 *
                (quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n
                  q) ^ (2 * a)) μ) ∧
          (∀ (ℓ : glInverseFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
              (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 1 / 2 ≤ a →
            Integrable (fun q => (inverseWhittakerNorm ψ f.val q) ^ 2 *
                ‖Φ (quotientLastRow n q)‖ ^ 2 *
                (quotientDeterminantAbs (normalizedAbsoluteValue F.canonicalTopologicalData) n
                  q) ^ (2 * a)) μ) := by
  have hstd := unitaryStandardWeightedSquare.{uF, uV} F n
  intro ψ _ μ hμ V _ _ π hadm hirr hunit
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  refine ⟨hstd ψ μ hμ V π hadm hirr hunit, ?_⟩
  intro ℓ f Φ a ha
  let ψ' : UnitaryAdditiveCharacter F.Carrier := ψ.scale (-1)
  have hθ : standardCharacter ψ' n = inverseStandardCharacter ψ n :=
    standardCharacter_scale_neg_one ψ n
  let ℓ' : glFunctionals ψ' n π :=
    ⟨ℓ.val, by simpa only [glFunctionals, hθ] using ℓ.property⟩
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  refine (hstd ψ' μ hμ V π hadm hirr hunit ℓ' (modelMap π ℓ' v) Φ a ha).congr
    (Filter.Eventually.of_forall fun q => ?_)
  induction q using Quotient.inductionOn with
  | h g => rfl

end Langlands.RankinSelberg.UnitaryGeneric

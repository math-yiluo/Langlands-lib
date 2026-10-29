import Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof
import Langlands.Representation.RankinSelberg.WeightedWhittakerSquareStatement
import Langlands.Representation.RankinSelberg.RecursiveQuotientIntegrationStatement
import Langlands.Representation.RankinSelberg.SquareIntegrableWhittakerRestrictionStatement
import Langlands.Representation.RankinSelberg.UnipotentQuotient
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.FunctionalEquationStatement
import Langlands.Representation.Whittaker.SmoothSimpleRootSupportProof
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.Representation.MatrixCoefficient.LawsProof
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.HarmonicAnalysis.PadicScalarHaarScalingProof
import Langlands.Group.GL.NormalizedCharacter
import Langlands.Group.GL.CartanProof
import Langlands.Group.GL.IntegralSubgroup
import Langlands.LocalField.Uniformizer
import Langlands.LocalField.Topology
import Langlands.LocalField.Normalization.Proof
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Reduction of the weighted Whittaker square estimate

The weighted Whittaker square estimate of JPSS Section 8.3 follows from the
recursive quotient integration formula (printed p.449, (1)) and the corank-one
restricted Whittaker square estimate (printed p.449, (2)). See the paired
Markdown for the route.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV

/-! ### Geometric tails along an integer order -/

section ShellTail

variable {X : Type*} [MeasurableSpace X]

/-- If an integer order has measurable fibres, a measure-preserving map raises it
by one, and the order-zero fibre has finite mass, then `ρ ^ ord` is integrable
on every set `{N ≤ ord}` for `0 < ρ < 1`. -/
theorem lintegral_indicator_zpow_ord_ne_top {μ : Measure X} {ord : X → ℤ}
    (hmeas : ∀ n, MeasurableSet {x | ord x = n})
    {τ : X → X} (hτ : MeasurePreserving τ μ μ) (hτord : ∀ x, ord (τ x) = ord x + 1)
    (hmass : μ {x | ord x = 0} ≠ ⊤) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (N : ℤ) :
    ∫⁻ x, {x | N ≤ ord x}.indicator (fun x => ENNReal.ofReal (ρ ^ ord x)) x ∂μ ≠ ⊤ := by
  set S : ℤ → Set X := fun n => {x | ord x = n} with hS
  have hpre (n : ℤ) : τ ⁻¹' S (n + 1) = S n := by
    ext x
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq, hτord]
    omega
  have hstep (n : ℤ) : μ (S n) = μ (S (n + 1)) := by
    rw [← hpre n]
    exact hτ.measure_preimage (hmeas _).nullMeasurableSet
  have hall (n : ℤ) : μ (S n) = μ (S 0) := by
    induction n using Int.induction_on with
    | zero => rfl
    | succ k ih => rw [← hstep, ih]
    | pred k ih =>
      rw [hstep, show -(k : ℤ) - 1 + 1 = -(k : ℤ) by ring]
      exact ih
  have hU : {x | N ≤ ord x} = ⋃ j : ℕ, S (N + j) := by
    ext x
    simp only [hS, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro h
      exact ⟨(ord x - N).toNat, by omega⟩
    · rintro ⟨j, hj⟩
      omega
  have hUm : MeasurableSet {x | N ≤ ord x} := by
    rw [hU]
    exact MeasurableSet.iUnion fun j => hmeas _
  have hdisj : Pairwise (Function.onFun Disjoint fun j : ℕ => S (N + j)) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun x hi hj => hij ?_
    simp only [hS, Set.mem_ofPred_eq] at hi hj
    omega
  have hterm (j : ℕ) : ∫⁻ x in S (N + j), ENNReal.ofReal (ρ ^ ord x) ∂μ =
      (ENNReal.ofReal (ρ ^ N) * ENNReal.ofReal ρ ^ j) * μ (S 0) := by
    rw [setLIntegral_congr_fun (hmeas _)
      (g := fun _ => ENNReal.ofReal (ρ ^ N) * ENNReal.ofReal ρ ^ j), setLIntegral_const,
      hall]
    intro x hx
    change ord x = N + j at hx
    change ENNReal.ofReal (ρ ^ ord x) = _
    rw [hx, zpow_add₀ hρ0.ne', zpow_natCast, ENNReal.ofReal_mul (zpow_nonneg hρ0.le _),
      ENNReal.ofReal_pow hρ0.le]
  rw [lintegral_indicator hUm, hU, lintegral_iUnion (fun j => hmeas _) hdisj]
  rw [tsum_congr hterm, ENNReal.tsum_mul_right, ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_) hmass
  rw [ENNReal.inv_ne_top]
  exact (tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr hρ1)).ne'

end ShellTail

/-! ### Upper bounds for iterated product integrals -/

section ProductBound

/-- A pointwise product bound on the integral subgroup bounds the integral against a
pushforward of a weighted triple product measure. -/
theorem lintegral_map_withDensity_prod_ne_top {X A B Y : Type*} [MeasurableSpace X]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace Y]
    {μs : Measure X} {dA : Measure A} {dB : Measure B} [SFinite dA] [SFinite dB]
    {c : X × A × B → Y} {w : X × A × B → ENNReal} (hw : Measurable w)
    (hc : AEMeasurable c ((μs.prod (dA.prod dB)).withDensity w))
    {h : Y → ENNReal} {P : X → ENNReal} {Q : A → ENNReal} {S : Set B}
    (hS : ∀ᵐ b ∂dB, b ∈ S)
    (hbound : ∀ x a b, b ∈ S → w (x, a, b) * h (c (x, a, b)) ≤ P x * Q a)
    (hPtop : ∀ x, P x ≠ ⊤) (hP : ∫⁻ x, P x ∂μs ≠ ⊤) (hQ : ∫⁻ a, Q a ∂dA ≠ ⊤)
    (hB : dB Set.univ ≠ ⊤) :
    ∫⁻ y, h y ∂Measure.map c ((μs.prod (dA.prod dB)).withDensity w) ≠ ⊤ := by
  have hinner (x : X) (a : A) :
      ∫⁻ b, (w * (h ∘ c)) (x, a, b) ∂dB ≤ P x * Q a * dB Set.univ := by
    calc
      ∫⁻ b, (w * (h ∘ c)) (x, a, b) ∂dB ≤ ∫⁻ _b, P x * Q a ∂dB := by
        apply lintegral_mono_ae
        filter_upwards [hS] with b hb
        exact hbound x a b hb
      _ = P x * Q a * dB Set.univ := lintegral_const _
  have hmid (x : X) :
      ∫⁻ y, (w * (h ∘ c)) (x, y) ∂(dA.prod dB) ≤
        P x * ((∫⁻ a, Q a ∂dA) * dB Set.univ) := by
    calc
      ∫⁻ y, (w * (h ∘ c)) (x, y) ∂(dA.prod dB)
          ≤ ∫⁻ a, ∫⁻ b, (w * (h ∘ c)) (x, a, b) ∂dB ∂dA :=
        lintegral_prod_le (fun y => (w * (h ∘ c)) (x, y))
      _ ≤ ∫⁻ a, P x * (Q a * dB Set.univ) ∂dA :=
        lintegral_mono fun a => (hinner x a).trans_eq (mul_assoc _ _ _)
      _ = P x * ((∫⁻ a, Q a ∂dA) * dB Set.univ) := by
        rw [lintegral_const_mul' _ _ (hPtop x), lintegral_mul_const' _ _ hB]
  refine ne_of_lt ?_
  calc
    ∫⁻ y, h y ∂Measure.map c ((μs.prod (dA.prod dB)).withDensity w)
        ≤ ∫⁻ z, h (c z) ∂((μs.prod (dA.prod dB)).withDensity w) :=
      lintegral_map_le h hc
    _ ≤ ∫⁻ z, (w * (h ∘ c)) z ∂(μs.prod (dA.prod dB)) :=
      lintegral_withDensity_le_lintegral_mul _ hw _
    _ ≤ ∫⁻ x, ∫⁻ y, (w * (h ∘ c)) (x, y) ∂(dA.prod dB) ∂μs := lintegral_prod_le _
    _ ≤ ∫⁻ x, P x * ((∫⁻ a, Q a ∂dA) * dB Set.univ) ∂μs := lintegral_mono hmid
    _ = (∫⁻ x, P x ∂μs) * ((∫⁻ a, Q a ∂dA) * dB Set.univ) :=
      lintegral_mul_const' _ _ (ENNReal.mul_ne_top hQ hB)
    _ < ⊤ := ENNReal.mul_lt_top hP.lt_top (ENNReal.mul_lt_top hQ.lt_top hB.lt_top)

end ProductBound

/-! ### Local field facts -/

section LocalFieldFacts

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A real power of the normalized absolute value of a nonzero element is an
integer power of `q ^ (-s)` indexed by its order. -/
theorem normalizedAbs_rpow_eq_zpow_ord {x : F.Carrier} (hx : x ≠ 0) (s : ℝ) :
    T.normalizedAbs x ^ s = ((T.residueCardinality : ℝ) ^ (-s)) ^ T.ord x := by
  have hq : (0 : ℝ) ≤ T.residueCardinality := Nat.cast_nonneg _
  rw [T.normalizedAbs_of_ne_zero hx, ← Real.rpow_intCast, ← Real.rpow_mul hq,
    ← Real.rpow_intCast, ← Real.rpow_mul hq]
  congr 1
  push_cast
  ring

/-- For `s > 0`, the base `q ^ (-s)` lies strictly between zero and one. -/
theorem residueCardinality_rpow_neg_mem {s : ℝ} (hs : 0 < s) :
    0 < (T.residueCardinality : ℝ) ^ (-s) ∧ (T.residueCardinality : ℝ) ^ (-s) < 1 := by
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  exact ⟨Real.rpow_pos_of_pos (zero_lt_one.trans hq) _,
    Real.rpow_lt_one_of_one_lt_of_neg hq (neg_lt_zero.mpr hs)⟩

/-- A bound on the normalized absolute value bounds the order from below. -/
theorem exists_ord_lower_bound (R : ℝ) :
    ∃ N : ℤ, ∀ x : F.Carrier, x ≠ 0 → T.normalizedAbs x ≤ R → N ≤ T.ord x := by
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt R hq
  refine ⟨-(k : ℤ), fun x hx hR => ?_⟩
  rw [T.normalizedAbs_of_ne_zero hx] at hR
  have h : (T.residueCardinality : ℝ) ^ (-T.ord x) <
      (T.residueCardinality : ℝ) ^ (k : ℤ) := by
    rw [zpow_natCast]
    exact hR.trans_lt hk
  have := (zpow_lt_zpow_iff_right₀ hq).mp h
  omega

/-- The order-zero units are exactly the integral units. -/
theorem ord_eq_zero_iff_mem_integralUnits_of_units (a : F.Carrierˣ) :
    T.ord (a : F.Carrier) = 0 ↔ a ∈ integralUnits T.Integers := by
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  rw [mem_integralUnits, ← T.normalizedAbs_le_one_iff_mem_integers,
    ← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_of_ne_zero a.ne_zero,
    T.normalizedAbs_of_ne_zero (a⁻¹).ne_zero, Units.val_inv_eq_inv_val, T.ord_inv,
    zpow_le_one_iff_right₀ hq, zpow_le_one_iff_right₀ hq]
  omega

/-- An integral invertible matrix has determinant of normalized absolute value one. -/
theorem normalizedAbs_det_of_mem_integralSubgroup {r : ℕ}
    {k : Langlands.GeneralLinear (r + 1) F.Carrier}
    (hk : k ∈ Conductor.integralSubgroup T.Integers r) :
    T.normalizedAbs (Matrix.det k.val) = 1 := by
  have hmem := (Conductor.mem_integralSubgroup _ _ k).mp hk
  have h1 : Matrix.det k.val ∈ T.Integers :=
    GeneralLinear.Cartan.det_mem_integer _ hmem.1
  have h2 : Matrix.det (k⁻¹).val ∈ T.Integers :=
    GeneralLinear.Cartan.det_mem_integer _ hmem.2
  have hprod : Matrix.det k.val * Matrix.det (k⁻¹).val = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have ha := (T.normalizedAbs_le_one_iff_mem_integers _).mpr h1
  have hb := (T.normalizedAbs_le_one_iff_mem_integers _).mpr h2
  have hab : T.normalizedAbs (Matrix.det k.val) * T.normalizedAbs (Matrix.det (k⁻¹).val) = 1 := by
    rw [← T.normalizedAbs_mul, hprod, T.normalizedAbs_one]
  nlinarith [T.normalizedAbs_nonneg (Matrix.det k.val),
    T.normalizedAbs_nonneg (Matrix.det (k⁻¹).val)]

/-- The normalized absolute value is continuous for the supplied topology. -/
theorem continuous_normalizedAbs' :
    letI := T.topology
    Continuous T.normalizedAbs := by
  let := T.topology
  exact NNReal.continuous_coe.comp T.continuous_normalizedAbsHom

/-- Square-integrability supplies a unitary central character. -/
theorem nonempty_unitaryCentralCharacter_of_isSquareIntegrable {n : ℕ}
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ (Langlands.GeneralLinear n F.Carrier) V}
    (h : T.IsSquareIntegrable ρ) :
    letI := T.topology
    Nonempty (UnitaryCentralCharacter ρ) := by
  let := T.topology
  have := T.generalLinearTopologicalGroup n
  let := T.centralQuotientMeasurableSpace n
  have := T.centralQuotientBorelSpace n
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_centralQuotient n
  obtain ⟨_, c, _⟩ := h μ
  exact ⟨c⟩

/-- Multiplicative geometric tails are integrable for the normalized
multiplicative Haar measure. -/
theorem lintegral_units_indicator_zpow_ord_ne_top :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ [MeasurableSpace F.Carrierˣ] [BorelSpace F.Carrierˣ] {ρ : ℝ}, 0 < ρ → ρ < 1 →
      ∀ N : ℤ,
      ∫⁻ a, {a : F.Carrierˣ | N ≤ T.ord (a : F.Carrier)}.indicator
          (fun a => ENNReal.ofReal (ρ ^ T.ord (a : F.Carrier))) a
        ∂localMultiplicativeHaar F.Carrier ≠ ⊤ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ ρ hρ0 hρ1 N
  let ϖ := LocalFactor.PadicAbelian.uniformizerUnit T
  refine lintegral_indicator_zpow_ord_ne_top
    (ord := fun a : F.Carrierˣ => T.ord (a : F.Carrier)) ?_
    (τ := fun a => ϖ * a) (measurePreserving_mul_left _ ϖ) ?_ ?_ hρ0 hρ1 N
  · intro n
    exact ((isOpen_discrete ({n} : Set ℤ)).preimage (continuous_ord_units T)).measurableSet
  · intro a
    change T.ord ((ϖ : F.Carrier) * (a : F.Carrier)) = T.ord (a : F.Carrier) + 1
    rw [T.ord_mul ϖ.ne_zero a.ne_zero, LocalFactor.PadicAbelian.uniformizerUnit_ord,
      add_comm]
  · have hset : {a : F.Carrierˣ | T.ord (a : F.Carrier) = 0} =
        (integralUnits T.Integers : Set F.Carrierˣ) := by
      ext a
      exact ord_eq_zero_iff_mem_integralUnits_of_units T a
    rw [hset]
    change localMultiplicativeHaar F.Carrier
      (integralUnits (ValuativeRel.valuation F.Carrier).integer : Set F.Carrierˣ) ≠ ⊤
    rw [localMultiplicativeHaar_integerUnits]
    exact ENNReal.one_ne_top

end LocalFieldFacts

/-! ### Continuity of the integrand -/

section Continuity

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

/-- The weighted square integrand is continuous on the quotient for a smooth
representation and a continuous absolute value. -/
theorem continuous_weightedSquareIntegrand {n : ℕ} (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V} (hπ : IsSmooth π)
    (ψ : UnitaryAdditiveCharacter F) (ℓ : glFunctionals ψ n π)
    (f : (coefficientModel π ℓ).toSubmodule) (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (s : ℝ) :
    Continuous (fun q => (whittakerNorm ψ f.val q) ^ 2 * ‖Φ (quotientLastRow n q)‖ ^ 2 *
      (quotientDeterminantAbs abv n q) ^ s) := by
  have hf : Continuous f.val.val := by
    obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
    exact (Langlands.matrixCoefficient_isLocallyConstant π ℓ.val v (hπ v)).continuous
  have hrow : Continuous (lastRow : Langlands.GeneralLinear (n + 1) F → _) := by
    apply continuous_pi
    intro j
    exact (Units.continuous_val.matrix_elem (Fin.last n) j)
  have hdet : Continuous (fun g : Langlands.GeneralLinear (n + 1) F =>
      abv (Matrix.det g.val)) := habv.comp Units.continuous_val.matrix_det
  apply (leftQuotient_isOpenQuotientMap
    (GeneralLinear.upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  refine ((hf.norm.pow 2).mul ((Φ.locallyConstant.continuous.comp hrow).norm.pow 2)).mul ?_
  exact hdet.rpow_const fun g => Or.inl (abv.pos g.det_ne_zero).ne'

end Continuity

/-! ### The standard-sign estimate in a fixed rank -/

/-- The standard-character conjunct of the weighted Whittaker square estimate, for
fixed local field data and rank `n + 1`, with the binders of the published
statement. -/
def StandardWeightedSquareAt {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) (n : ℕ) : Prop :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
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
        Representation.IsIrreducible π → T.IsSquareIntegrable π →
        ∀ (ℓ : glFunctionals ψ n π) (f : (coefficientModel π ℓ).toSubmodule)
            (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)) (a : ℝ), 0 < a →
          Integrable (fun q => (whittakerNorm ψ f.val q) ^ 2 *
              ‖Φ (quotientLastRow n q)‖ ^ 2 *
              (quotientDeterminantAbs (normalizedAbsoluteValue T) n q) ^ (2 * a)) μ

/-! ### Rank one -/

section RankOne

/-- In rank one every element is central, so a unitary central character makes
the norm of a coefficient-model vector constant. -/
theorem norm_coefficientModel_rankOne {F : Type*} [Field F] [TopologicalSpace F]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {π : Representation ℂ (Langlands.GeneralLinear 1 F) V} (c : UnitaryCentralCharacter π)
    (ψ : UnitaryAdditiveCharacter F) (ℓ : glFunctionals ψ 0 π)
    (f : (coefficientModel π ℓ).toSubmodule) (g : Langlands.GeneralLinear 1 F) :
    ‖f.val.val g‖ = ‖f.val.val 1‖ := by
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  have hg : g ∈ Subgroup.center (Langlands.GeneralLinear 1 F) :=
    Subgroup.mem_center_iff.mpr fun h => rankOne_mul_comm h g
  have h : matrixCoefficient π ℓ.val v g =
      (c.character ⟨g, hg⟩ : ℂ) * matrixCoefficient π ℓ.val v 1 := by
    have := c.matrixCoefficient_mul_center ℓ.val v 1 ⟨g, hg⟩
    rwa [one_mul] at this
  change ‖matrixCoefficient π ℓ.val v g‖ = ‖matrixCoefficient π ℓ.val v 1‖
  rw [h, norm_mul, c.norm_eq_one, one_mul]

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- A rank-one matrix whose determinant has order zero is integral. -/
theorem mem_integralSubgroup_rankOne_of_ord_eq_zero
    {g : Langlands.GeneralLinear 1 F.Carrier}
    (hg : T.ord (GeneralLinear.determinant g : F.Carrier) = 0) :
    g ∈ GeneralLinearGroup.integralSubgroup (Fin 1) T.Integers := by
  have hint : ∀ x : F.Carrierˣ, T.ord (x : F.Carrier) = 0 → (x : F.Carrier) ∈ T.Integers := by
    intro x hx
    rw [← T.normalizedAbs_le_one_iff_mem_integers, T.normalizedAbs_of_ne_zero x.ne_zero, hx]
    simp
  have hentry : ∀ (h : Langlands.GeneralLinear 1 F.Carrier) (i j : Fin 1),
      h i j = (GeneralLinear.determinant h : F.Carrier) := by
    intro h i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_fin_one]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (g : Matrix (Fin 1) (Fin 1) F.Carrier) i j ∈ T.Integers
    rw [hentry]
    exact hint _ hg
  · change ((g⁻¹ : Langlands.GeneralLinear 1 F.Carrier) : Matrix (Fin 1) (Fin 1) F.Carrier) i j ∈
      T.Integers
    rw [hentry, map_inv]
    apply hint
    rw [Units.val_inv_eq_inv_val, T.ord_inv, hg, neg_zero]

/-- The weighted square estimate in rank one: the Whittaker norm is constant, the
Schwartz–Bruhat factor is bounded with support in a bounded set, and the
determinant power is a geometric tail. -/
theorem standardWeightedSquare_zero : StandardWeightedSquareAt.{uF, uV} F T 0 := by
  intro ψ _ μ hμ V _ _ π _ hsq ℓ f Φ a ha
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
  have hsmooth : IsSmooth π := hsq.isAdmissible.1
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter_of_isSquareIntegrable T hsq
  have habv : Continuous (normalizedAbsoluteValue T) := continuous_normalizedAbs' T
  refine ⟨(continuous_weightedSquareIntegrand _ habv hsmooth ψ ℓ f Φ
    (2 * a)).aestronglyMeasurable, ?_⟩
  obtain ⟨M, hM⟩ :=
    Φ.locallyConstant.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨R, hR⟩ := Φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn
    ((continuous_normalizedAbs' T).comp (continuous_apply (0 : Fin 1))).continuousOn
  obtain ⟨N, hN⟩ := exists_ord_lower_bound T R
  obtain ⟨hρ0, hρ1⟩ := residueCardinality_rpow_neg_mem T (by positivity : 0 < 2 * a)
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

end RankOne

/-! ### Determinant bound on the support

The lemmas `normalizedAbs_prod`, `diagonal_abs_last` and
`diagonal_abs_bound` are imported from
`Langlands.Representation.RankinSelberg.UnequalRankIwasawaSupportProof`. -/

section DeterminantSupport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A smooth Whittaker coefficient vanishes on every matrix with last row `e_last`
whose determinant is large: the Iwasawa diagonal of such a matrix has a unit last
coordinate, and the simple-root support bound controls the adjacent ratios. -/
theorem exists_normalizedAbs_det_bound (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V), IsSmooth π →
      ∀ (ℓ : glFunctionals ψ r π) (f : (coefficientModel π ℓ).toSubmodule),
      ∃ C : ℝ, ∀ x : Langlands.GeneralLinear (r + 1) F.Carrier,
        (∀ b, x (Fin.last r) b = if Fin.last r = b then 1 else 0) →
        f.val.val x ≠ 0 → T.normalizedAbs (Matrix.det x.val) ≤ C := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro ψ V _ _ π hπ ℓ f
  obtain ⟨R, _hR, hs⟩ := Whittaker.smoothSimpleRootSupport.{uF, uV} F T r ψ V π hπ ℓ f
  let B : ℝ := max 1 R
  have hB : 1 ≤ B := le_max_left _ _
  refine ⟨(B ^ r) ^ (r + 1), fun x hx hf => ?_⟩
  obtain ⟨ϖ, hϖ⟩ := GeneralLinear.Iwasawa.exists_isUniformizingElement F.Carrier
  obtain ⟨u, hu, lam, κ, hκ, hm⟩ := GeneralLinear.Iwasawa.exists_iwasawa hϖ x
  let a : Fin (r + 1) → F.Carrierˣ := fun i => ϖ ^ lam i
  have hm' : x = u * GeneralLinear.Iwasawa.diagonalUnits a * κ := hm
  have hn : f.val.val (GeneralLinear.Iwasawa.diagonalUnits a * κ) ≠ 0 := by
    intro hz
    apply hf
    rw [hm', mul_assoc]
    change f.val.val ((⟨u, hu⟩ : GeneralLinear.upperUnipotent _ F.Carrier).val *
      (GeneralLinear.Iwasawa.diagonalUnits a * κ)) = 0
    rw [f.val.property ⟨u, hu⟩, hz, mul_zero]
  have hlast := diagonal_abs_last F T r x u a κ hx hu hκ hm'
  have habound := diagonal_abs_bound F T r a B hB hlast fun i =>
    (hs a κ hκ hn i).trans (le_max_right _ _)
  have hdetu : Matrix.det u.val = 1 := by
    rw [Matrix.det_of_isUpperTriangular (fun i j hij => hu.1 hij)]
    exact Finset.prod_eq_one fun i _ => hu.2 i
  have hdetκ : T.normalizedAbs (Matrix.det κ.val) = 1 :=
    normalizedAbs_det_of_mem_integralSubgroup T hκ
  rw [hm', Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hdetu, one_mul,
    GeneralLinear.Iwasawa.diagonalUnits_val, Matrix.det_diagonal, T.normalizedAbs_mul, hdetκ,
    mul_one, normalizedAbs_prod]
  calc
    ∏ i, T.normalizedAbs (a i : F.Carrier) ≤ ∏ _i : Fin (r + 1), B ^ r :=
      Finset.prod_le_prod₀ (fun i _ => T.normalizedAbs_nonneg _) (fun i _ => habound i)
    _ = (B ^ r) ^ (r + 1) := by simp

end DeterminantSupport

/-! ### Higher rank -/

section HigherRank

/-- The scalar factor of a recursive representative is central, so a unitary
central character removes it from the norm of a matrix coefficient; the right
factor `k` moves into the vector. -/
theorem norm_matrixCoefficient_recursiveQuotientRepresentative {F : Type*} [Field F]
    [TopologicalSpace F] {V : Type*} [AddCommGroup V] [Module ℂ V] {n : ℕ}
    {π : Representation ℂ (Langlands.GeneralLinear (n + 2) F) V}
    (c : UnitaryCentralCharacter π) (ℓ : Module.Dual ℂ V) (v : V)
    (g : Langlands.GeneralLinear (n + 1) F) (t : Fˣ)
    (k : Langlands.GeneralLinear (n + 2) F) :
    ‖matrixCoefficient π ℓ v (recursiveQuotientRepresentative n g t k)‖ =
      ‖matrixCoefficient π ℓ (π k v) (rankInclusion 1 g)‖ := by
  have hz : (GeneralLinear.scalar t : Langlands.GeneralLinear (n + 2) F) =
      ((GeneralLinear.scalarToCenter t : Subgroup.center (Langlands.GeneralLinear (n + 2) F)) :
        Langlands.GeneralLinear (n + 2) F) := rfl
  rw [recursiveQuotientRepresentative, mul_assoc, Matrix.GeneralLinearGroup.scalar_commute t k,
    ← mul_assoc, hz, c.norm_matrixCoefficient_mul_center, matrixCoefficient_mul]

/-- The last row of `diag(g, 1)` is the last standard basis row. -/
theorem rankInclusion_one_lastRow {F : Type*} [Field F] {n : ℕ}
    (g : Langlands.GeneralLinear (n + 1) F) (b : Fin (n + 1 + 1)) :
    rankInclusion 1 g (Fin.last (n + 1)) b = if Fin.last (n + 1) = b then 1 else 0 := by
  have h := appendIdentity_entry n 1 g (Fin.last (n + 1)) b
  simp only [Fin.val_last, lt_self_iff_false, dite_false] at h
  exact h

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- For a smooth representation, the orbit of a vector under the integral subgroup
is finite. -/
theorem exists_finset_integralOrbit (r : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ {V : Type uV} [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V), IsSmooth π →
      ∀ v : V, ∃ S : Finset V, ∀ k ∈ Conductor.integralSubgroup
        (ValuativeRel.valuation F.Carrier).integer r, π k v ∈ S := by
  classical
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro V _ _ π hπ v
  let K := Conductor.levelOpenSubgroup F.Carrier r 0
  have hK : IsCompact (K : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) :=
    Conductor.isCompact_levelOpenSubgroup F.Carrier r 0
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hS : (Set.range (fun k : K => π k.val v)).Finite :=
    ((Hecke.orbitMap_locallyConstant π (hπ v)).comp_continuous
      continuous_subtype_val).range_finite
  refine ⟨hS.toFinset, fun k hk => ?_⟩
  have hkK : k ∈ K := by
    change k ∈ Conductor.levelSubgroup F.Carrier r 0
    rw [Conductor.levelSubgroup_zero]
    exact hk
  rw [Set.Finite.mem_toFinset]
  exact ⟨⟨k, hkK⟩, rfl⟩

/-- On the support of a Schwartz–Bruhat function evaluated at a scaled integral
last row, the order of the scalar is bounded below. -/
theorem exists_ord_lower_bound_of_lastRow (r : ℕ) :
    letI := T.topology
    ∀ Φ : SchwartzBruhat (Fin (r + 1) → F.Carrier), ∃ N : ℤ,
      ∀ (t : F.Carrierˣ) (k : Langlands.GeneralLinear (r + 1) F.Carrier),
        k ∈ Conductor.integralSubgroup T.Integers r →
        Φ (fun j => (t : F.Carrier) * lastRow k j) ≠ 0 → N ≤ T.ord (t : F.Carrier) := by
  let := T.topology
  intro Φ
  have hcont : Continuous (fun y : Fin (r + 1) → F.Carrier => ∑ j, T.normalizedAbs (y j)) :=
    continuous_finsetSum _ fun j _ => (continuous_normalizedAbs' T).comp (continuous_apply j)
  obtain ⟨R, hR⟩ :=
    Φ.hasCompactSupport.isCompact.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨N, hN⟩ := exists_ord_lower_bound T R
  refine ⟨N, fun t k hk hΦ => hN _ t.ne_zero ?_⟩
  have hmem := (Conductor.mem_integralSubgroup _ _ k).mp hk
  have hy := hR _ (subset_tsupport _ (Function.mem_support.mpr hΦ))
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ => T.normalizedAbs_nonneg _)]
    at hy
  have hone : ∑ j, k (Fin.last r) j * (k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) j
      (Fin.last r) = 1 := by
    have h : ((k : Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier) *
        ((k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) :
          Matrix (Fin (r + 1)) (Fin (r + 1)) F.Carrier)) (Fin.last r) (Fin.last r) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_apply_eq]
    rwa [Matrix.mul_apply] at h
  have ht : (t : F.Carrier) = ∑ j, ((t : F.Carrier) * lastRow k j) *
      (k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) j (Fin.last r) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum]
    change (t : F.Carrier) = (t : F.Carrier) * ∑ j, k (Fin.last r) j *
      (k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) j (Fin.last r)
    rw [hone, mul_one]
  calc
    T.normalizedAbs (t : F.Carrier)
        = T.normalizedAbs (∑ j, ((t : F.Carrier) * lastRow k j) *
            (k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) j (Fin.last r)) := by
      rw [← ht]
    _ ≤ ∑ j, T.normalizedAbs (((t : F.Carrier) * lastRow k j) *
            (k⁻¹ : Langlands.GeneralLinear (r + 1) F.Carrier) j (Fin.last r)) :=
      (normalizedAbsoluteValue T).sum_le _ _
    _ ≤ ∑ j, T.normalizedAbs ((t : F.Carrier) * lastRow k j) := by
      apply Finset.sum_le_sum
      intro j _
      rw [T.normalizedAbs_mul]
      exact mul_le_of_le_one_right (T.normalizedAbs_nonneg _)
        ((T.normalizedAbs_le_one_iff_mem_integers _).mpr (hmem.2 _ _))
    _ ≤ R := hy

/-- The weighted square estimate in rank `m + 2`, from the recursive quotient
integration formula in rank `m + 2` and the corank-one restricted square estimate. -/
theorem standardWeightedSquare_succ (m : ℕ)
    (h1 : RecursiveQuotientIntegrationStatement F T m)
    (h2 : SquareIntegrableWhittakerRestrictionStatement.{uF, uV}) :
    StandardWeightedSquareAt.{uF, uV} F T (m + 1) := by
  classical
  intro ψ _ μ hμ V _ _ π hirr hsq ℓ f Φ a ha
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
  have hsmooth : IsSmooth π := hsq.isAdmissible.1
  obtain ⟨c⟩ := nonempty_unitaryCentralCharacter_of_isSquareIntegrable T hsq
  have habv : Continuous (normalizedAbsoluteValue T) := continuous_normalizedAbs' T
  refine ⟨(continuous_weightedSquareIntegrand _ habv hsmooth ψ ℓ f Φ
    (2 * a)).aestronglyMeasurable, ?_⟩
  -- The recursive integration formula, with the actual smaller quotient measure.
  let μs := unipotentQuotientHaar F.Carrier m
  have hμs := unipotentQuotientHaar_isCompatible F.Carrier m
  have hrec := h1 μs μ hμs hμ
  -- The vector, its integral orbit, and the determinant bounds of the orbit.
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  obtain ⟨S, hS⟩ := exists_finset_integralOrbit T (m + 1) π hsmooth v
  choose C hC using fun w : V =>
    exists_normalizedAbs_det_bound F T (m + 1) ψ V π hsmooth ℓ (modelMap π ℓ w)
  let D : V → ℝ := fun w => max (C w) 1 ^ (2 * a)
  have hD (w : V) : 0 ≤ D w := Real.rpow_nonneg (zero_le_one.trans (le_max_right _ _)) _
  let G : V → LeftUnipotentQuotient m F.Carrier → ℝ := fun w q =>
    restrictedWhittakerNorm ψ 0 (modelMap π ℓ w).val q ^ 2 *
      quotientDeterminantAbs (normalizedAbsoluteValue T) m q ^ (-(((0 + 0 + 1 : ℕ) : ℝ)))
  have hG (w : V) : Integrable (G w) μs :=
    h2 p F T m 0 ψ μs hμs V π hirr hsq ℓ (modelMap π ℓ w)
  have hG0 (w : V) (q : LeftUnipotentQuotient m F.Carrier) : 0 ≤ G w q :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (quotientDeterminantAbs_nonneg _ _ _) _)
  let Pr : LeftUnipotentQuotient m F.Carrier → ℝ := fun q => ∑ w ∈ S, D w * G w q
  have hPr : Integrable Pr μs := integrable_finsetSum S fun w _ => (hG w).const_mul (D w)
  -- The scalar coordinate.
  obtain ⟨M, hM⟩ :=
    Φ.locallyConstant.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  obtain ⟨N, hN⟩ := exists_ord_lower_bound_of_lastRow T (m + 1) Φ
  obtain ⟨hρ0, hρ1⟩ := residueCardinality_rpow_neg_mem T
    (by positivity : 0 < ((m + 2 : ℕ) : ℝ) * (2 * a))
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
    have hGw : G (π k v) ⟦g⟧ = ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 *
        (normalizedAbsoluteValue T (Matrix.det g.val))⁻¹ := by
      change ‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 *
          normalizedAbsoluteValue T (Matrix.det g.val) ^ (-(((0 + 0 + 1 : ℕ) : ℝ))) = _
      rw [show (((0 + 0 + 1 : ℕ) : ℝ)) = 1 by norm_num, Real.rpow_neg_one]
    have hPge : D (π k v) * (‖matrixCoefficient π ℓ.val (π k v) (rankInclusion 1 g)‖ ^ 2 *
        (normalizedAbsoluteValue T (Matrix.det g.val))⁻¹) ≤ Pr ⟦g⟧ := by
      rw [← hGw]
      exact Finset.single_le_sum (f := fun w => D w * G w ⟦g⟧)
        (fun w _ => mul_nonneg (hD w) (hG0 w _)) (hS k hk)
    have hdD : normalizedAbsoluteValue T (Matrix.det g.val) ^ (2 * a) ≤ D (π k v) :=
      Real.rpow_le_rpow ((normalizedAbsoluteValue T).nonneg _)
        (hdg.trans (le_max_left _ _)) (by positivity)
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
    have hd0 : 0 ≤ d := (normalizedAbsoluteValue T).nonneg _
    have hρo : 0 ≤ ρ ^ T.ord (t : F.Carrier) := zpow_nonneg hρ0.le _
    calc
      d⁻¹ * (X ^ 2 * Y ^ 2 * (d ^ (2 * a) * ρ ^ T.ord (t : F.Carrier)))
          = (X ^ 2 * d⁻¹ * d ^ (2 * a)) * (Y ^ 2 * ρ ^ T.ord (t : F.Carrier)) := by ring
      _ ≤ (D (π k v) * (X ^ 2 * d⁻¹)) * (M ^ 2 * ρ ^ T.ord (t : F.Carrier)) := by
        apply mul_le_mul _ (mul_le_mul_of_nonneg_right hY hρo) (by positivity)
          (mul_nonneg (hD _) (by positivity))
        rw [mul_comm (D (π k v))]
        exact mul_le_mul_of_nonneg_left hdD (by positivity)
      _ ≤ Pr ⟦g⟧ * (M ^ 2 * ρ ^ T.ord (t : F.Carrier)) :=
        mul_le_mul_of_nonneg_right hPge (by positivity)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (lintegral_units_indicator_zpow_ord_ne_top T hρ0 hρ1 N)

end HigherRank

/-! ### Both character signs -/

section Assembly

/-- The standard-sign estimate in every rank, from the recursive quotient integration
formula in every rank and the corank-one restricted square estimate. -/
theorem standardWeightedSquare_of {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
    (T : F.TopologicalData)
    (h1 : ∀ m : ℕ, RecursiveQuotientIntegrationStatement F T m)
    (h2 : SquareIntegrableWhittakerRestrictionStatement.{uF, uV}) (n : ℕ) :
    StandardWeightedSquareAt.{uF, uV} F T n := by
  cases n with
  | zero => exact standardWeightedSquare_zero T
  | succ m => exact standardWeightedSquare_succ T m (h1 m) h2

/-- The weighted Whittaker square estimate for both character signs, from the
recursive quotient integration formula and the corank-one restricted square
estimate. The inverse sign is the standard sign for the additive character
`x ↦ ψ(-x)`: an inverse-character functional for `ψ` is a standard-character
functional for `ψ.scale (-1)` with the same coefficient functions. -/
theorem weightedWhittakerSquare_of
    (h1 : ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (m : ℕ), RecursiveQuotientIntegrationStatement F T m)
    (h2 : SquareIntegrableWhittakerRestrictionStatement.{uF, uV}) :
    WeightedWhittakerSquareStatement.{uF, uV} := by
  intro p _ F T n
  have hstd := standardWeightedSquare_of T (h1 F T) h2 n
  intro ψ _ μ hμ V _ _ π hirr hsq
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  refine ⟨hstd ψ μ hμ V π hirr hsq, ?_⟩
  intro ℓ f Φ a ha
  let ψ' : UnitaryAdditiveCharacter F.Carrier := ψ.scale (-1)
  have hθ : standardCharacter ψ' n = inverseStandardCharacter ψ n :=
    standardCharacter_scale_neg_one ψ n
  let ℓ' : glFunctionals ψ' n π :=
    ⟨ℓ.val, by simpa only [glFunctionals, hθ] using ℓ.property⟩
  obtain ⟨v, rfl⟩ := modelMap_surjective π ℓ f
  refine (hstd ψ' μ hμ V π hirr hsq ℓ' (modelMap π ℓ' v) Φ a ha).congr
    (Filter.Eventually.of_forall fun q => ?_)
  induction q using Quotient.inductionOn with
  | h g => rfl

end Assembly

end Langlands.RankinSelberg

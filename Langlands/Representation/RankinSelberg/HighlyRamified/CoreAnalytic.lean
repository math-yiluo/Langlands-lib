import Langlands.Representation.RankinSelberg.HighlyRamified.ShellDischarge
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.HighlyRamified.DualMatrix
import Langlands.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.Representation.RankinSelberg.EqualRankLastRowReductionProof

/-!
# Analytic glue for the adjacent-rank step

Small facts used to assemble the Jacquet–Shalika §4.4 core: the conductor-`0` hypothesis in
the form `HasIntegerConductorAt`, continuity of corank-one integrands of smooth functions,
smoothness, unipotent equivariance and shell-wise compact support of the restriction
`F_A(g) = U(diag(g,1)) |det g|^(-1/2)`, local constancy and compact support of the weight
`dualWeightFourier`, and the unipotent equivariance of `A ↦ W(M(diag(A,1)))`.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration Matrix Langlands.GeneralLinear
open Filter

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance coreAnalyticFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance coreAnalyticValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance coreAnalyticLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance coreAnalyticFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance coreAnalyticFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance coreAnalyticGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance coreAnalyticGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreAnalyticUnipotentMeasurable (r : ℕ) : MeasurableSpace
    (upperUnipotent (r + 1) F.Carrier) := borel _
local instance coreAnalyticUnipotentBorel (r : ℕ) : BorelSpace
    (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance coreAnalyticQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := borel _
local instance coreAnalyticQuotientBorel (r : ℕ) : BorelSpace
    (LeftQuotient (upperUnipotent (r + 1) F.Carrier)) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- An additive character of conductor exponent `0` has conductor `O` in the sense of
`HasIntegerConductorAt`. -/
theorem hasIntegerConductorAt_of_additiveConductor_eq_zero
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : F.canonicalTopologicalData.additiveConductor ψ = 0) : HasIntegerConductorAt F ψ := by
  obtain ⟨h1, h2⟩ := hasIntegerConductor_of_additiveConductor_eq_zero F ψ hψ
  refine ⟨h1, fun t ht => ?_⟩
  by_contra hall
  apply ht
  apply h2 t
  intro y hy
  have hc : ψ.complex (y * t) = 1 := by
    by_contra hne
    exact hall ⟨y, hy, hne⟩
  rw [UnitaryAdditiveCharacter.complex_apply, mul_comm] at hc
  exact Circle.ext (by simpa using hc)

variable {m : ℕ}

/-- The determinant weight is invariant under right multiplication by `GL_(m+1)(O)`. -/
theorem determinantWeight_mul_integral (g k : Langlands.GeneralLinear (m + 1) F.Carrier)
    (hk : k ∈ Conductor.levelOpenSubgroup F.Carrier m 0) (s : ℂ) :
    determinantWeight abv (g * k) s = determinantWeight abv g s := by
  have hk' : k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer m := by
    rw [← Conductor.levelSubgroup_zero]; exact hk
  have h1 := normalizedAbs_det_of_mem_integralSubgroup F.canonicalTopologicalData hk'
  unfold determinantWeight
  rw [Units.val_mul, Matrix.det_mul, map_mul, normalizedAbsoluteValue_apply,
    normalizedAbsoluteValue_apply, h1, mul_one]

/-- Corank-one integrands of right-invariant functions are continuous. -/
theorem continuous_corankOneIntegrand (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ m)
    (L₁ : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hW : ∀ g l, l ∈ L₁ → W.val (g * l) = W.val g)
    (L₂ : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hW' : ∀ g l, l ∈ L₂ → W'.val (g * l) = W'.val g) (s : ℂ) :
    Continuous (corankOneIntegrand ψ abv W W' s) := by
  apply LastRowReduction.continuous_descend
  apply LastRowReduction.continuous_of_rightInvariant
    (L₁.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous ⊓ L₂ ⊓
      Conductor.levelOpenSubgroup F.Carrier m 0)
  intro x j hj
  unfold corankOneFunction
  rw [map_mul, hW _ _ hj.1.1, hW' _ _ hj.1.2, determinantWeight_mul_integral F x j hj.2]

/-- Corank-one integrands of right-invariant functions are measurable. -/
theorem measurable_corankOneIntegrand (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ m)
    (L₁ : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hW : ∀ g l, l ∈ L₁ → W.val (g * l) = W.val g)
    (L₂ : OpenSubgroup (Langlands.GeneralLinear (m + 1) F.Carrier))
    (hW' : ∀ g l, l ∈ L₂ → W'.val (g * l) = W'.val g) (s : ℂ) :
    Measurable (corankOneIntegrand ψ abv W W' s) :=
  (continuous_corankOneIntegrand F ψ W W' L₁ hW L₂ hW' s).measurable

/-- The restriction `F_A` of a right-invariant function is right invariant. -/
theorem corankRestriction_mul (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1))
    (L : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hU : ∀ g l, l ∈ L → U.val (g * l) = U.val g) :
    ∀ g l, l ∈ L.comap (rankInclusion 1) (rankInclusionContinuous 1).continuous ⊓
        Conductor.levelOpenSubgroup F.Carrier m 0 →
      corankRestriction F ψ U (g * l) = corankRestriction F ψ U g := by
  intro g l hl
  unfold corankRestriction
  rw [map_mul, hU _ _ hl.1, determinantWeight_mul_integral F g l hl.2]

/-- The restriction `F_A` transforms by `ψ_N` under left unipotent translation. -/
theorem corankRestriction_unipotent (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1)) (u : upperUnipotent (m + 1) F.Carrier)
    (g : Langlands.GeneralLinear (m + 1) F.Carrier) :
    corankRestriction F ψ U (u.val * g) =
      (standardCharacter ψ m u : ℂ) * corankRestriction F ψ U g := by
  unfold corankRestriction
  rw [determinantWeight_unipotent_mul, map_mul]
  change U.val ((corankOneUnipotent u).val * rankInclusion 1 g) * _ = _
  rw [U.property, corankOne_standardCharacter, mul_assoc]

/-- On each determinant shell, the restriction `F_A` of a right-invariant Whittaker function
is supported in `N C` for a compact set `C`. -/
theorem corankRestriction_shell_compact (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1))
    (L : OpenSubgroup (Langlands.GeneralLinear (m + 1 + 1) F.Carrier))
    (hU : ∀ g l, l ∈ L → U.val (g * l) = U.val g) (j : ℤ) :
    ∃ C : Set (Langlands.GeneralLinear (m + 1) F.Carrier), IsCompact C ∧
      ∀ g, F.canonicalTopologicalData.ord (determinant g : F.Carrier) = j →
        corankRestriction F ψ U g ≠ 0 →
        ∃ u : upperUnipotent (m + 1) F.Carrier, u.val * g ∈ C := by
  set T := F.canonicalTopologicalData with hTdef
  obtain ⟨R, hR, hroot⟩ := CommonLevel.root_bound F T (m + 1) ψ (fun _ => U) L.toSubgroup
    L.isOpen (fun _ g k => hU g k k.property)
  set M : ℝ := max R 1 ^ (m + 1) with hMdef
  have hM1 : 1 ≤ M := one_le_pow₀ (le_max_right _ _)
  set c : ℝ := (T.residueCardinality : ℝ) ^ (-j) / M ^ m with hcdef
  have hq : (1 : ℝ) < T.residueCardinality := by
    exact_mod_cast T.residueCardinality_gt_one
  have hc : 0 < c :=
    div_pos (zpow_pos (zero_lt_one.trans hq) _) (pow_pos (zero_lt_one.trans_le hM1) _)
  set A : Set (Fin (m + 1) → F.Carrierˣ) := Set.univ.pi fun _ =>
    {a : F.Carrierˣ | c ≤ T.normalizedAbs (a : F.Carrier) ∧ T.normalizedAbs (a : F.Carrier) ≤ M}
    with hAdef
  set K : Set (Langlands.GeneralLinear (m + 1) F.Carrier) :=
    (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer m :
      Set (Langlands.GeneralLinear (m + 1) F.Carrier)) with hKdef
  have hA : IsCompact A := isCompact_univ_pi fun _ => isCompact_normalizedAbs_annulus_units T hc
  have hK : IsCompact K := by
    rw [hKdef, ← Conductor.levelSubgroup_zero]
    exact Conductor.isCompact_levelOpenSubgroup F.Carrier m 0
  refine ⟨(fun x : (Fin (m + 1) → F.Carrierˣ) × Langlands.GeneralLinear (m + 1) F.Carrier =>
      Iwasawa.diagonalUnits x.1 * x.2) '' (A ×ˢ K),
    (hA.prod hK).image (((GeneralLinear.continuous_diagonalUnits (m + 1)).comp
      continuous_fst).mul continuous_snd), ?_⟩
  intro g hj hne
  have hW : U.val (rankInclusion 1 g) ≠ 0 := by
    intro h
    apply hne
    unfold corankRestriction
    rw [h, zero_mul]
  obtain ⟨u, hu, a, κ, hκ, rfl⟩ :=
    CommonLevel.exists_unipotent_diagonal_integral (ValuativeRel.valuation F.Carrier) g
  have hWD : U.val (rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) ≠ 0 := by
    intro h
    apply hW
    rw [map_mul]
    change U.val ((corankOneUnipotent ⟨u, hu⟩).val *
      rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) = 0
    rw [U.property, h, mul_zero]
  have hupper : ∀ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ M :=
    CommonLevel.corank_diagonal_upper T m ψ U hR (hroot 0) a κ hκ hWD
  have hdet : (GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) :
      F.Carrier) = (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) * Matrix.det κ.val := by
    rw [determinant_unipotent_mul ⟨u, hu⟩]
    change Matrix.det ((Iwasawa.diagonalUnits a).val * κ.val) = _
    rw [Matrix.det_mul, Iwasawa.diagonalUnits_val, Matrix.det_diagonal]
  have hprod : T.normalizedAbs (∏ i, ((a i : F.Carrierˣ) : F.Carrier)) =
      ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) := by
    rw [← normalizedAbsoluteValue_apply, map_prod]
    rfl
  have hslice : T.normalizedAbs (GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) :
      F.Carrier) = (T.residueCardinality : ℝ) ^ (-j) := by
    rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant _).ne_zero, hj]
  have hall : ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) =
      (T.residueCardinality : ℝ) ^ (-j) := by
    rw [← hslice, hdet, T.normalizedAbs_mul, hprod,
      normalizedAbs_det_of_mem_integralSubgroup T hκ, mul_one]
  have hlower : ∀ i, c ≤ T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) := by
    intro i
    have herase : ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : F.Carrierˣ) : F.Carrier)
        ≤ M ^ m := by
      calc ∏ j ∈ Finset.univ.erase i, T.normalizedAbs ((a j : F.Carrierˣ) : F.Carrier)
          ≤ ∏ _j ∈ Finset.univ.erase i, M :=
            Finset.prod_le_prod₀ (fun j _ => T.normalizedAbs_nonneg _) fun j _ => hupper j
        _ = M ^ m := by
          rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
            Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel]
    rw [hcdef, div_le_iff₀ (pow_pos (zero_lt_one.trans_le hM1) _), ← hall,
      ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)]
    exact mul_le_mul_of_nonneg_left herase (T.normalizedAbs_nonneg _)
  refine ⟨(⟨u, hu⟩ : upperUnipotent (m + 1) F.Carrier)⁻¹, ⟨(a, κ), ⟨fun i _ =>
    ⟨hlower i, hupper i⟩, hκ⟩, ?_⟩⟩
  change Iwasawa.diagonalUnits a * κ = u⁻¹ * (u * (Iwasawa.diagonalUnits a * κ))
  group

/-- The weight `dualWeightFourier` has compact support. -/
theorem dualWeightFourier_hasCompactSupport (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrier) (c f : ℕ) (T : Finset (Fin (m + 1) → F.Carrier)) :
    HasCompactSupport (dualWeightFourier F ψ ω ϖ c f T) := by
  have := localField_t2 F.Carrier
  have hO : IsCompact ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier) :=
    isCompact_integer F
  apply HasCompactSupport.intro (K := Set.univ.pi fun _ : Fin 1 => Set.univ.pi fun _ :
    Fin (m + 1) => ((ValuativeRel.valuation F.Carrier).integer : Set F.Carrier))
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hO)
  intro x hx
  unfold dualWeightFourier
  refine ite_eq_right_of_eq_false _ _ (eq_false fun hall => hx ?_)
  intro i _ k _
  rw [Fin.fin_one_eq_zero i]
  simpa using hall k.rev

/-- A complex additive character trivial on `O` is locally constant along any continuous
map. -/
theorem eventually_character_eq (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) {X : Type*} [TopologicalSpace X] (L : X → F.Carrier)
    (hL : Continuous L) (x : X) :
    ∀ᶠ y in nhds x, ψ.complex (L y) = ψ.complex (L x) := by
  have hO : IsOpen {t : F.Carrier | t - L x ∈ (ValuativeRel.valuation F.Carrier).integer} :=
    (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).preimage
      (continuous_id.sub continuous_const)
  have hmem : L x ∈ {t : F.Carrier | t - L x ∈ (ValuativeRel.valuation F.Carrier).integer} := by
    simp only [Set.mem_ofPred_eq, sub_self]
    exact Subring.zero_mem _
  filter_upwards [hL.continuousAt.preimage_mem_nhds (hO.mem_nhds hmem)] with y hy
  have hy' : L y - L x ∈ (ValuativeRel.valuation F.Carrier).integer := hy
  have hsplit : L y = L x + (L y - L x) := by ring
  rw [hsplit, AddChar.map_add_eq_mul, UnitaryAdditiveCharacter.complex_apply (ψ := ψ) (L y - L x),
    hψ.trivial _ hy']
  simp

/-- The weight `dualWeightFourier` is locally constant. -/
theorem dualWeightFourier_isLocallyConstant (ψ : UnitaryAdditiveCharacter F.Carrier)
    (hψ : HasIntegerConductorAt F ψ) (ω : F.Carrierˣ →* ℂˣ) (ϖ : F.Carrier) (c f : ℕ)
    (T : Finset (Fin (m + 1) → F.Carrier)) :
    IsLocallyConstant (dualWeightFourier F ψ ω ϖ c f T) := by
  classical
  have := localField_t2 F.Carrier
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  set E : Set (Matrix (Fin 1) (Fin (m + 1)) F.Carrier) :=
    {y | ∀ k : Fin (m + 1), y 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer} with hE
  have hcoord : ∀ k : Fin (m + 1),
      Continuous fun y : Matrix (Fin 1) (Fin (m + 1)) F.Carrier => y 0 k.rev :=
    fun k => (continuous_apply k.rev).comp (continuous_apply 0)
  have hEo : IsOpen E := by
    rw [hE, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun k =>
      (Valuation.isOpen_integer (v := ValuativeRel.valuation F.Carrier)).preimage (hcoord k)
  have hEc : IsClosed E := by
    rw [hE, Set.ofPred_forall]
    exact isClosed_iInter fun k => (isCompact_integer F).isClosed.preimage (hcoord k)
  by_cases hx : x ∈ E
  · have hsum : ∀ z : Fin (m + 1) → F.Carrier, Continuous fun y : Matrix (Fin 1) (Fin (m + 1))
        F.Carrier => ∑ k, z k * y 0 k.rev :=
      fun z => continuous_finsetSum _ fun k _ => continuous_const.mul (hcoord k)
    have hev : ∀ᶠ y in nhds x, ∀ z ∈ T,
        ψ.complex (∑ k, z k * y 0 k.rev) = ψ.complex (∑ k, z k * x 0 k.rev) :=
      (Filter.eventually_all_finset T).mpr fun z _ =>
        eventually_character_eq F ψ hψ _ (hsum z) x
    filter_upwards [hEo.mem_nhds hx, hev] with y hy hyz
    have hy' : ∀ k : Fin (m + 1), y 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer := hy
    have hx' : ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer := hx
    unfold dualWeightFourier
    rw [ite_eq_left_of_eq_true _ _ (eq_true hy'), ite_eq_left_of_eq_true _ _ (eq_true hx')]
    exact Finset.sum_congr rfl fun z hz => by rw [hyz z hz]
  · filter_upwards [hEc.isOpen_compl.mem_nhds hx] with y hy
    have hy' : ¬ ∀ k : Fin (m + 1), y 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer := hy
    have hx' : ¬ ∀ k : Fin (m + 1), x 0 k.rev ∈ (ValuativeRel.valuation F.Carrier).integer := hx
    unfold dualWeightFourier
    rw [ite_eq_right_of_eq_false _ _ (eq_false hy'), ite_eq_right_of_eq_false _ _ (eq_false hx')]

/-- `A ↦ W(M(diag(A,1)))` transforms by `ψ_N⁻¹` under left unipotent translation. -/
theorem whittaker_dualConj_unipotent (ψ : UnitaryAdditiveCharacter F.Carrier)
    (W : WhittakerFunctions ψ (m + 2)) (u : upperUnipotent (m + 1) F.Carrier)
    (A : Langlands.GeneralLinear (m + 1) F.Carrier) :
    W.val (dualConj (rankInclusion 1 (u.val * A))) =
      ((standardCharacter ψ m u : ℂ))⁻¹ * W.val (dualConj (rankInclusion 1 A)) := by
  rw [map_mul, map_mul]
  change W.val ((reflectedUnipotent (corankOneUnipotent (corankOneUnipotent u))).val *
    dualConj (rankInclusion 1 A)) = _
  rw [W.property, standardCharacter_reflected]
  change (((standardCharacter ψ (m + 1 + 1) (corankOneUnipotent (corankOneUnipotent u)))⁻¹ :
    ℂˣ) : ℂ) * _ = _
  rw [corankOne_standardCharacter, corankOne_standardCharacter, Units.val_inv_eq_inv_val]

end Langlands.RankinSelberg.HighlyRamified

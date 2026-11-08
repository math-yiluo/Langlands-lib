import Langlands.Representation.RankinSelberg.HighlyRamified.ShellExpansion
import Langlands.Representation.RankinSelberg.DeterminantSlices
import Langlands.Representation.RankinSelberg.CorankCommonCompactSupport
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange

/-!
# Determinant shells of the corank-one integral

On `N_(m+1) \ GL_(m+1)`, the corank-one integrand at `s` is the integrand at `0` times
`(q^(-s))^(ord det)`. For a smooth Whittaker function `U` on `GL_(m+2)`, the function
`g ↦ U(diag(g,1))` vanishes unless `ord det g` is bounded below. Consequently, if the
corank-one integral converges absolutely at one real point and is the constant `K` on a right
half-plane, its shell integrals at `0` are `K` on the shell `ord det = 0` and `0` elsewhere.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open MeasureTheory HarmonicAnalysis QuotientIntegration GeneralLinear

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance corankShellsFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance corankShellsValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance corankShellsLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance corankShellsQuotientMeasurable (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance corankShellsQuotientBorel (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

variable {m : ℕ}

/-- `|det g|^s = (q^(-s))^(ord det g)`. -/
theorem determinantWeight_eq_spectral (g : GeneralLinear (m + 1) F.Carrier) (s : ℂ) :
    determinantWeight abv g s =
      spectralPoint qF s ^ F.canonicalTopologicalData.ord (determinant g : F.Carrier) := by
  apply determinantWeight_eq_spectralPoint_zpow qF
    (lt_trans zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one)
  rw [normalizedAbsoluteValue_apply]
  exact F.canonicalTopologicalData.normalizedAbs_of_ne_zero (determinant g).ne_zero

/-- The corank-one integrand at `s` is the integrand at `0` times `(q^(-s))^(ord det)`. -/
theorem corankOneIntegrand_eq_mul_spectral (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ m) (s : ℂ)
    (q : LeftUnipotentQuotient m F.Carrier) :
    corankOneIntegrand ψ abv U W' s q =
      corankOneIntegrand ψ abv U W' 0 q *
        spectralPoint qF s ^ determinantOrder F.canonicalTopologicalData m q := by
  induction q using Quotient.inductionOn with
  | h g =>
    rw [corankOneIntegrand_mk, corankOneIntegrand_mk, determinantOrder_mk,
      ← determinantWeight_eq_spectral]
    have hne : ((abv (Matrix.det g.val) : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]
      exact AbsoluteValue.ne_zero _ g.det_ne_zero
    have hw : determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g (0 - 1 / 2) * determinantWeight abv g s := by
      unfold determinantWeight
      rw [← Complex.cpow_add _ _ hne]
      ring_nf
    rw [hw]
    ring

/-- A smooth Whittaker function `U` on `GL_(m+2)` restricted to `diag(g,1)` vanishes unless
`ord det g` is bounded below. -/
theorem exists_order_lower_bound (ψ : UnitaryAdditiveCharacter F.Carrier)
    (U : WhittakerFunctions ψ (m + 1))
    (K : Subgroup (GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsOpen (K : Set (GeneralLinear (m + 1 + 1) F.Carrier)))
    (hU : ∀ g (k : K), U.val (g * k) = U.val g) :
    ∃ j₀ : ℤ, ∀ g : GeneralLinear (m + 1) F.Carrier, U.val (rankInclusion 1 g) ≠ 0 →
      j₀ ≤ F.canonicalTopologicalData.ord (determinant g : F.Carrier) := by
  set T := F.canonicalTopologicalData with hT
  obtain ⟨R, hR, hroot⟩ := CommonLevel.root_bound F T (m + 1) ψ (fun _ => U) K hK
    (fun _ g k => hU g k)
  set M : ℝ := max R 1 ^ (m + 1) with hM
  have hq : (1 : ℝ) < T.residueCardinality := by exact_mod_cast T.residueCardinality_gt_one
  obtain ⟨N, hN⟩ := pow_unbounded_of_one_lt (M ^ (m + 1)) hq
  refine ⟨-(N : ℤ), fun g hg => ?_⟩
  obtain ⟨u, hu, a, κ, hκ, rfl⟩ :=
    CommonLevel.exists_unipotent_diagonal_integral (ValuativeRel.valuation F.Carrier) g
  have hWD : U.val (rankInclusion 1 (Iwasawa.diagonalUnits a * κ)) ≠ 0 := by
    intro h
    apply hg
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
  have hM1 : 0 ≤ M := by positivity
  have habs : T.normalizedAbs (GeneralLinear.determinant (u * (Iwasawa.diagonalUnits a * κ)) :
      F.Carrier) ≤ M ^ (m + 1) := by
    rw [hdet, T.normalizedAbs_mul, hprod, normalizedAbs_det_of_mem_integralSubgroup T hκ,
      mul_one]
    calc ∏ i, T.normalizedAbs ((a i : F.Carrierˣ) : F.Carrier) ≤ ∏ _i : Fin (m + 1), M :=
          Finset.prod_le_prod₀ (fun i _ => T.normalizedAbs_nonneg _) fun i _ => hupper i
      _ = M ^ (m + 1) := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [T.normalizedAbs_of_ne_zero (GeneralLinear.determinant _).ne_zero] at habs
  have h2 : (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant
      (u * (Iwasawa.diagonalUnits a * κ)) : F.Carrier)) <
      (T.residueCardinality : ℝ) ^ (N : ℤ) := by
    rw [zpow_natCast]
    exact habs.trans_lt hN
  have h3 := (zpow_lt_zpow_iff_right₀ hq).mp h2
  omega

/-- Shell coefficients of a constant corank-one integral. -/
theorem corankOne_shell_eq_of_const (ψ : UnitaryAdditiveCharacter F.Carrier)
    (μ : Measure (LeftUnipotentQuotient m F.Carrier))
    (U : WhittakerFunctions ψ (m + 1)) (W' : InverseWhittakerFunctions ψ m)
    (K : Subgroup (GeneralLinear (m + 1 + 1) F.Carrier))
    (hK : IsOpen (K : Set (GeneralLinear (m + 1 + 1) F.Carrier)))
    (hU : ∀ g (k : K), U.val (g * k) = U.val g)
    (s₀ : ℝ) (hint : Integrable (corankOneIntegrand ψ abv U W' s₀) μ)
    (C : ℂ) (a : ℝ) (hC : ∀ s : ℂ, a < s.re → corankOneIntegral ψ abv μ U W' s = C) (j : ℤ) :
    ∫ q in determinantSlice F.canonicalTopologicalData m j,
        corankOneIntegrand ψ abv U W' 0 q ∂μ = if j = 0 then C else 0 := by
  obtain ⟨j₀, hj₀⟩ := exists_order_lower_bound F ψ U K hK hU
  have hq : 1 < qF := F.canonicalTopologicalData.residueCardinality_gt_one
  refine shell_integral_eq_of_const μ (determinantOrder F.canonicalTopologicalData m) hq
    (fun j => measurableSet_determinantSlice F.canonicalTopologicalData m j)
    (corankOneIntegrand ψ abv U W' 0) j₀ ?_ s₀ ?_ C a ?_ j
  · intro q hq0
    induction q using Quotient.inductionOn with
    | h g =>
      rw [determinantOrder_mk]
      apply hj₀ g
      intro h0
      apply hq0
      rw [corankOneIntegrand_mk, h0, zero_mul, zero_mul]
  · refine hint.congr (Filter.Eventually.of_forall fun q => ?_)
    rw [corankOneIntegrand_eq_mul_spectral F ψ U W' s₀ q]
  · intro s hs
    rw [← hC s hs]
    unfold corankOneIntegral
    congr 1
    funext q
    rw [corankOneIntegrand_eq_mul_spectral F ψ U W' s q]

end Langlands.RankinSelberg.HighlyRamified

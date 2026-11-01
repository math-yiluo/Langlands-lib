import Langlands.Representation.RankinSelberg.AdjacentRankSpectralExpansion
import Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient

/-! The actual finite integral product identity at a common convergent parameter. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped BigOperators

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance productsFieldTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance productsFieldValuation : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance productsLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance productsFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance productsFieldTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance productsFieldMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance productsFieldBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance productsGroupMeasurableSpace (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance productsGroupBorelSpace (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance productsUnipotentMeasurableSpace (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance productsUnipotentBorelSpace (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance productsQuotientMeasurableSpace (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance productsQuotientBorelSpace (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData
local notation "qF" => F.canonicalTopologicalData.residueCardinality

/-- The literal finite sum of equal-rank and shifted matrix integrals. -/
def adjacentRankFiniteProductValue {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (f : Fin N → Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (s : ℂ) : ℂ :=
  ∑ i, equalRankIntegral ψ abv ν W (B i) φ s *
    GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)

/-- A pointwise lower determinant bound forces every smaller quotient coefficient
to vanish, independently of the second Whittaker function. -/
theorem equalRankSliceCoefficient_eq_zero_of_pointwise_bound {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (W : WhittakerFunctions ψ r) (W' : InverseWhittakerFunctions ψ r)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier)) (L : ℤ)
    (hL : ∀ g, W.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      L ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier))
    (m : ℤ) (hm : m < L) :
    equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W W' φ m = 0 := by
  rw [equalRankSliceCoefficient_def]
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro q hq
  induction q using Quotient.inductionOn with
  | h g =>
    rw [mk_mem_determinantSlice] at hq
    rw [equalRankIntegrand_zero_mk]
    by_cases hW : W.val g = 0
    · rw [hW, zero_mul, zero_mul]
    by_cases hφ : φ (lastRow g) = 0
    · rw [hφ, mul_zero]
    have hb := hL g hW hφ
    omega

/-- The square-test support bound forces all smaller group coefficients to vanish.
No global convergence is needed for this support assertion. -/
theorem adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (χ : Quasicharacter F.Carrier)
    (f : Langlands.GeneralLinear (r + 1) F.Carrier → ℂ) (L : ℤ)
    (hL : ∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
      L ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier))
    (m : ℤ) (hm : m < L) :
    adjacentRankMatrixSliceCoefficient F Φ χ f m = 0 := by
  rw [adjacentRankMatrixSliceCoefficient]
  apply integral_eq_zero_of_ae
  filter_upwards [] with h
  dsimp only [adjacentRankInnerSliceWeight]
  rw [matrixSliceTest_apply]
  by_cases hh : h ∈ generalLinearDeterminantSlice F.canonicalTopologicalData r m
  · rw [Set.indicator_of_mem hh]
    have hΦ : Φ h.val = 0 := by
      by_contra hne
      have hb := hL h hne
      change F.canonicalTopologicalData.ord
        (GeneralLinear.determinant h : F.Carrier) = m at hh
      omega
    rw [hΦ, zero_mul, zero_mul, zero_mul]
    rfl
  · rw [Set.indicator_of_notMem hh, zero_mul, zero_mul, zero_mul]
    rfl

/-- A finite coefficient convolution gives the actual integral identity whenever
all the actual integrals converge at the same supplied parameter. -/
theorem corankOneIntegral_eq_finiteProducts_of_coefficients {r N : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (W : WhittakerFunctions ψ r) (B : Fin N → InverseWhittakerFunctions ψ r)
    (U : WhittakerFunctions ψ (r + 1)) (W' : InverseWhittakerFunctions ψ r)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (χ : Quasicharacter F.Carrier)
    (f : Fin N → Langlands.GeneralLinear (r + 1) F.Carrier → ℂ)
    (Lq Lh : ℤ)
    (hLq : ∀ g, W.val g ≠ 0 → φ (lastRow g) ≠ 0 →
      Lq ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier))
    (hLh : ∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
      Lh ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier))
    (hc : ∀ m : ℤ, sliceCoefficient F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U W' 0) m =
      ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W (B i) φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k))
    (s : ℂ)
    (hU : CorankOneConverges ψ abv ν U W' s)
    (hW : ∀ i, EqualRankConverges ψ abv ν W (B i) φ s)
    (hf : ∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
      (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) :
    corankOneIntegral ψ abv ν U W' s =
      adjacentRankFiniteProductValue F ψ ν W B Φ φ χ f s := by
  classical
  have hi : ∀ i : Fin N,
      HasSum (fun m : ℤ =>
        (∑ k ∈ Finset.Icc Lq (m - Lh),
          equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W (B i) φ k *
            adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)) *
              spectralPoint qF s ^ m)
        (equalRankIntegral ψ abv ν W (B i) φ s *
          GodementJacquet.Padic.matrixIntegral F Φ (s + (r : ℂ) / 2)
            (fun h => (χ (GeneralLinear.determinant h) : ℂ) * f i h)) := by
    intro i
    exact (hasSum_intervalConvolution _ _ Lq Lh
      (equalRankSliceCoefficient_eq_zero_of_pointwise_bound F ψ ν W (B i) φ Lq hLq)
      (adjacentRankMatrixSliceCoefficient_eq_zero_of_pointwise_bound F Φ χ (f i) Lh hLh)
      _ _ _ (spectralPoint_ne_zero_of_pos
        (lt_trans Nat.zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one) s)
      (equalRankSliceExpansion F F.canonicalTopologicalData r ν ψ W (B i) φ s (hW i)).2.2
      (adjacentRankMatrixSliceExpansion F Φ χ (f i) s (hf i)).2).2
  have hsum := hasSum_sum (s := Finset.univ) (fun i _ => hi i)
  have heq : (fun m : ℤ => ∑ i : Fin N,
      (∑ k ∈ Finset.Icc Lq (m - Lh),
        equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W (B i) φ k *
          adjacentRankMatrixSliceCoefficient F Φ χ (f i) (m - k)) *
            spectralPoint qF s ^ m) =
      (fun m : ℤ => sliceCoefficient F.canonicalTopologicalData ν
        (corankOneIntegrand ψ abv U W' 0) m * spectralPoint qF s ^ m) := by
    funext m
    rw [← Finset.sum_mul, Finset.sum_comm, ← hc m]
  rw [heq] at hsum
  exact (corankOneSliceExpansion F ψ U W' ν s hU).2.unique hsum

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A realized separated model has a uniform finite product formula at every
supplied parameter where all actual integrands are integrable. -/
theorem adjacentRankModel_corankOne_finiteProducts
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ r σ)
    (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V')
    (hτ : IsAdmissible τ) (ℓ' : glFunctionals (ψ.scale (-1)) r τ)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (GeneralLinear.upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν) :
    ∃ (Lq Lh : ℤ) (N : ℕ)
      (B : Fin N → (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule),
      (∀ g, W.val.val g ≠ 0 → φ (lastRow g) ≠ 0 →
        Lq ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier)) ∧
      (∀ h : Langlands.GeneralLinear (r + 1) F.Carrier, Φ h.val ≠ 0 →
        Lh ≤ F.canonicalTopologicalData.ord (GeneralLinear.determinant h : F.Carrier)) ∧
      ∀ W' : (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule,
        ∃ f : Fin N → GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel (ψ.scale (-1)) r τ ℓ').toSubmodule)
          (glModelRepresentation (ψ.scale (-1)) r τ ℓ'),
          let Winv := InducedTailIntermediate.scaledStandardAsInverse ψ W'.val
          let Binv := fun i => InducedTailIntermediate.scaledStandardAsInverse ψ (B i).val
          ∀ s : ℂ,
            CorankOneConverges ψ abv ν U Winv s →
            (∀ i, EqualRankConverges ψ abv ν W.val (Binv i) φ s) →
            (∀ i, GodementJacquet.Padic.MatrixConverges F Φ (s + (r : ℂ) / 2)
              (fun h => (χ (GeneralLinear.determinant h) : ℂ) * (f i).val h)) →
            corankOneIntegral ψ abv ν U Winv s =
              adjacentRankFiniteProductValue F ψ ν W.val Binv Φ φ χ
                (fun i => (f i).val) s := by
  obtain ⟨Lq, Lh, N, B, hLq, hLh, hB⟩ :=
    adjacentRankModel_corankOne_finiteConvolution F ψ μ hself σ hσ ℓ χ Φ φ W U hU
      τ hτ ℓ' ν hν
  refine ⟨Lq, Lh, N, B, hLq, hLh, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, ?_⟩
  dsimp only at hf ⊢
  intro s hs ha hb
  exact corankOneIntegral_eq_finiteProducts_of_coefficients F ψ ν W.val _ U _ Φ φ χ
    (fun i => (f i).val) Lq Lh hLq hLh hf.2.2.2 s hs ha hb

end Langlands.RankinSelberg.Padic

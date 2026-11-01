import Langlands.Representation.RankinSelberg.AdjacentRankShellConvolution
import Langlands.Representation.RankinSelberg.AdjacentRankIntegralModel
import Langlands.Representation.RankinSelberg.TwistInvariance
import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws
import Langlands.HarmonicAnalysis.PartialFourierCovarianceProof
import Langlands.HarmonicAnalysis.SchwartzBruhatProduct
import Langlands.Representation.Hecke.TestFunction

/-! The actual model substitution preceding the finite convolution in JPSS 6.3. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration
open scoped BigOperators

universe uF uV uW

/-- A rectangular Schwartz test separated into its square block and last column. -/
def adjacentRankSeparatedTest {K : Type uF} [TopologicalSpace K] {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (φ : SchwartzBruhat (Fin (r + 1) → K)) :
    SchwartzBruhat (Matrix (Fin (r + 1)) (Fin (r + 2)) K) :=
  Hecke.TestFunction.pullback rectangularSplit (SchwartzBruhat.tensor Φ φ)

@[simp] theorem adjacentRankSeparatedTest_join
    {K : Type uF} [TopologicalSpace K] {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (φ : SchwartzBruhat (Fin (r + 1) → K))
    (x : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (y : Fin (r + 1) → K) :
    adjacentRankSeparatedTest Φ φ (rectangularJoin x y) = Φ x * φ y := by
  simp [adjacentRankSeparatedTest]

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance : MeasurableSpace F.Carrier := borel _
local instance : BorelSpace F.Carrier := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance (r : ℕ) : BorelSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : SecondCountableTopology
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSecondCountableTopology (r + 1)
local instance (r : ℕ) : SigmaCompactSpace
    (Langlands.GeneralLinear (r + 1) F.Carrier) :=
  F.canonicalTopologicalData.generalLinearSigmaCompactSpace (r + 1)
local instance (r : ℕ) : MeasurableSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := borel _
local instance (r : ℕ) : BorelSpace
    (GeneralLinear.upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance (r : ℕ) : MeasurableSpace
    (LeftUnipotentQuotient r F.Carrier) := borel _
local instance (r : ℕ) : BorelSpace
    (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

theorem adjacentRankInnerMultiplier_mul {r : ℕ}
    (χ : Quasicharacter F.Carrier) (s : ℂ)
    (h g : Langlands.GeneralLinear (r + 1) F.Carrier) :
    adjacentRankInnerMultiplier F χ s (h * g) =
      adjacentRankInnerMultiplier F χ s h * adjacentRankInnerMultiplier F χ s g := by
  simp only [adjacentRankInnerMultiplier, map_mul, Units.val_mul, determinantWeight_mul]
  ring

/-- The proved elementary Fourier covariance evaluates the separated test
at precisely the square block `h g` and the last row of `h⁻¹`. -/
theorem adjacentRankSeparatedTest_rho0_rankInclusion
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (g h : Langlands.GeneralLinear (r + 1) F.Carrier) :
    rectangularRho0 ψ μ (r + 1) hself (GeneralLinear.rankInclusion 1 g)
        (adjacentRankSeparatedTest Φ φ) (adjacentRankKernelMatrix h) =
      Φ (h * g).val * φ (lastRow h⁻¹) := by
  rw [(partialFourierCovariance ψ μ (r + 1) hself).1,
    rectangularTranslate_apply, adjacentRankKernelMatrix,
    rectangularJoin_mul_rankInclusion, adjacentRankSeparatedTest_join]
  have he := funext (inverseTranspose_mulVec_adjacentRankEpsilon h)
  rw [he]
  rfl

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Direct substitution of a separated pure tensor into the literal model.
No Whittaker image or spanning assertion is assumed. -/
theorem adjacentRankModelIntegral_separated_rankInclusion_raw
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (r + 1) F.Carrier) :
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) =
      (χ (GeneralLinear.determinant g) : ℂ) *
        determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
        ∫ h, Φ (h * g).val * φ (lastRow h⁻¹) * W.val.val h⁻¹ *
          adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
            ∂generalLinearHaar F.Carrier r := by
  unfold adjacentRankModelIntegral
  rw [RankinSelberg.adjacentRankModelIntegral_tmul]
  have hdet : GeneralLinear.determinant (GeneralLinear.rankInclusion 1 g) =
      GeneralLinear.determinant g :=
    Units.ext (det_rankInclusion 1 g)
  have hw : determinantWeight abv (GeneralLinear.rankInclusion 1 g)
      (((r + 1 : ℕ) : ℂ) / 2) =
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) := by
    simp only [determinantWeight, det_rankInclusion]
  rw [hdet, hw]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro h
  dsimp only
  rw [adjacentRankSeparatedTest_rho0_rankInclusion F]
  change (Φ _ * φ _ * W.val.val _ *
    (χ (GeneralLinear.determinant h) : ℂ) *
      determinantWeight abv h ((r : ℂ) / 2)) = _
  unfold adjacentRankInnerMultiplier
  ring

/-- Right substitution in the same GL Haar measure and cancellation of the
two half-weights give the kernel used in the shell convolution. -/
theorem adjacentRankModelIntegral_separated_rankInclusion_weighted
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : Langlands.GeneralLinear (r + 1) F.Carrier) (s : ℂ) :
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) *
        determinantWeight abv g (s - 1 / 2) =
      determinantWeight abv g s *
        ∫ h, Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
          adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
            ∂generalLinearHaar F.Carrier r := by
  let a := adjacentRankInnerMultiplier F (r := r) χ ((r : ℂ) / 2)
  let orig := fun h : Langlands.GeneralLinear (r + 1) F.Carrier =>
    Φ (h * g).val * φ (lastRow h⁻¹) * W.val.val h⁻¹ * a h
  let after := fun h : Langlands.GeneralLinear (r + 1) F.Carrier =>
    Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) * a h
  have he : ∀ h, after (h * g) = a g * orig h := by
    intro h
    dsimp only [after, orig, a]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul,
      adjacentRankInnerMultiplier_mul]
    ring
  have hi : (∫ h, after h ∂generalLinearHaar F.Carrier r) =
      a g * ∫ h, orig h ∂generalLinearHaar F.Carrier r := by
    rw [← integral_mul_right_eq_self after g]
    simp_rw [he]
    exact integral_const_mul _ _
  have hw : (χ (GeneralLinear.determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g s * a g := by
    dsimp only [a, adjacentRankInnerMultiplier]
    rw [mul_assoc, ← determinantWeight_exponent_add, mul_left_comm,
      ← determinantWeight_exponent_add]
    congr 2
    push_cast
    ring
  rw [adjacentRankModelIntegral_separated_rankInclusion_raw F]
  change ((χ (GeneralLinear.determinant g) : ℂ) *
    determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, orig h ∂generalLinearHaar F.Carrier r)) *
        determinantWeight abv g (s - 1 / 2) =
      determinantWeight abv g s * ∫ h, after h ∂generalLinearHaar F.Carrier r
  rw [hi]
  calc
    _ = ((χ (GeneralLinear.determinant g) : ℂ) *
        determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
        determinantWeight abv g (s - 1 / 2)) *
          (∫ h, orig h ∂generalLinearHaar F.Carrier r) := by ring
    _ = _ := by rw [hw]; ring

/-- A Whittaker function realized by this separated model has exactly the
before-shear kernel on each determinant slice. Realization is explicit data. -/
theorem adjacentRankModel_corankOneSlice_eq_before
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (W' : InverseWhittakerFunctions ψ r) (m : ℤ)
    (q : LeftUnipotentQuotient r F.Carrier) :
    (determinantSlice F.canonicalTopologicalData r m).indicator
        (corankOneIntegrand ψ abv U W' 0) q =
      ∫ h, adjacentRankBeforeShearKernel F ψ W.val W' Φ φ
        (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h)
          ∂generalLinearHaar F.Carrier r := by
  classical
  induction q using Quotient.inductionOn with
  | h g =>
    by_cases hg : F.canonicalTopologicalData.ord
        (GeneralLinear.determinant g : F.Carrier) = m
    · rw [Set.indicator_of_mem (show Quotient.mk _ g ∈
        determinantSlice F.canonicalTopologicalData r m from hg),
        corankOneIntegrand_mk, hU]
      have hw := adjacentRankModelIntegral_separated_rankInclusion_weighted
        F ψ μ hself σ ℓ χ Φ φ W g 0
      simp only [determinantWeight_zero, one_mul] at hw
      calc
        _ = (adjacentRankModelIntegral F ψ μ hself σ ℓ χ
              (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (GeneralLinear.rankInclusion 1 g) *
              determinantWeight abv g (0 - 1 / 2)) * W'.val g := by ring
        _ = (∫ h, Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
              adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h
                ∂generalLinearHaar F.Carrier r) * W'.val g := by rw [hw]
        _ = ∫ h, (Φ h.val * φ (lastRow (g * h⁻¹)) * W.val.val (g * h⁻¹) *
              adjacentRankInnerMultiplier F χ ((r : ℂ) / 2) h) * W'.val g
                ∂generalLinearHaar F.Carrier r := (integral_mul_const _ _).symm
        _ = _ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun h => by
            dsimp only
            rw [adjacentRankBeforeShearKernel_mk, ite_eq_left hg]
            ring
    · rw [Set.indicator_of_notMem (show Quotient.mk _ g ∉
        determinantSlice F.canonicalTopologicalData r m from hg)]
      simp only [adjacentRankBeforeShearKernel_mk, ite_eq_right hg, integral_zero]

set_option maxHeartbeats 1600000 in
/-- The actual corank-one coefficient of a realized separated model is a finite
convolution, with genuine convergence on every determinant slice. -/
theorem adjacentRankModel_corankOne_finiteConvolution
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
          SliceIntegrable F.canonicalTopologicalData ν (corankOneIntegrand ψ abv U Winv 0) ∧
            (∀ k i, Integrable ((determinantSlice F.canonicalTopologicalData r k).indicator
              (equalRankIntegrand ψ abv W.val (Binv i) φ 0)) ν) ∧
            (∀ j i, Integrable (fun h => adjacentRankInnerSliceWeight F Φ χ j
              ((r : ℂ) / 2) h * (f i).val h) (generalLinearHaar F.Carrier r)) ∧
            ∀ m : ℤ,
              sliceCoefficient F.canonicalTopologicalData ν
                (corankOneIntegrand ψ abv U Winv 0) m =
                ∑ k ∈ Finset.Icc Lq (m - Lh), ∑ i,
                  equalRankSliceCoefficient F.canonicalTopologicalData ν ψ W.val
                    (Binv i) φ k *
                    ∫ h, adjacentRankInnerSliceWeight F Φ χ (m - k)
                      ((r : ℂ) / 2) h * (f i).val h
                        ∂generalLinearHaar F.Carrier r := by
  classical
  obtain ⟨Lq, Lh, N, B, hLq, hLh, hB⟩ :=
    adjacentRankShell_finiteConvolution F ψ σ hσ ℓ W τ hτ ℓ' Φ φ χ ν hν
  refine ⟨Lq, Lh, N, B, hLq, hLh, fun W' => ?_⟩
  obtain ⟨f, hf⟩ := hB W'
  refine ⟨f, ?_⟩
  dsimp only
  let Winv := InducedTailIntermediate.scaledStandardAsInverse ψ W'.val
  let η := generalLinearHaar F.Carrier r
  have he : ∀ m, (determinantSlice F.canonicalTopologicalData r m).indicator
      (corankOneIntegrand ψ abv U Winv 0) =
      fun q => ∫ h, adjacentRankBeforeShearKernel F ψ W.val Winv Φ φ
        (adjacentRankInnerMultiplier F χ ((r : ℂ) / 2)) m (q, h) ∂η := by
    intro m
    funext q
    exact adjacentRankModel_corankOneSlice_eq_before F ψ μ hself σ ℓ χ Φ φ W U hU Winv m q
  have hslice : SliceIntegrable F.canonicalTopologicalData ν
      (corankOneIntegrand ψ abv U Winv 0) := by
    intro m
    have hb := (hf m ((r : ℂ) / 2)).1
    have ho := hb.integral_prod_left
    have hind : Integrable ((determinantSlice F.canonicalTopologicalData r m).indicator
        (corankOneIntegrand ψ abv U Winv 0)) ν := by
      rw [he m]
      exact ho
    exact (integrable_indicator_iff
      (measurableSet_determinantSlice F.canonicalTopologicalData r m)).mp hind
  refine ⟨hslice, (hf 0 ((r : ℂ) / 2)).2.2.1,
    (hf 0 ((r : ℂ) / 2)).2.2.2.1, fun m => ?_⟩
  rw [sliceCoefficient_eq_integral_indicator, he m]
  exact (hf m ((r : ℂ) / 2)).2.2.2.2.2

end Padic
end Langlands.RankinSelberg

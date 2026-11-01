import Langlands.Representation.RankinSelberg.AdjacentRankDualRestriction
import Langlands.Representation.RankinSelberg.AdjacentRankMatchedShellConvolution

/-! The literal model-star restriction and the matched determinant coefficients. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker QuotientIntegration GeneralLinear
open scoped BigOperators

universe uF uV uW

/-- Reflection of the actual square Schwartz test. -/
def adjacentRankReflectedTest {K : Type uF} [Field K] [TopologicalSpace K]
    [IsTopologicalRing K] {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r K) :
    GodementJacquet.MatrixTestFunction r K :=
  Hecke.TestFunction.pullback (Homeomorph.neg _) Φ

@[simp] theorem adjacentRankReflectedTest_apply
    {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    adjacentRankReflectedTest Φ X = Φ (-X) := rfl

theorem adjacentRankReflectedTest_mul
    {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K] {r : ℕ}
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (h g : GeneralLinear (r + 1) K) :
    adjacentRankReflectedTest Φ (h * g).val =
      Φ (h * (scalar (n := r + 1) (-1 : Kˣ) * g)).val := by
  change Φ (-(h.val * g.val)) =
    Φ (h.val * ((scalar (n := r + 1) (-1 : Kˣ)).val * g.val))
  apply congrArg (fun X : Matrix (Fin (r + 1)) (Fin (r + 1)) K => Φ X)
  ext i j
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.mul_apply, Matrix.diagonal_apply, Finset.sum_neg_distrib]

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualModelFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualModelValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualModelLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualModelFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance dualModelFieldTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance dualModelFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualModelFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualModelGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualModelGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualModelQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance dualModelQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The literal character scalar from the model-star sign matrix. -/
def adjacentRankModelStarScalar (χ : Quasicharacter F.Carrier) (r : ℕ) : ℂ :=
  χ⁻¹ (determinant (scalar (n := r + 1) (-1 : F.Carrierˣ)))

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1600000 in
/-- Right translation of the literal fixed-character model-star restriction
gives exactly the reflected before-shell integrand and its sign scalar. -/
theorem adjacentRankModelStar_separated_rankInclusion_weighted
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : GeneralLinear (r + 1) F.Carrier) (s : ℂ) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    adjacentRankModelIntegral F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
        (weylLong (r + 2) F.Carrier *
          inverseTranspose (r + 2) F.Carrier (rankInclusion 1 g)) *
        determinantWeight abv g (s - 1 / 2) =
      adjacentRankModelStarScalar F χ r * determinantWeight abv g s *
        ∫ h, ΦD h.val * φHat (lastRow (g * h⁻¹)) * WD.val.val (g * h⁻¹) *
          adjacentRankInnerMultiplier F χ⁻¹ ((r : ℂ) / 2) h
            ∂generalLinearHaar F.Carrier r := by
  dsimp only
  let ΦHat := rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ
  let ΦD := adjacentRankReflectedTest ΦHat
  let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
    (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
  let c := scalar (n := r + 1) (-1 : F.Carrierˣ)
  let a := adjacentRankInnerMultiplier F (r := r) χ⁻¹ ((r : ℂ) / 2)
  let orig := fun h : GeneralLinear (r + 1) F.Carrier =>
    ΦD (h * g).val * φHat (lastRow h⁻¹) * WD.val.val h⁻¹ * a h
  let after := fun h : GeneralLinear (r + 1) F.Carrier =>
    ΦD h.val * φHat (lastRow (g * h⁻¹)) * WD.val.val (g * h⁻¹) * a h
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
  have hraw := (adjacentRankModelStar_separated_rankInclusion
    F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W g).2.2
  have hk : adjacentRankZeta F.Carrier r * rankInclusion 1 g =
      rankInclusion 1 (c * g) := by
    rw [adjacentRankZeta_eq_rankInclusion, map_mul]
  have hdet : determinant (adjacentRankZeta F.Carrier r * rankInclusion 1 g) =
      determinant (c * g) := by
    rw [hk]
    exact Units.ext (det_rankInclusion 1 (c * g))
  have hwc (t : ℂ) : determinantWeight abv c t = 1 := by
    simp [determinantWeight, c, scalar]
  have hwk (t : ℂ) :
      determinantWeight abv (adjacentRankZeta F.Carrier r * rankInclusion 1 g) t =
        determinantWeight abv g t := by
    rw [hk]
    change (abv (Matrix.det (rankInclusion 1 (c * g)).val) : ℂ) ^ t = _
    rw [det_rankInclusion]
    change determinantWeight abv (c * g) t = _
    rw [determinantWeight_mul, hwc, one_mul]
  have hJ :
      (fun h : GeneralLinear (r + 1) F.Carrier =>
        ΦHat (h * (c * g)).val * φHat (lastRow h⁻¹) *
          W.val.val (weylLong (r + 1) F.Carrier *
            inverseTranspose (r + 1) F.Carrier h⁻¹) *
          (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)) =
        orig := by
    funext h
    rw [← adjacentRankReflectedTest_mul]
    change ΦD (h * g).val * φHat (lastRow h⁻¹) * WD.val.val h⁻¹ *
      (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2) = _
    dsimp only [orig, a, adjacentRankInnerMultiplier]
    ring
  change _ = (χ⁻¹ (determinant
      (adjacentRankZeta F.Carrier r * rankInclusion 1 g)) : ℂ) *
    determinantWeight abv (adjacentRankZeta F.Carrier r * rankInclusion 1 g)
      (((r + 1 : ℕ) : ℂ) / 2) *
    ∫ h, ΦHat (h * (c * g)).val * φHat (lastRow h⁻¹) *
      W.val.val (weylLong (r + 1) F.Carrier *
        inverseTranspose (r + 1) F.Carrier h⁻¹) *
      (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)
        ∂generalLinearHaar F.Carrier r at hraw
  rw [hJ, hdet, hwk, map_mul, map_mul, Units.val_mul] at hraw
  have hw : (χ⁻¹ (determinant g) : ℂ) *
      determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      determinantWeight abv g (s - 1 / 2) =
        determinantWeight abv g s * a g := by
    dsimp only [a, adjacentRankInnerMultiplier]
    rw [mul_assoc, ← determinantWeight_exponent_add, mul_left_comm,
      ← determinantWeight_exponent_add]
    congr 2
    push_cast
    ring
  rw [hraw]
  change (((χ⁻¹ (determinant c) : ℂ) * (χ⁻¹ (determinant g) : ℂ) *
    determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
      (∫ h, orig h ∂generalLinearHaar F.Carrier r)) *
        determinantWeight abv g (s - 1 / 2)) =
    adjacentRankModelStarScalar F χ r * determinantWeight abv g s *
      ∫ h, after h ∂generalLinearHaar F.Carrier r
  rw [hi]
  calc
    _ = (χ⁻¹ (determinant c) : ℂ) *
        ((χ⁻¹ (determinant g) : ℂ) *
          determinantWeight abv g (((r + 1 : ℕ) : ℂ) / 2) *
          determinantWeight abv g (s - 1 / 2)) *
        (∫ h, orig h ∂generalLinearHaar F.Carrier r) := by ring
    _ = _ := by
      rw [hw]
      dsimp only [adjacentRankModelStarScalar, c]
      ring

set_option maxHeartbeats 1600000 in
/-- The actual dual corank-one determinant indicator is the matched
before-shell integral times the explicit model-star scalar. -/
theorem adjacentRankModelStar_corankOneSlice_eq_before
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (U : WhittakerFunctions ψ (r + 1))
    (hU : ∀ g, U.val g = adjacentRankModelIntegral F ψ μ hself σ ℓ χ
      (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) g)
    (W'D : InverseWhittakerFunctions (ψ.scale (-1)) r) (m : ℤ)
    (q : LeftUnipotentQuotient r F.Carrier) :
    let ΦD := adjacentRankReflectedTest
      (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ)
    let WD := inverseCoefficientAsScaledStandard F ψ (inverseTransposePullback σ)
      (dualFunctional ψ σ ℓ) (dualModelLinearMap ψ σ ℓ W)
    let UD := InducedTailIntermediate.inverseAsScaledStandard ψ
      (dualFunctionEquiv ψ (r + 1) U)
    (determinantSlice F.canonicalTopologicalData r m).indicator
        (corankOneIntegrand (ψ.scale (-1)) abv UD W'D 0) q =
      adjacentRankModelStarScalar F χ r *
        ∫ h, adjacentRankBeforeShearKernel F (ψ.scale (-1)) WD.val W'D ΦD φHat
          (adjacentRankInnerMultiplier F χ⁻¹ ((r : ℂ) / 2)) m (q, h)
            ∂generalLinearHaar F.Carrier r := by
  classical
  dsimp only
  induction q using Quotient.inductionOn with
  | h g =>
    by_cases hg : F.canonicalTopologicalData.ord (determinant g : F.Carrier) = m
    · rw [Set.indicator_of_mem (show Quotient.mk _ g ∈
        determinantSlice F.canonicalTopologicalData r m from hg),
        corankOneIntegrand_mk]
      change U.val (weylLong (r + 2) F.Carrier *
        inverseTranspose (r + 2) F.Carrier (rankInclusion 1 g)) *
        W'D.val g * determinantWeight abv g (0 - 1 / 2) = _
      rw [hU]
      have hw := adjacentRankModelStar_separated_rankInclusion_weighted
        F ψ μ hself σ hσ ℓ χ Φ φ φHat hφ W g 0
      dsimp only at hw
      simp only [determinantWeight_zero, mul_one] at hw
      calc
        _ = (adjacentRankModelIntegral F ψ μ hself σ ℓ χ
              (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
              (weylLong (r + 2) F.Carrier *
                inverseTranspose (r + 2) F.Carrier (rankInclusion 1 g)) *
              determinantWeight abv g (0 - 1 / 2)) * W'D.val g := by ring
        _ = _ := by
          rw [hw]
          rw [mul_assoc, ← integral_mul_const]
          congr 1
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun h => by
            dsimp only
            rw [adjacentRankBeforeShearKernel_mk, ite_eq_left hg]
            ring
    · rw [Set.indicator_of_notMem (show Quotient.mk _ g ∉
        determinantSlice F.canonicalTopologicalData r m from hg)]
      simp only [adjacentRankBeforeShearKernel_mk, ite_eq_right hg,
        integral_zero, mul_zero]

end Padic
end Langlands.RankinSelberg

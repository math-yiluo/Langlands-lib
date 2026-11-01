import Langlands.Representation.RankinSelberg.AdjacentRankModelZetaCoefficient
import Langlands.Representation.RankinSelberg.AdjacentRankModelStarProof
import Langlands.HarmonicAnalysis.RowFourierCompatibilityProof
import Mathlib.MeasureTheory.Integral.Prod

/-! The separated Fourier test and the actual model-star restriction. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear
open scoped BigOperators

universe uF uV

section MeasureSplit

variable {K : Type uF} [MeasurableSpace K] (n : ℕ)

/-- The measurable square-block/last-column split, with its inverse given by
the actual rectangular join. -/
def adjacentRankFourierSplit :
    Matrix (Fin n) (Fin (n + 1)) K ≃ᵐ
      Matrix (Fin n) (Fin n) K × (Fin n → K) where
  toFun m := (rectangularFirstColumns m, rectangularLastColumn m)
  invFun z := rectangularJoin z.1 z.2
  left_inv := rectangularJoin_split
  right_inv z := by
    simp only [rectangularFirstColumns_join, rectangularLastColumn_join]
  measurable_toFun := (measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j =>
    (measurable_pi_apply j.castSucc).comp (measurable_pi_apply i)).prodMk
      (measurable_pi_iff.2 fun i =>
        (measurable_pi_apply (Fin.last n)).comp (measurable_pi_apply i))
  measurable_invFun := measurable_pi_iff.2 fun i => measurable_pi_iff.2 fun j => by
    change Measurable (fun z : Matrix (Fin n) (Fin n) K × (Fin n → K) =>
      rectangularJoin z.1 z.2 i j)
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp only [rectangularJoin_last]
      fun_prop
    · simp only [rectangularJoin_castSucc]
      fun_prop

variable [AddGroup K] [TopologicalSpace K]

/-- Splitting off the last column preserves the supplied scalar product
normalization exactly. -/
theorem adjacentRankFourierSplit_measurePreserving (μ : AdditiveHaarMeasure K)
    [SigmaFinite μ.measure] :
    MeasurePreserving (adjacentRankFourierSplit (K := K) n)
      (rectangularMeasure μ n (n + 1)) ((rectangularMeasure μ n n).prod (rowMeasure μ n)) := by
  have hrow : MeasurePreserving
      (fun x : Fin (n + 1) → K => ((fun j : Fin n => x j.castSucc), x (Fin.last n)))
      (rowMeasure μ (n + 1)) ((rowMeasure μ n).prod μ.measure) := by
    convert (Measure.measurePreserving_swap.comp
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => μ.measure)
        (Fin.last n))) using 1
    · funext x
      simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
      rfl
    · rfl
    · rfl
  have hpi := measurePreserving_pi
    (fun _ : Fin n => rowMeasure μ (n + 1))
    (fun _ : Fin n => (rowMeasure μ n).prod μ.measure) (fun _ => hrow)
  exact (measurePreserving_arrowProdEquivProdArrow (Fin n → K) K (Fin n)
    (fun _ => rowMeasure μ n) (fun _ => μ.measure)).comp hpi

end MeasureSplit

section Fourier

variable {K : Type uF} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K)
  (hself : IsSelfDual ψ μ) {r : ℕ}

omit [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]
  [BorelSpace K] [LocallyCompactSpace K] [T2Space K]
  [TotallyDisconnectedSpace K] in
theorem adjacentRank_rectangularPairing_join
    (A X : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (b y : Fin (r + 1) → K) :
    rectangularPairing (rectangularJoin A b) (rectangularJoin X y) =
      rectangularPairing A X + rowPairing b y := by
  simp only [rectangularPairing, rowPairing, Fin.sum_univ_castSucc,
    rectangularJoin_castSucc, rectangularJoin_last, Finset.sum_add_distrib]

/-- The actual full plus Fourier transform factors into its square and row
transforms on a separated Schwartz test, with no measure scalar. -/
theorem adjacentRankSeparatedTest_fourier
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → K))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (y : Fin (r + 1) → K) :
    rectangularFourierEquiv ψ μ (r + 1) (r + 2) hself
        (adjacentRankSeparatedTest Φ φ) (rectangularJoin X y) =
      rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ X * φHat y := by
  let : SigmaFinite μ.measure := selfDualSigmaFinite K ψ μ hself
  rw [rectangularFourierEquiv_apply, rectangularFourierEquiv_apply, hφ y]
  let F : Matrix (Fin (r + 1)) (Fin (r + 2)) K → ℂ := fun m =>
    adjacentRankSeparatedTest Φ φ m * ψ.complex (rectangularPairing m (rectangularJoin X y))
  have hsplit := ((adjacentRankFourierSplit_measurePreserving (r + 1) μ).symm).integral_comp' F
  change (∫ m, F m ∂rectangularMeasure μ (r + 1) (r + 2)) = _
  rw [← hsplit]
  have he : (fun z : Matrix (Fin (r + 1)) (Fin (r + 1)) K × (Fin (r + 1) → K) =>
      F ((adjacentRankFourierSplit (K := K) (r + 1)).symm z)) =
      (fun z => (Φ z.1 * ψ.complex (rectangularPairing z.1 X)) *
        (ψ.complex (rowPairing z.2 y) * φ z.2)) := by
    funext z
    change adjacentRankSeparatedTest Φ φ (rectangularJoin z.1 z.2) *
      ψ.complex (rectangularPairing (rectangularJoin z.1 z.2) (rectangularJoin X y)) = _
    rw [adjacentRankSeparatedTest_join Φ φ z.1 z.2,
      adjacentRank_rectangularPairing_join z.1 X z.2 y,
      AddChar.map_add_eq_mul]
    ring
  rw [he]
  exact integral_prod_mul
    (fun A => Φ A * ψ.complex (rectangularPairing A X))
    (fun b => ψ.complex (rowPairing b y) * φ b)

/-- The separated Fourier identity is an equality of whole Schwartz tests. -/
theorem adjacentRankSeparatedTest_fourier_eq
    (Φ : GodementJacquet.MatrixTestFunction r K)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → K))
    (hφ : IsRowFourierPair ψ μ φ φHat) :
    rectangularFourierEquiv ψ μ (r + 1) (r + 2) hself
        (adjacentRankSeparatedTest Φ φ) =
      adjacentRankSeparatedTest
        (rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ) φHat := by
  ext m
  obtain ⟨X, y, rfl⟩ : ∃ X y, rectangularJoin X y = m :=
    ⟨_, _, rectangularJoin_split m⟩
  exact (adjacentRankSeparatedTest_fourier ψ μ hself Φ φ φHat hφ X y).trans
    (adjacentRankSeparatedTest_join _ φHat X y).symm

end Fourier

section SignMatrix

variable {K : Type uF} [Field K] (r : ℕ)

/-- The model-star sign matrix is the standard rank inclusion of the negative
scalar matrix in the smaller group. -/
theorem adjacentRankZeta_eq_rankInclusion :
    adjacentRankZeta K r = rankInclusion 1 (scalar (n := r + 1) (-1 : Kˣ)) := by
  apply Units.ext
  ext i j
  change (adjacentRankZeta K r).val i j =
    (blockSum (scalar (n := r + 1) (-1 : Kˣ), (1 : GeneralLinear 1 K))).val i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;>
    refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [show (blockSum (scalar (n := r + 1) (-1 : Kˣ), (1 : GeneralLinear 1 K))).val
        (Fin.last (r + 1)) (Fin.last (r + 1)) = 1 by
      exact (blockSum_apply_right (scalar (n := r + 1) (-1 : Kˣ))
        (1 : GeneralLinear 1 K) (0 : Fin 1) (0 : Fin 1)).trans (by rfl)]
    exact adjacentRankZeta_diagonal_last K r
  · rw [show (blockSum (scalar (n := r + 1) (-1 : Kˣ), (1 : GeneralLinear 1 K))).val
        (Fin.last (r + 1)) j.castSucc = 0 from
      blockSum_apply_right_left _ _ (0 : Fin 1) j]
    exact adjacentRankZeta_offDiagonal K r _ _ (Fin.castSucc_ne_last j).symm
  · rw [show (blockSum (scalar (n := r + 1) (-1 : Kˣ), (1 : GeneralLinear 1 K))).val
        i.castSucc (Fin.last (r + 1)) = 0 from
      blockSum_apply_left_right _ _ i (0 : Fin 1)]
    exact adjacentRankZeta_offDiagonal K r _ _ (Fin.castSucc_ne_last i)
  · rw [show (blockSum (scalar (n := r + 1) (-1 : Kˣ), (1 : GeneralLinear 1 K))).val
        i.castSucc j.castSucc = (scalar (n := r + 1) (-1 : Kˣ)).val i j from
      blockSum_apply_left _ _ i j]
    simp [adjacentRankZeta_entry, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply]

end SignMatrix

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualRestrictionFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualRestrictionValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualRestrictionLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualRestrictionFieldT2 : T2Space F.Carrier :=
  F.canonicalTopologicalData.fieldT2
local instance dualRestrictionFieldTotallyDisconnected :
    TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance dualRestrictionFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualRestrictionFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualRestrictionGroupMeasurable (r : ℕ) :
    MeasurableSpace (GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualRestrictionGroupBorel (r : ℕ) :
    BorelSpace (GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

set_option maxHeartbeats 1600000 in
/-- The published fixed-character model-star identity on the actual diagonal
subgroup, for a separated tensor. The full Fourier transform factors exactly,
and the negative scalar remains in the square-test argument. -/
theorem adjacentRankModelStar_separated_rankInclusion
    (ψ : UnitaryAdditiveCharacter F.Carrier) (μ : AdditiveHaarMeasure F.Carrier)
    (hself : IsSelfDual ψ μ) {r : ℕ}
    (σ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ)
    (ℓ : glFunctionals ψ r σ) (χ : Quasicharacter F.Carrier)
    (Φ : GodementJacquet.MatrixTestFunction r F.Carrier)
    (φ φHat : SchwartzBruhat (Fin (r + 1) → F.Carrier))
    (hφ : IsRowFourierPair ψ μ φ φHat)
    (W : (glCoefficientModel ψ r σ ℓ).toSubmodule)
    (g : GeneralLinear (r + 1) F.Carrier) :
    let ΦHat := rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ
    let k := adjacentRankZeta F.Carrier r * rankInclusion 1 g
    let J : GeneralLinear (r + 1) F.Carrier → ℂ := fun h =>
      ΦHat (h * (scalar (n := r + 1) (-1 : F.Carrierˣ) * g)).val *
        φHat (lastRow h⁻¹) *
        W.val.val (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
        (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)
    AdjacentRankModelConverges F ψ μ hself σ ℓ χ
        (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
        (weylLong (r + 2) F.Carrier * inverseTranspose (r + 2) F.Carrier (rankInclusion 1 g)) ∧
      Integrable J (generalLinearHaar F.Carrier r) ∧
      adjacentRankModelIntegral F ψ μ hself σ ℓ χ
          (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)
          (weylLong (r + 2) F.Carrier *
            inverseTranspose (r + 2) F.Carrier (rankInclusion 1 g)) =
        (χ⁻¹ (determinant k) : ℂ) *
          determinantWeight abv k (((r + 1 : ℕ) : ℂ) / 2) *
          ∫ h, J h ∂generalLinearHaar F.Carrier r := by
  have hs := adjacentRankModelStar p F ψ μ hself r V σ hσ ℓ χ
    (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W) (rankInclusion 1 g)
  have hk : adjacentRankZeta F.Carrier r * rankInclusion 1 g =
      rankInclusion 1 (scalar (n := r + 1) (-1 : F.Carrierˣ) * g) := by
    rw [adjacentRankZeta_eq_rankInclusion, map_mul]
  have htest := adjacentRankSeparatedTest_fourier_eq ψ μ hself Φ φ φHat hφ
  have he :
      (fun h : GeneralLinear (r + 1) F.Carrier =>
        adjacentRankTestEvaluation ψ σ ℓ
          (adjacentRankRho0 ψ μ hself σ ℓ
            (adjacentRankZeta F.Carrier r * rankInclusion 1 g)
            (TensorProduct.map
              (rectangularFourierEquiv ψ μ (r + 1) (r + 2) hself).toLinearMap
              LinearMap.id (adjacentRankSeparatedTest Φ φ ⊗ₜ[ℂ] W)))
          (adjacentRankKernelMatrix h)
          (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
          (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)) =
      (fun h => rectangularFourierEquiv ψ μ (r + 1) (r + 1) hself Φ
          (h * (scalar (n := r + 1) (-1 : F.Carrierˣ) * g)).val *
        φHat (lastRow h⁻¹) *
        W.val.val (weylLong (r + 1) F.Carrier * inverseTranspose (r + 1) F.Carrier h⁻¹) *
        (χ⁻¹ (determinant h) : ℂ) * determinantWeight abv h ((r : ℂ) / 2)) := by
    funext h
    rw [hk, TensorProduct.map_tmul, LinearMap.id_apply]
    change adjacentRankTestEvaluation ψ σ ℓ
      (adjacentRankRho0 ψ μ hself σ ℓ
        (rankInclusion 1 (scalar (n := r + 1) (-1 : F.Carrierˣ) * g))
        (rectangularFourierEquiv ψ μ (r + 1) (r + 2) hself
          (adjacentRankSeparatedTest Φ φ) ⊗ₜ[ℂ] W)) _ _ * _ * _ = _
    rw [htest, adjacentRankRho0_tmul, adjacentRankTestEvaluation_tmul,
      adjacentRankSeparatedTest_rho0_rankInclusion F]
    rfl
  dsimp only at hs ⊢
  rw [he] at hs
  exact hs

end Padic

end Langlands.RankinSelberg

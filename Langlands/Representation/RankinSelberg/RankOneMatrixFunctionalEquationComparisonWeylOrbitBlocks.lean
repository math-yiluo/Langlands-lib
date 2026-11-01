import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylBlockFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonFourierInvariance

/-! The scalar Fourier orbit and complementary block orbit for the same matrix test. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg

open MeasureTheory MeasureTheory.Measure GeneralLinear HarmonicAnalysis Whittaker
open UnequalRankComplementaryConjugationProof

universe uK

variable {K : Type uK} [Field K]

/-- Inverse transpose fixes the actual leading sign diagonal. -/
@[simp] theorem inverseTranspose_rankOneWeylLeadingSign (n : ℕ) :
    inverseTranspose (n + 1) K (rankOneWeylLeadingSign n) =
      rankOneWeylLeadingSign n := by
  apply Units.ext
  simp only [inverseTranspose_coe, rankOneWeylLeadingSign_inv,
    rankOneWeylLeadingSign_val, Matrix.diagonal_transpose]

/-- The signed complementary Weyl representative is orthogonal. -/
@[simp] theorem inverseTranspose_rankOneSignedBlockWeyl (n : ℕ) (hn : 0 < n) :
    inverseTranspose (n + 1) K (rankOneSignedBlockWeyl n hn) =
      rankOneSignedBlockWeyl n hn := by
  simp only [rankOneSignedBlockWeyl, map_mul,
    inverseTranspose_rankOneWeylAlternating, inverseTranspose_rankOneWeylLeadingSign,
    blockWeylAt_eq, inverseTranspose_permutation]

section Kernels

variable [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]

/-- The dual orbit kernel at a scalar diagonal and the fixed right translate. -/
def signedWeylOrbitFourierKernel (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (z : upperUnipotent (m + 2) K × K) : ℂ :=
  (inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
    rectangularFourierIntegral ψ ν Φ
      ((inverseTranspose (m + 2) K z.1.val).val *
        (rankOneSignedWeyl (m + 1))⁻¹.val *
        Matrix.diagonal (Fin.cons z.2 (fun _ => 1)) * h.val)

/-- The original orbit kernel at the complementary affine block and the
actual signed block Weyl translate. -/
def signedBlockOrbitKernel (ψ : UnitaryAdditiveCharacter K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (z : upperUnipotent (m + 2) K × (K × Matrix (Fin m) (Fin 1) K)) : ℂ :=
  (inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
    Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
      (rankOneSignedBlockWeyl (m + 1) (by omega)).val *
      (inverseTranspose (m + 2) K h).val)

omit [IsTopologicalRing K] [MeasurableSpace K] in
/-- At an invertible scalar this is the literal unequal-rank block matrix,
followed by the signed complementary Weyl element and inverse transpose of h. -/
theorem signedBlockOrbitKernel_at_generalLinear
    (ψ : UnitaryAdditiveCharacter K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (u : upperUnipotent (m + 2) K) (g : Langlands.GeneralLinear 1 K)
    (X : Matrix (Fin m) (Fin 1) K) :
    signedBlockOrbitKernel ψ m h Φ (u, (g 0 0, X)) =
      (inverseStandardCharacter ψ (m + 1) u : ℂ) *
        Φ (u.val * AdjacentBlockReduction.blockMatrixAt m 0 (by omega) g X *
          rankOneSignedBlockWeyl (m + 1) (by omega) *
          inverseTranspose (m + 2) K h).val := by
  simp only [signedBlockOrbitKernel, firstColumnMatrix_eq_blockMatrixAt,
    Units.val_mul]

end Kernels

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)

local instance orbitBlocksTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance orbitBlocksValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance orbitBlocksLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance orbitBlocksT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance orbitBlocksSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance orbitBlocksSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance orbitBlocksMeasurable : MeasurableSpace F.Carrier := borel _
local instance orbitBlocksBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance orbitBlocksNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance orbitBlocksNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance orbitBlocksNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).isClosedEmbedding.locallyCompactSpace
local instance orbitBlocksNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).secondCountableTopology
local instance orbitBlocksTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

/-- The signed complementary Weyl matrix has normalized determinant norm one. -/
theorem determinantNorm_rankOneSignedBlockWeyl (n : ℕ) (hn : 0 < n) :
    F.canonicalTopologicalData.determinantNorm (n + 1)
      (rankOneSignedBlockWeyl n hn) = 1 := by
  have hA : F.canonicalTopologicalData.determinantNorm (n + 1)
      (rankOneWeylAlternating n) = 1 := by
    apply F.canonicalTopologicalData.determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylAlternating_mul_self]
  have hE : F.canonicalTopologicalData.determinantNorm (n + 1)
      (rankOneWeylLeadingSign n) = 1 := by
    apply F.canonicalTopologicalData.determinantNorm_eq_one_of_pow_eq_one _
      (by decide : 2 ≠ 0)
    rw [pow_two, rankOneWeylLeadingSign_mul_self]
  simp only [rankOneSignedBlockWeyl, map_mul, hA, hE, blockWeylAt_eq,
    F.canonicalTopologicalData.determinantNorm_permutation, one_mul]

private theorem scalarSign_preserving (ν : AdditiveHaarMeasure F.Carrier) (d : ℕ) :
    MeasurePreserving (fun a : F.Carrier => (-1 : F.Carrier) ^ d * a)
      ν.measure ν.measure := by
  rcases neg_one_pow_eq_or F.Carrier d with hd | hd
  · convert! MeasurePreserving.id ν.measure using 1
    funext a
    simp [hd]
  · simpa only [hd, neg_one_mul] using measurePreserving_neg ν.measure

private def scalarSignEquiv (d : ℕ) : F.Carrier ≃ᵐ F.Carrier where
  toFun a := (-1 : F.Carrier) ^ d * a
  invFun a := (-1 : F.Carrier) ^ d * a
  left_inv a := by
    change (-1 : F.Carrier) ^ d * ((-1 : F.Carrier) ^ d * a) = a
    rw [← mul_assoc, ← mul_pow]
    simp
  right_inv a := by
    change (-1 : F.Carrier) ^ d * ((-1 : F.Carrier) ^ d * a) = a
    rw [← mul_assoc, ← mul_pow]
    simp
  measurable_toFun := measurable_const.mul measurable_id
  measurable_invFun := measurable_const.mul measurable_id

set_option maxHeartbeats 800000 in
/-- For the same test and norm-one h, the true scalar Fourier orbit and
complementary block orbit are jointly integrable and have equal integrals.
The scalar sign substitution preserves the supplied additive Haar exactly. -/
theorem signedWeylOrbit_blockOrbit_fourier_duality
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hh : F.canonicalTopologicalData.determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (signedWeylOrbitFourierKernel ψ ν m h Φ)
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure) ∧
    Integrable (signedBlockOrbitKernel ψ m h Φ)
      ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylOrbitFourierKernel ψ ν m h Φ z
      ∂(unipotentHaar F.Carrier (m + 1)).prod ν.measure) =
    ∫ z, signedBlockOrbitKernel ψ m h Φ z
      ∂(unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)) := by
  let b : Langlands.GeneralLinear (m + 2) F.Carrier :=
    rankOneSignedBlockWeyl (m + 1) (by omega)
  have hbh : F.canonicalTopologicalData.determinantNorm (m + 2) (b * h) = 1 := by
    rw [map_mul, determinantNorm_rankOneSignedBlockWeyl, hh, one_mul]
  obtain ⟨hl, hr, he⟩ := signedWeyl_affineBlock_fourier_duality F ψ ν hsd m
    (b * h) hbh Φ
  let e := (MeasurableEquiv.refl (upperUnipotent (m + 2) F.Carrier)).prodCongr
    (scalarSignEquiv F (m + 2))
  have hp : MeasurePreserving e
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure)
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure) :=
    (MeasurePreserving.id _).prod (scalarSign_preserving F ν (m + 2))
  have hleft (z : upperUnipotent (m + 2) F.Carrier × F.Carrier) :
      signedWeylScalarFourierKernel ψ ν m (b * h) Φ z =
        signedWeylOrbitFourierKernel ψ ν m h Φ (e z) := by
    change signedWeylScalarFourierKernel ψ ν m (b * h) Φ z =
      signedWeylOrbitFourierKernel ψ ν m h Φ
        (z.1, (-1 : F.Carrier) ^ (m + 2) * z.2)
    have hc : b⁻¹.val * (b * h).val = h.val := by
      change (b⁻¹ * (b * h)).val = h.val
      rw [inv_mul_cancel_left]
    simp only [signedWeylScalarFourierKernel, signedWeylOrbitFourierKernel,
      inverseTranspose_coe, Subgroup.coe_inv, Matrix.mul_assoc]
    change _ * rectangularFourierIntegral ψ ν Φ
      (_ * (_ * (_ * (b⁻¹.val * (b * h).val)))) = _
    rw [hc]
  have hright (z : upperUnipotent (m + 2) F.Carrier ×
      (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier)) :
      affineBlockFourierKernel ψ m (b * h) Φ z =
        signedBlockOrbitKernel ψ m h Φ z := by
    simp only [affineBlockFourierKernel, signedBlockOrbitKernel, map_mul,
      b, inverseTranspose_rankOneSignedBlockWeyl, Units.val_mul, Matrix.mul_assoc]
  have hl' : Integrable ((signedWeylOrbitFourierKernel ψ ν m h Φ) ∘ e)
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure) :=
    hl.congr (Filter.Eventually.of_forall hleft)
  refine ⟨(hp.integrable_comp_emb e.measurableEmbedding).mp hl',
    hr.congr (Filter.Eventually.of_forall hright), ?_⟩
  calc
    _ = ∫ z, signedWeylScalarFourierKernel ψ ν m (b * h) Φ z
        ∂(unipotentHaar F.Carrier (m + 1)).prod ν.measure := by
      rw [← hp.integral_comp e.measurableEmbedding]
      exact integral_congr_ae (Filter.Eventually.of_forall fun z => (hleft z).symm)
    _ = _ := he
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall hright)

/-- Fubini puts the scalar outside the actual Fourier orbit and the
scalar/block pair outside the original orbit, with genuine convergence. -/
theorem signedWeylOrbit_blockOrbit_fourier_duality_averaged
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hh : F.canonicalTopologicalData.determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (fun a : F.Carrier =>
      ∫ u, signedWeylOrbitFourierKernel ψ ν m h Φ (u, a)
        ∂unipotentHaar F.Carrier (m + 1)) ν.measure ∧
    Integrable (fun z : F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier =>
      ∫ u, signedBlockOrbitKernel ψ m h Φ (u, z)
        ∂unipotentHaar F.Carrier (m + 1))
      (ν.measure.prod (rectangularMeasure ν m 1)) ∧
    (∫ a : F.Carrier, ∫ u, signedWeylOrbitFourierKernel ψ ν m h Φ (u, a)
      ∂unipotentHaar F.Carrier (m + 1) ∂ν.measure) =
    ∫ a : F.Carrier, ∫ X : Matrix (Fin m) (Fin 1) F.Carrier,
      ∫ u, signedBlockOrbitKernel ψ m h Φ (u, (a, X))
        ∂unipotentHaar F.Carrier (m + 1)
      ∂rectangularMeasure ν m 1 ∂ν.measure := by
  obtain ⟨hl, hr, he⟩ :=
    signedWeylOrbit_blockOrbit_fourier_duality F ψ ν hsd m h hh Φ
  refine ⟨hl.integral_prod_right, hr.integral_prod_right, ?_⟩
  rw [integral_prod_symm _ hl, integral_prod_symm _ hr] at he
  exact he.trans (integral_prod _ hr.integral_prod_right)

end CanonicalPadic

end Langlands.RankinSelberg

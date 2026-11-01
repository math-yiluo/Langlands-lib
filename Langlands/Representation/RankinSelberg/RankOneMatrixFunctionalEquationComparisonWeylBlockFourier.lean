import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonAffineBlocks
import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylSigns

/-! Actual signed Weyl and rectangular block coordinates for the affine Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.RankinSelberg

open GeneralLinear HarmonicAnalysis
open UnequalRankComplementaryConjugationProof

universe uK

variable {K : Type uK} [Field K]

private theorem matrix_mul_permutation_entry {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (σ : Equiv.Perm (Fin r)) (i j : Fin r) :
    (M * (permutation r K σ).val) i j = M i (σ j) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ j)]
  · simp only [permutation_entry, ite_true, mul_one]
  · intro k _ hk
    simp only [permutation_entry, ite_eq_right (Ne.symm hk), mul_zero]
  · simp

private theorem weylLong_matrix_mul_entry {r : ℕ}
    (M : Matrix (Fin r) (Fin r) K) (i j : Fin r) :
    ((weylLong r K).val * M) i j = M i.rev j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i.rev]
  · simp only [weylLong_entry, Fin.rev_rev, ite_true, one_mul]
  · intro k _ hk
    have hki : k.rev ≠ i := by
      intro h
      apply hk
      simpa using congrArg Fin.rev h
    simp only [weylLong_entry, ite_eq_right hki, zero_mul]
  · simp

/-- The actual unsigned long/complementary Weyl product has positive
superdiagonal; all signs remain explicit in the signed version below. -/
theorem weylLong_scalarDiagonal_blockWeyl_entry (n : ℕ) (hn : 0 < n)
    (a : K) (i j : Fin (n + 1)) :
    ((weylLong (n + 1) K).val * Matrix.diagonal (Fin.cons a (fun _ => 1)) *
      (blockWeylAt 0 n hn).val : Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j =
    Matrix.diagonal (Fin.cons a (fun _ => 1)) i.rev (tailRev 0 n j) := by
  rw [blockWeylAt_eq, matrix_mul_permutation_entry, weylLong_matrix_mul_entry]
  rfl

private theorem blockWeyl_rankOne_inv (n : ℕ) (hn : 0 < n) :
    (blockWeylAt (F := K) 0 n hn)⁻¹ = blockWeylAt 0 n hn := by
  rw [blockWeylAt_eq, permutation_inv]
  rfl

private theorem adjacent_alternating_sign (n : ℕ) (i : Fin n) :
    (-1 : K) ^ (n - i.val) * (-1 : K) ^ (n - (i.val + 1)) = -1 := by
  have he : n - i.val = n - (i.val + 1) + 1 := by have := i.isLt; omega
  rw [he, pow_succ]
  calc
    _ = (-1 : K) * ((-1 : K) ^ (n - (i.val + 1)) *
        (-1 : K) ^ (n - (i.val + 1))) := by ring
    _ = -1 := by rw [← mul_pow]; simp

/-- The negative-superdiagonal affine shift is the actual signed Weyl
product, including the leading scalar sign `(-1)^(n+1)`. -/
theorem cyclicShiftMatrix_eq_signedWeyl (n : ℕ) (hn : 0 < n) (a : K) :
    cyclicShiftMatrix n a =
      (rankOneSignedWeyl (K := K) n)⁻¹.val *
        Matrix.diagonal (Fin.cons ((-1 : K) ^ (n + 1) * a) (fun _ => 1)) *
        (rankOneSignedBlockWeyl n hn)⁻¹.val := by
  simp only [rankOneSignedWeyl, rankOneSignedBlockWeyl, mul_inv_rev,
    rankOneWeylAlternating_inv, rankOneWeylLeadingSign_inv, weylLong_inv,
    blockWeyl_rankOne_inv, Units.val_mul]
  ext i j
  have hentry :
      (((rankOneWeylAlternating (K := K) n).val * (weylLong (n + 1) K).val) *
        Matrix.diagonal (Fin.cons ((-1 : K) ^ (n + 1) * a) (fun _ => 1)) *
        ((blockWeylAt 0 n hn).val * ((rankOneWeylLeadingSign (K := K) n).val *
          (rankOneWeylAlternating n).val)) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j =
      (-1 : K) ^ (n - i.val) *
        Matrix.diagonal (Fin.cons ((-1 : K) ^ (n + 1) * a) (fun _ => 1))
          i.rev (tailRev 0 n j) *
        (if j = 0 then (-1 : K) else 1) * (-1 : K) ^ (n - j.val) := by
    calc
      _ = ((rankOneWeylAlternating (K := K) n).val *
          (((weylLong (n + 1) K).val *
            Matrix.diagonal (Fin.cons ((-1 : K) ^ (n + 1) * a) (fun _ => 1)) *
            (blockWeylAt 0 n hn).val) *
            (rankOneWeylLeadingSign n).val * (rankOneWeylAlternating n).val) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) K) i j := by
        simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [rankOneWeylAlternating_val, rankOneWeylLeadingSign_val,
          Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.mul_diagonal,
          weylLong_scalarDiagonal_blockWeyl_entry n hn]
        ring
  rw [hentry]
  refine Fin.cases ?_ (fun k => ?_) j
  · have ht : tailRev 0 n (0 : Fin (n + 1)) = 0 := tailRev_of_lt 0 n (by simp)
    rw [ht]
    by_cases hi : i = Fin.last n
    · subst i
      simp only [Fin.rev_last, Matrix.diagonal_apply_eq, Fin.cons_zero,
        Fin.val_last, Nat.sub_self, pow_zero, one_mul, ite_true, Fin.val_zero,
        Nat.sub_zero]
      have hs : (-1 : K) ^ (n + 1) * (-1 : K) * (-1 : K) ^ n = 1 := by
        rw [pow_succ]
        calc
          _ = ((-1 : K) * (-1 : K)) *
              ((-1 : K) ^ n * (-1 : K) ^ n) := by ring
          _ = 1 := by rw [← mul_pow]; simp
      calc
        cyclicShiftMatrix n a (Fin.last n) 0 = a := by
          simp [cyclicShiftMatrix, negativeSuperdiagonal]
        _ = _ := by linear_combination -a * hs
    · have hir : i.rev ≠ 0 := by
        intro h
        apply hi
        simpa using congrArg Fin.rev h
      simp [Matrix.diagonal_apply_ne _ hir, cyclicShiftMatrix,
        negativeSuperdiagonal, Ne.symm hi]
  · have ht : (tailRev 0 n k.succ).val = n - k.val := by
      rw [tailRev_val_of_ge 0 n (by simp)]
      simp only [Fin.val_succ]
      omega
    have htn : tailRev 0 n k.succ ≠ 0 := by
      intro h
      have he := congrArg Fin.val h
      rw [ht] at he
      have := k.isLt
      simp only [Fin.val_zero] at he
      omega
    have he : i.rev = tailRev 0 n k.succ ↔ i = k.castSucc := by
      constructor <;> intro h
      · apply Fin.ext
        have hv := congrArg Fin.val h
        rw [Fin.val_rev, ht] at hv
        have := i.isLt
        have := k.isLt
        change i.val = k.val
        omega
      · subst i
        apply Fin.ext
        rw [Fin.val_rev, ht]
        simp only [Fin.val_castSucc]
        omega
    by_cases hi : i = k.castSucc
    · subst i
      rw [he.mpr rfl, Matrix.diagonal_apply_eq]
      have hc : Fin.cons (α := fun _ : Fin (n + 1) => K)
          ((-1 : K) ^ (n + 1) * a) (fun _ => 1)
          (tailRev 0 n k.succ) = 1 := by
        obtain ⟨t, ht⟩ := Fin.eq_succ_of_ne_zero htn
        rw [ht]
        rfl
      rw [hc]
      simp only [Fin.succ_ne_zero, ite_false, mul_one, Fin.val_castSucc, Fin.val_succ]
      rw [adjacent_alternating_sign]
      simp [cyclicShiftMatrix, negativeSuperdiagonal,
        Ne.symm (Fin.succ_ne_zero k)]
    · have hir : i.rev ≠ tailRev 0 n k.succ := fun h => hi (he.mp h)
      rw [Matrix.diagonal_apply_ne _ hir]
      have hiv : i.val ≠ k.val := fun h => hi (Fin.ext h)
      simp [cyclicShiftMatrix, negativeSuperdiagonal,
        Ne.symm (Fin.succ_ne_zero k), hiv]

section Kernels

variable [TopologicalSpace K] [IsTopologicalRing K] [MeasurableSpace K]

/-- The actual signed-Weyl scalar Fourier slice, with its inverse
Whittaker character and the fixed norm-one right parameter. -/
def signedWeylScalarFourierKernel (ψ : UnitaryAdditiveCharacter K)
    (ν : AdditiveHaarMeasure K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (z : upperUnipotent (m + 2) K × K) : ℂ :=
  (Whittaker.inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
    rectangularFourierIntegral ψ ν Φ
      ((z.1⁻¹).val.val.transpose * (rankOneSignedWeyl (m + 1))⁻¹.val *
        Matrix.diagonal (Fin.cons ((-1 : K) ^ (m + 2) * z.2) (fun _ => 1)) *
        (rankOneSignedBlockWeyl (m + 1) (by omega))⁻¹.val * h.val)

/-- The original Fourier slice in the actual scalar and rectangular
coordinates, with no invertibility restriction on the scalar. -/
def affineBlockFourierKernel (ψ : UnitaryAdditiveCharacter K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (z : upperUnipotent (m + 2) K × (K × Matrix (Fin m) (Fin 1) K)) : ℂ :=
  (Whittaker.inverseStandardCharacter ψ (m + 1) z.1 : ℂ) *
    Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
      (inverseTranspose (m + 2) K h).val)

omit [IsTopologicalRing K] [MeasurableSpace K] in
/-- At each invertible scalar, the affine kernel uses the literal
`blockMatrixAt m 0`, in the correct multiplication order. -/
theorem affineBlockFourierKernel_at_generalLinear
    (ψ : UnitaryAdditiveCharacter K) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) K)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) K))
    (u : upperUnipotent (m + 2) K) (g : Langlands.GeneralLinear 1 K)
    (X : Matrix (Fin m) (Fin 1) K) :
    affineBlockFourierKernel ψ m h Φ (u, (g 0 0, X)) =
      (Whittaker.inverseStandardCharacter ψ (m + 1) u : ℂ) *
        Φ (u.val * AdjacentBlockReduction.blockMatrixAt m 0 (by omega) g X *
          inverseTranspose (m + 2) K h).val := by
  simp only [affineBlockFourierKernel, firstColumnMatrix_eq_blockMatrixAt,
    Units.val_mul]

end Kernels

section CanonicalPadic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uK} p)

local instance weylBlockTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance weylBlockValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance weylBlockLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance weylBlockT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance weylBlockSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance weylBlockSigmaCompact : SigmaCompactSpace F.Carrier :=
  F.canonicalTopologicalData.sigmaCompactSpace
local instance weylBlockMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance weylBlockBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance weylBlockNMeasurableSpace (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance weylBlockNBorelSpace (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance weylBlockNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).isClosedEmbedding.locallyCompactSpace
local instance weylBlockNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F.Carrier) :=
  (upperEntryCoordinates (n + 1) (K := F.Carrier)).secondCountableTopology
local instance weylBlockTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

set_option maxHeartbeats 800000 in
/-- The actual affine Fourier equality in signed Weyl and rectangular block
coordinates. Both full product integrands are integrable for the same supplied
self-dual scalar Haar measure and the actual integral-normalized unipotent Haar. -/
theorem signedWeyl_affineBlock_fourier_duality
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F.Carrier)
    (hh : F.canonicalTopologicalData.determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F.Carrier)) :
    Integrable (signedWeylScalarFourierKernel ψ ν m h Φ)
      ((unipotentHaar F.Carrier (m + 1)).prod ν.measure) ∧
    Integrable (affineBlockFourierKernel ψ m h Φ)
      ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylScalarFourierKernel ψ ν m h Φ z
      ∂(unipotentHaar F.Carrier (m + 1)).prod ν.measure) =
    ∫ z, affineBlockFourierKernel ψ m h Φ z
      ∂(unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)) := by
  obtain ⟨hl, hr, he⟩ := padicUnipotentHaar_iota_fourier_duality_right
    F F.canonicalTopologicalData (m + 1) ψ ν hsd
      (unipotentHaar F.Carrier (m + 1)) h hh Φ
  let e := (MeasurableEquiv.refl (upperUnipotent (m + 2) F.Carrier)).prodCongr
    (rankOneAffineParametersEquiv (K := F.Carrier) m)
  have hp : MeasurePreserving e
      ((unipotentHaar F.Carrier (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)))
      ((unipotentHaar F.Carrier (m + 1)).prod (rowMeasure ν (m + 1))) :=
    (MeasurePreserving.id _).prod (rankOneAffineParameters_preserving ν m)
  have hri := hp.integrable_comp_of_integrable hr
  have hei := hp.integral_comp e.measurableEmbedding
    (fun z : upperUnipotent (m + 2) F.Carrier × (Fin (m + 1) → F.Carrier) =>
      inverseUnipotentFourierPhase ψ (m + 1) z.1 *
        Φ (z.1.val.val * firstColumnMatrix (m + 1) z.2 *
          (inverseTranspose (m + 2) F.Carrier h).val))
  change Integrable
    (fun z : upperUnipotent (m + 2) F.Carrier ×
        (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier) =>
      inverseUnipotentFourierPhase ψ (m + 1) z.1 *
        Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
          (inverseTranspose (m + 2) F.Carrier h).val)) _ at hri
  change (∫ z : upperUnipotent (m + 2) F.Carrier ×
      (F.Carrier × Matrix (Fin m) (Fin 1) F.Carrier),
    inverseUnipotentFourierPhase ψ (m + 1) z.1 *
      Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
        (inverseTranspose (m + 2) F.Carrier h).val)
    ∂(unipotentHaar F.Carrier (m + 1)).prod
      (ν.measure.prod (rectangularMeasure ν m 1))) = _ at hei
  have heq := he.trans hei.symm
  simpa +unfoldPartialApp only [signedWeylScalarFourierKernel, affineBlockFourierKernel,
    unipotentFourierSum_inverseCharacter,
    cyclicShiftMatrix_eq_signedWeyl (m + 1) (by omega), Matrix.mul_assoc]
    using And.intro hl (And.intro hri heq)

end CanonicalPadic

end Langlands.RankinSelberg

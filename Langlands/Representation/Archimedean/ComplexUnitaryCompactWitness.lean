import Langlands.Representation.Archimedean.ComplexUnitaryCompactChart
import Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension
import Mathlib.LinearAlgebra.Matrix.Block

/-! Compact test vectors for the signature calculation. -/

noncomputable section

open scoped Matrix Matrix.Norms.Operator
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.ComplexUnitary

open ComplexBlock ComplexPrincipalSeriesExtension
open ComplexGramFormula

variable {n : ℕ}

private theorem lowGram_unitary (k : ℕ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    lowGram k (U : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  simpa only [Matrix.one_mul, lowGram_one] using
    lowGram_mul_unitary k (1 : Matrix (Fin n) (Fin n) ℂ) U.2

/-- On the compact group the nonvanishing vector depends only on the angular weights. -/
theorem nzFunction_unitary (ds : List ComplexCharacterData) (U : Matrix.unitaryGroup (Fin n) ℂ) :
    nzFunction n ds (U : Matrix (Fin n) (Fin n) ℂ) =
      ∏ k : Fin n, lowMinor k (U : Matrix (Fin n) (Fin n) ℂ) ^ (nzWeight ds k).toNat *
        starRingEnd ℂ (lowMinor k (U : Matrix (Fin n) (Fin n) ℂ)) ^ (-nzWeight ds k).toNat := by
  simp [nzFunction, nzFactor, minorFactor, lowGram_unitary]

private theorem lowMinor_blockMat {p k : ℕ} (hp : p + 2 ≤ n) (hk : k ≠ p + 1)
    (M : Matrix (Fin 2) (Fin 2) ℂ) (hdet : M.det = 1) (Y : Matrix (Fin n) (Fin n) ℂ) :
    lowMinor k (blockMat p hp M * Y) = lowMinor k Y := by
  classical
  let B := blockMat p hp M
  let X : Matrix (LowIdx n k) (LowIdx n k) ℂ := B.submatrix Subtype.val Subtype.val
  have hsub : (B * Y).submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val =
      X * Y.submatrix Subtype.val Subtype.val := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply, X]
    rw [← Fintype.sum_subtype_add_sum_subtype (fun l : Fin n => k ≤ (l : ℕ))]
    suffices hzero : ∑ l : {l : Fin n // ¬ k ≤ (l : ℕ)}, B i.1 l.1 * Y l.1 j.1 = 0 by
      rw [hzero, add_zero]
    apply Finset.sum_eq_zero
    intro l _
    change blockMat p hp M i.1 l.1 * Y l.1 j.1 = 0
    have hil : i.1 ≠ l.1 := fun h => l.2 (h ▸ i.2)
    rcases mem_range_or p hp i.1 with ⟨a, ha⟩ | hi
    · have hl (b : Fin 2) : l.1 ≠ pos p hp b := by
        intro hb
        have h₁ := i.2
        have h₂ := l.2
        rw [ha, pos_val] at h₁
        rw [hb, pos_val] at h₂
        have ha' := a.isLt
        have hb' := b.isLt
        omega
      rw [blockMat_apply_right p hp M _ hl, Matrix.one_apply_ne hil, zero_mul]
    · rw [blockMat_apply_left p hp M hi, Matrix.one_apply_ne hil, zero_mul]
  have houtside (i : LowIdx n k) (hi : ∀ a, i.1 ≠ pos p hp a) (j : LowIdx n k) :
      X i j = (1 : Matrix (LowIdx n k) (LowIdx n k) ℂ) i j := by
    change blockMat p hp M i.1 j.1 = _
    rw [blockMat_apply_left p hp M hi, Matrix.one_apply, Matrix.one_apply]
    simp only [Subtype.ext_iff]
  have hX : X.det = 1 := by
    rcases le_or_gt k p with hkp | hpk
    · let inside : LowIdx n k → Prop := fun i => ∃ a : Fin 2, i.1 = pos p hp a
      rw [Matrix.twoBlockTriangular_det X inside]
      · have h₁ : (Matrix.toSquareBlockProp X inside).det = 1 := by
          let f : Fin 2 → {i : LowIdx n k // inside i} := fun a =>
            ⟨⟨pos p hp a, hkp.trans (Nat.le_add_right p a)⟩, a, rfl⟩
          let e := Equiv.ofBijective f ⟨fun a b hab => pos_injective p hp
            (congrArg (fun i : {i : LowIdx n k // inside i} => i.1.1) hab),
            fun i => by
              obtain ⟨a, ha⟩ := i.2
              exact ⟨a, Subtype.ext (Subtype.ext ha.symm)⟩⟩
          rw [← Matrix.det_submatrix_equiv_self e]
          have he : (Matrix.toSquareBlockProp X inside).submatrix e e = M := by
            ext a b
            exact blockMat_apply_pos p hp M a b
          rw [he, hdet]
        have h₂ : Matrix.toSquareBlockProp X (fun i => ¬inside i) = 1 := by
          ext i j
          change X i.1 j.1 = _
          rw [houtside i.1 (fun a ha => i.2 ⟨a, ha⟩), Matrix.one_apply, Matrix.one_apply]
          simp only [Subtype.ext_iff]
        rw [h₁, h₂, Matrix.det_one, mul_one]
      · intro i hi j hj
        exact (houtside i (fun a ha => hi ⟨a, ha⟩) j).trans
          (Matrix.one_apply_ne (fun h : i = j => hi (h.symm ▸ hj)))
    · have hI : X = 1 := by
        ext i j
        apply houtside i _ j
        intro a ha
        have hki := i.2
        rw [ha, pos_val] at hki
        have hlt := a.isLt
        omega
      rw [hI, Matrix.det_one]
  change ((B * Y).submatrix (Subtype.val : LowIdx n k → Fin n) Subtype.val).det = _
  rw [hsub, Matrix.det_mul, hX, one_mul]
  rfl

theorem nzFunction_blockU {pre post : List ComplexCharacterData} {d e : ComplexCharacterData}
    (p : ℕ) (hp : p + 2 ≤ n) (hpre : pre.length = p) (hwt : d.weight = e.weight)
    (M : Matrix.unitaryGroup (Fin 2) ℂ) (hdet : (M : Matrix (Fin 2) (Fin 2) ℂ).det = 1)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    nzFunction n (pre ++ d :: e :: post) (↑(blockU p hp M * U) : Matrix (Fin n) (Fin n) ℂ) =
      nzFunction n (pre ++ d :: e :: post) (U : Matrix (Fin n) (Fin n) ℂ) := by
  rw [nzFunction_unitary, nzFunction_unitary]
  refine Finset.prod_congr rfl fun k _ => ?_
  by_cases hk : (k : ℕ) = p + 1
  · have hw : nzWeight (pre ++ d :: e :: post) k = 0 := by
      rw [hk, ← hpre, nzWeight, tele, ComplexSwapJacquet.posWeight_append_cons_succ,
        ComplexSwapJacquet.posWeight_append_cons, hwt, sub_self]
    simp [hw]
  · change lowMinor k (blockMat p hp (M : Matrix (Fin 2) (Fin 2) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ)) ^ _ *
        starRingEnd ℂ (lowMinor k (blockMat p hp (M : Matrix (Fin 2) (Fin 2) ℂ) *
        (U : Matrix (Fin n) (Fin n) ℂ))) ^ _ = _
    rw [lowMinor_blockMat hp hk _ hdet]

/-- Squared absolute value of an entry, as a complex polynomial in entries and conjugates. -/
def entrySq (Y : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) : ℂ := Y i j * starRingEnd ℂ (Y i j)

/-- The difference of the squared entries in column `i` at rows `i` and `j`. -/
def rowDifference (i j : Fin n) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ := entrySq Y i i - entrySq Y j i

/-- The base test uses the constant factor and a test for a pair uses its row difference. -/
def testFactor (ij : Option (Fin n × Fin n)) (Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  match ij with
  | none => 1
  | some (i, j) => rowDifference i j Y

/-- Compact restrictions of the test vectors. -/
def compactTest (ds : List ComplexCharacterData) (ij : Option (Fin n × Fin n))
    (U : Matrix.unitaryGroup (Fin n) ℂ) : ℂ :=
  nzFunction n ds (U : Matrix (Fin n) (Fin n) ℂ) * testFactor ij U

theorem compactTest_one (ds : List ComplexCharacterData) (ij : Option (Fin n × Fin n))
    (h : ∀ i j, ij = some (i, j) → i ≠ j) : compactTest ds ij 1 = 1 := by
  have hz : nzFunction n ds (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
    simp [nzFunction, nzFactor, minorFactor, lowMinor_one, lowGram_one]
  change nzFunction n ds (1 : Matrix (Fin n) (Fin n) ℂ) * testFactor ij 1 = _
  rw [hz, one_mul]
  cases ij with
  | none => rfl
  | some ij =>
    rcases ij with ⟨i, j⟩
    simp [testFactor, rowDifference, entrySq, Matrix.one_apply_ne (h i j rfl).symm]

theorem compactTest_eq_of_posWeight_eq {ds es : List ComplexCharacterData}
    (h : posWeight ds = posWeight es) (ij : Option (Fin n × Fin n))
    (U : Matrix.unitaryGroup (Fin n) ℂ) : compactTest ds ij U = compactTest es ij U := by
  simp only [compactTest, nzFunction_unitary, nzWeight, h]

private theorem entrySq_phaseMatrix (a : Fin n → ℂˣ) (U : Matrix.unitaryGroup (Fin n) ℂ)
    (i j : Fin n) : entrySq (↑(phaseMatrix a * U) : Matrix (Fin n) (Fin n) ℂ) i j = entrySq U i j := by
  change entrySq ((phaseMatrix a : Matrix (Fin n) (Fin n) ℂ) * (U : Matrix (Fin n) (Fin n) ℂ)) i j = _
  have h : (phaseUnit (a i) : ℂ) * starRingEnd ℂ (phaseUnit (a i) : ℂ) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_phaseUnit]
    simp
  simp only [entrySq, phaseMatrix_val, Matrix.diagonal_mul, map_mul]
  rw [mul_mul_mul_comm, h, one_mul]

private theorem testFactor_phaseMatrix (ij : Option (Fin n × Fin n)) (a : Fin n → ℂˣ)
    (U : Matrix.unitaryGroup (Fin n) ℂ) :
    testFactor ij (↑(phaseMatrix a * U) : Matrix (Fin n) (Fin n) ℂ) = testFactor ij U := by
  cases ij with
  | none => rfl
  | some ij =>
    rcases ij with ⟨i, j⟩
    simp only [testFactor, rowDifference, entrySq_phaseMatrix]

private theorem testFactor_mem (ij : Option (Fin n × Fin n)) :
    (fun g : Langlands.GeneralLinear n ℂ => testFactor ij (g : Matrix (Fin n) (Fin n) ℂ)) ∈
      kFiniteSubalgebra (unitaryCompact ℂ n) := by
  cases ij with
  | none => exact Subalgebra.one_mem _
  | some ij =>
    rcases ij with ⟨i, j⟩
    apply Subalgebra.sub_mem
    · exact Subalgebra.mul_mem _ (entryFn_mem (RingHom.id ℂ) i i) (entryFn_mem (starRingEnd ℂ) i i)
    · exact Subalgebra.mul_mem _ (entryFn_mem (RingHom.id ℂ) j i) (entryFn_mem (starRingEnd ℂ) j i)

private theorem continuous_testFactor (ij : Option (Fin n × Fin n)) : Continuous (testFactor ij) := by
  cases ij with
  | none => exact continuous_const
  | some ij =>
    rcases ij with ⟨i, j⟩
    exact ((contDiff_entry i i).continuous.mul (contDiff_conj_entry i i).continuous).sub
      ((contDiff_entry j i).continuous.mul (contDiff_conj_entry j i).continuous)

/-- Each compact test is the restriction of a compact-finite vector in the principal series. -/
theorem exists_testVector (ds : List ComplexCharacterData) (ij : Option (Fin n × Fin n)) :
    ∃ v : KFs n ds, ∀ U : Matrix.unitaryGroup (Fin n) ℂ,
      (v : Langlands.GeneralLinear n ℂ → ℂ) (Unitary.toUnits U) = compactTest ds ij U := by
  let φ := compactTest ds ij
  have hc : Continuous φ :=
    ((contDiffOn_nzFunction ds).continuousOn.comp_continuous continuous_subtype_val
      (fun U => (Unitary.toUnits U).isUnit)).mul
        ((continuous_testFactor ij).comp continuous_subtype_val)
  let f : Langlands.GeneralLinear n ℂ → ℂ := fun g =>
    nzFunction n ds (g : Matrix (Fin n) (Fin n) ℂ) * testFactor ij g
  have hf : f ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n) :=
    (mem_kFiniteSubalgebra_iff _ _).1 (Subalgebra.mul_mem _ (nzFunction_mem ds) (testFactor_mem ij))
  have hfin : FiniteDimensional ℂ (Submodule.span ℂ
      (Set.range fun k : Matrix.unitaryGroup (Fin n) ℂ => fun x => φ (x * k))) := by
    rw [mem_kFiniteVectors_iff] at hf
    let W := Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      Whittaker.rightTranslation ℂ _ (k : Langlands.GeneralLinear n ℂ) f)
    have : FiniteDimensional ℂ W := hf
    let R : (Langlands.GeneralLinear n ℂ → ℂ) →ₗ[ℂ] (Matrix.unitaryGroup (Fin n) ℂ → ℂ) :=
      LinearMap.funLeft ℂ ℂ Unitary.toUnits
    apply Submodule.finiteDimensional_of_le (S₂ := W.map R)
    apply Submodule.span_le.mpr
    rintro _ ⟨U, rfl⟩
    let k : unitaryCompact ℂ n := ⟨Unitary.toUnits U, U.2⟩
    refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, ?_⟩
    funext x
    change f (Unitary.toUnits x * Unitary.toUnits U) = φ (x * U)
    rw [← map_mul]
    rfl
  have hcov (a : Fin n → ℂˣ) (U : Matrix.unitaryGroup (Fin n) ℂ) :
      φ (phaseMatrix a * U) =
        principalSeriesCharacter ℂ n (complexPositionCharacter ds) (fun i => phaseUnit (a i)) * φ U := by
    let g : Langlands.GeneralLinear n ℂ → ℂ := fun x => nzFunction n ds (x : Matrix (Fin n) (Fin n) ℂ)
    have hg := (ComplexSwapJacquet.nzFunction_mem_kFiniteFunctions (n := n) ds).1.2
      (fun i => phaseUnit (a i)) 1 (Unitary.toUnits U)
    have hdiag : Iwasawa.diagonalUnits (fun i => phaseUnit (a i)) = Unitary.toUnits (phaseMatrix a) :=
      Units.ext rfl
    rw [hdiag] at hg
    change g (Unitary.toUnits (phaseMatrix a) * 1 * Unitary.toUnits U) = _ at hg
    rw [mul_one, ← map_mul] at hg
    change g (Unitary.toUnits (phaseMatrix a * U)) = _ at hg
    change g (Unitary.toUnits (phaseMatrix a * U)) * testFactor ij (↑(phaseMatrix a * U) : Matrix (Fin n) (Fin n) ℂ) = _
    rw [hg, testFactor_phaseMatrix, mul_assoc]
    rfl
  obtain ⟨f, hf, he⟩ := complexPrincipalSeriesExtension n ds φ hc hfin hcov
  exact ⟨⟨f, hf⟩, he⟩

end Langlands.Archimedean.ComplexUnitary

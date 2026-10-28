import Langlands.Representation.Whittaker.TwoBlockJacquetCovarianceStatement
import Langlands.Representation.Whittaker.TwoBlockInducingCovarianceProof
import Langlands.Representation.Whittaker.TwoBlockCellUnipotentStabilityProof
import Langlands.Representation.Shahidi.JacquetDiagonalProof

/-! # Full upper-unipotent covariance of the scalar two-block Jacquet integral -/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section Algebra

variable {R : Type uF} [CommRing R] {m n : ℕ}

/-- A block diagonal matrix with upper-unipotent blocks is upper unipotent. -/
theorem blockSum_mem_upperUnipotent
    (u₁ : upperUnipotent m R) (u₂ : upperUnipotent n R) :
    blockSum (u₁.val, u₂.val) ∈ upperUnipotent (m + n) R := by
  constructor
  · intro i j hij
    induction i using Fin.addCases <;> induction j using Fin.addCases
    · rw [blockSum_apply_left]
      exact UpperUnipotent.entry_eq_zero u₁
        (by simpa only [id_eq, Fin.lt_def, Fin.val_castAdd] using hij)
    · simp only [id_eq, Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd] at hij
      omega
    · exact blockSum_apply_right_left _ _ _ _
    · rw [blockSum_apply_right]
      exact UpperUnipotent.entry_eq_zero u₂ (by simpa using hij)
  · intro i
    induction i using Fin.addCases <;> simp

/-- A full upper-unipotent matrix is an exchanged unipotent diagonal times
an exchanged radical element. -/
theorem upperUnipotent_exchanged_factorization (hm : 0 < m) (hn : 0 < n)
    (u : upperUnipotent (m + n) R) :
    ∃ (u₁ : upperUnipotent m R) (u₂ : upperUnipotent n R)
      (y : Matrix (Fin n) (Fin m) R),
      u.val = Shahidi.swapRank m n R (blockSum (u₂.val, u₁.val)) *
        Shahidi.intertwiningUnipotent m n R y := by
  let g : (Shahidi.twoBlocks n m hn hm).parabolic R :=
    ⟨(Shahidi.swapRank m n R).symm u.val, swapRank_symm_mem_parabolic hm hn R u⟩
  have hg : g.val ∈ upperUnipotent (n + m) R := by
    exact Shahidi.swapRank_mem_upperUnipotent n m R u.property
  have hα : (parabolicDiagonal hm hn R g).1 ∈ upperUnipotent n R := by
    constructor
    · intro i j hij
      rw [parabolicDiagonal_fst_apply]
      exact hg.1 (by simpa only [id_eq, Fin.lt_def, Fin.val_castAdd] using hij)
    · intro i
      rw [parabolicDiagonal_fst_apply]
      exact hg.2 _
  have hδ : (parabolicDiagonal hm hn R g).2 ∈ upperUnipotent m R := by
    constructor
    · intro i j hij
      rw [parabolicDiagonal_snd_apply]
      exact hg.1 (by simpa using hij)
    · intro i
      rw [parabolicDiagonal_snd_apply]
      exact hg.2 _
  refine ⟨⟨_, hδ⟩, ⟨_, hα⟩, parabolicShift hm hn R g 0, ?_⟩
  have h := congrArg (Shahidi.swapRank m n R)
    (upper_mul_parabolic hm hn R (0 : Matrix (Fin n) (Fin m) R) g)
  simpa only [Shahidi.upper_zero, one_mul, map_mul, g, MulEquiv.apply_symm_apply,
    Shahidi.intertwiningUnipotent] using h

/-- The first-superdiagonal sum of a block diagonal matrix is the sum from
its two diagonal blocks. -/
theorem sum_superdiagonal_blockSum {a b : ℕ}
    (g : Langlands.GeneralLinear (a + 1) R) (h : Langlands.GeneralLinear (b + 1) R) :
    (∑ i : Fin (a + 1 + b), blockSum (g, h) i.castSucc i.succ) =
      (∑ i : Fin a, g i.castSucc i.succ) + ∑ i : Fin b, h i.castSucc i.succ := by
  rw [Fin.sum_univ_add, Fin.sum_univ_castSucc]
  have h₁ (j : Fin a) :
      blockSum (g, h) (Fin.castAdd b j.castSucc).castSucc
        (Fin.castAdd b j.castSucc).succ = g j.castSucc j.succ := by
    have e₁ : ((Fin.castAdd b j.castSucc).castSucc : Fin (a + 1 + (b + 1))) =
        Fin.castAdd (b + 1) j.castSucc := Fin.ext (by simp)
    have e₂ : ((Fin.castAdd b j.castSucc).succ : Fin (a + 1 + (b + 1))) =
        Fin.castAdd (b + 1) j.succ := Fin.ext (by simp)
    rw [e₁, e₂, blockSum_apply_left]
  have h₂ (j : Fin b) :
      blockSum (g, h) (Fin.natAdd (a + 1) j).castSucc
        (Fin.natAdd (a + 1) j).succ = h j.castSucc j.succ := by
    have e₁ : ((Fin.natAdd (a + 1) j).castSucc : Fin (a + 1 + (b + 1))) =
        Fin.natAdd (a + 1) j.castSucc := Fin.ext (by simp)
    have e₂ : ((Fin.natAdd (a + 1) j).succ : Fin (a + 1 + (b + 1))) =
        Fin.natAdd (a + 1) j.succ := Fin.ext (by simp; omega)
    rw [e₁, e₂, blockSum_apply_right]
  have e₁ : ((Fin.castAdd b (Fin.last a)).castSucc : Fin (a + 1 + (b + 1))) =
      Fin.castAdd (b + 1) (Fin.last a) := Fin.ext (by simp)
  have e₂ : ((Fin.castAdd b (Fin.last a)).succ : Fin (a + 1 + (b + 1))) =
      (Fin.natAdd (a + 1) (0 : Fin (b + 1)) : Fin (a + 1 + (b + 1))) :=
    Fin.ext (by simp)
  simp_rw [h₁, h₂]
  rw [e₁, e₂, blockSum_apply_left_right, add_zero]

variable [TopologicalSpace R] (ψ : UnitaryAdditiveCharacter R)

/-- Arithmetic rank exchange preserves the positive standard character,
and its value on an exchanged diagonal is the product of the block values. -/
theorem standardCharacter_exchanged_blockSum {a b : ℕ}
    (u₁ : upperUnipotent (a + 1) R) (u₂ : upperUnipotent (b + 1) R) :
    (standardCharacter ψ (a + 1 + b)
      ⟨Shahidi.swapRank (a + 1) (b + 1) R (blockSum (u₂.val, u₁.val)),
        Shahidi.swapRank_mem_upperUnipotent _ _ R
          (blockSum_mem_upperUnipotent u₂ u₁)⟩ : ℂ) =
      (standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ) := by
  rw [standardCharacter_apply]
  have hs : (∑ i : Fin (a + 1 + b),
      Shahidi.swapRank (a + 1) (b + 1) R (blockSum (u₂.val, u₁.val))
        i.castSucc i.succ) =
      ∑ i : Fin (b + 1 + a), blockSum (u₂.val, u₁.val) i.castSucc i.succ := by
    let e : Fin (a + 1 + b) ≃ Fin (b + 1 + a) := finCongr (by omega)
    apply Fintype.sum_equiv e
    intro i
    change blockSum (u₂.val, u₁.val)
        (Fin.cast (Nat.add_comm (a + 1) (b + 1)) i.castSucc)
        (Fin.cast (Nat.add_comm (a + 1) (b + 1)) i.succ) =
      blockSum (u₂.val, u₁.val) (e i).castSucc (e i).succ
    congr 1
  rw [hs, sum_superdiagonal_blockSum, AddChar.map_add_eq_mul]
  exact mul_comm _ _

end Algebra

/-- Actual normalized inducing covariance, followed by radical and diagonal
changes of variables, gives full upper-unipotent scalar covariance. -/
theorem twoBlockJacquetCovariance : TwoBlockJacquetCovarianceStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.secondCountableTopology
  let := T.fieldT2
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  dsimp only
  intro ψ ℓ₁ hℓ₁ ℓ₂ hℓ₂ μ _ f u hi
  obtain ⟨u₁, u₂, y, hu⟩ :=
    upperUnipotent_exchanged_factorization (Nat.succ_pos a) (Nat.succ_pos b) u
  let ℓ := Shahidi.pairFunctional ℓ₁ ℓ₂
  let z := (standardCharacter ψ a u₁ : ℂ) * (standardCharacter ψ b u₂ : ℂ)
  let d := Shahidi.swapRank (a + 1) (b + 1) F.Carrier (blockSum (u₂.val, u₁.val))
  let fN := twoBlockInduced F a b π₁ π₂
    (Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier y) f
  have hNi : Integrable
      (Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ fN)) μ :=
    Shahidi.integrable_jacquetIntegrand_rightTranslate_intertwiningUnipotent
      ψ a b ℓ μ (twoBlockEval F a b π₁ π₂ f) y hi
  have hNe : (∫ x, Shahidi.jacquetIntegrand a b ψ ℓ
      (twoBlockEval F a b π₁ π₂ fN) x ∂μ) =
      (Shahidi.intertwiningCharacter a b ψ (Multiplicative.ofAdd y) : ℂ) *
        ∫ x, Shahidi.jacquetIntegrand a b ψ ℓ (twoBlockEval F a b π₁ π₂ f) x ∂μ :=
    Shahidi.integral_jacquetIntegrand_rightTranslate_intertwiningUnipotent
      ψ a b ℓ μ (twoBlockEval F a b π₁ π₂ f) y
  have hcov := twoBlockInducingWhittakerCovariance p F ψ a b π₁ π₂
    ℓ₁ hℓ₁ ℓ₂ hℓ₂ fN u₁ u₂
  have hd := (Shahidi.jacquetDiagonalCovariance p F T _ ψ a b ℓ μ u₁ u₂ z
    (twoBlockEval F a b π₁ π₂ fN) hcov).2.2 hNi
  have hfull :
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d)) =
        twoBlockEval F a b π₁ π₂ (twoBlockInduced F a b π₁ π₂ u.val f) := by
    funext g
    change twoBlockEval F a b π₁ π₂ f
      ((g * d) * Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier y) =
        twoBlockEval F a b π₁ π₂ f (g * u.val)
    rw [mul_assoc, ← hu]
  change Integrable (Shahidi.jacquetIntegrand a b ψ ℓ
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d))) μ ∧
    (∫ x, Shahidi.jacquetIntegrand a b ψ ℓ
      (fun g => twoBlockEval F a b π₁ π₂ fN (g * d)) x ∂μ) = _ at hd
  rw [hfull] at hd
  refine ⟨hd.1, ?_⟩
  rw [hd.2, hNe, ← mul_assoc]
  congr 1
  let du : upperUnipotent (a + 1 + (b + 1)) F.Carrier :=
    ⟨d, Shahidi.swapRank_mem_upperUnipotent _ _ _
      (blockSum_mem_upperUnipotent u₂ u₁)⟩
  let ny := Shahidi.intertwiningToUnipotent (a + 1) (b + 1) F.Carrier
    (Multiplicative.ofAdd y)
  have hu' : u = du * ny := Subtype.ext hu
  rw [hu', map_mul, Units.val_mul]
  rw [standardCharacter_exchanged_blockSum]
  rfl

end Langlands.Whittaker

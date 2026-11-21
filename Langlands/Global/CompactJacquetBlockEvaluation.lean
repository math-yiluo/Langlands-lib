import Langlands.Global.AdelicBlockParabolicPlaceDifferential
import Langlands.Representation.Archimedean.CompactJacquetStandardTensor

/-! # Jacquet equations for normalized block evaluations -/

noncomputable section

open scoped BigOperators TensorProduct

namespace Langlands.Global

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open RealLeviChart RealLeviSlices RealBlockPosition AdelicBlockDeterminantCharacter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

universe uR uW uE

variable {n : ℕ} (B : BlockShape n)

private theorem val_index (i : Fin B.length) (j : Fin (B.size i)) :
    (B.index i j : ℕ) = start B.size i + j :=
  val_pos B.size i j

private theorem index_ne_of_ne {i k : Fin B.length} (hik : i ≠ k)
    (a : Fin (B.size i)) (b : Fin (B.size k)) : B.index i a ≠ B.index k b :=
  fun h => hik (congrArg Sigma.fst (B.indexEquiv.injective h))

private theorem submatrix_single_same {R : Type*} [Zero R]
    (i : Fin B.length) (a : Fin (B.size i)) (z : R) :
    (Matrix.single (B.index i a) (B.index i a) z).submatrix (B.index i) (B.index i) =
      Matrix.single a a z := by
  ext b c
  simp [Matrix.single, Matrix.submatrix_apply, (B.index i).injective.eq_iff]

private theorem submatrix_single_of_ne {R : Type*} [Zero R]
    {i k : Fin B.length} (hik : i ≠ k) (a : Fin (B.size i)) (z : R) :
    (Matrix.single (B.index i a) (B.index i a) z).submatrix (B.index k) (B.index k) = 0 := by
  ext b c
  exact Matrix.single_apply_of_row_ne (index_ne_of_ne B hik a b) _ _ _

private theorem submatrix_strictUpper {R : Type*} [Zero R]
    {X : Matrix (Fin n) (Fin n) R} (hX : ∀ a b : Fin n, (b : ℕ) ≤ a → X a b = 0)
    (i : Fin B.length) (a b : Fin (B.size i)) (hba : (b : ℕ) ≤ a) :
    (X.submatrix (B.index i) (B.index i)) a b = 0 :=
  hX _ _ (by rw [val_index, val_index]; exact Nat.add_le_add_left hba _)

private theorem blockTrace_eq_zero_of_strictUpper {R : Type*} [AddCommMonoid R]
    {X : Matrix (Fin n) (Fin n) R} (hX : ∀ a b : Fin n, (b : ℕ) ≤ a → X a b = 0)
    (i : Fin B.length) : blockTrace B X i = 0 :=
  Finset.sum_eq_zero fun _ _ => hX _ _ le_rfl

private theorem blockTrace_single_same {R : Type*} [AddCommMonoid R]
    (i : Fin B.length) (a : Fin (B.size i)) (z : R) :
    blockTrace B (Matrix.single (B.index i a) (B.index i a) z) i = z := by
  change Matrix.trace ((Matrix.single (B.index i a) (B.index i a) z).submatrix
    (B.index i) (B.index i)) = z
  rw [submatrix_single_same, Matrix.trace_single_eq_same]

private theorem blockTrace_single_of_ne {R : Type*} [AddCommMonoid R]
    {i k : Fin B.length} (hik : i ≠ k) (a : Fin (B.size i)) (z : R) :
    blockTrace B (Matrix.single (B.index i a) (B.index i a) z) k = 0 := by
  change Matrix.trace ((Matrix.single (B.index i a) (B.index i a) z).submatrix
    (B.index k) (B.index k)) = 0
  rw [submatrix_single_of_ne B hik, Matrix.trace_zero]

section Common

variable {R : Type uR} [RCLike R]

local notation "L" => Matrix (Fin n) (Fin n) R

/-- The normalized local determinant differential contributes the real part of
each block trace with multiplicity `[R : ℝ]` and with the outer half exponent. -/
def blockHalfDifferential (X : L) : ℂ :=
  ↑(∑ i, blockHalfExponent B.size i * ((Module.finrank ℝ R : ℝ) * RCLike.re (blockTrace B X i)))

theorem blockHalfDifferential_real (X : Matrix (Fin n) (Fin n) ℝ) :
    blockHalfDifferential B X = (↑(∑ i, blockHalfExponent B.size i * blockTrace B X i) : ℂ) := by
  simp [blockHalfDifferential, RCLike.re_to_real]

theorem blockHalfDifferential_complex (X : Matrix (Fin n) (Fin n) ℂ) :
    blockHalfDifferential B X =
      (↑(∑ i, blockHalfExponent B.size i * (2 * (blockTrace B X i).re)) : ℂ) := by
  simp [blockHalfDifferential, Complex.finrank_real_complex]

private theorem blockHalfDifferential_single (i : Fin B.length) (a : Fin (B.size i)) (z : R) :
    blockHalfDifferential B (Matrix.single (B.index i a) (B.index i a) z) =
      (↑(blockHalfExponent B.size i * ((Module.finrank ℝ R : ℝ) * RCLike.re z)) : ℂ) := by
  unfold blockHalfDifferential
  rw [Finset.sum_eq_single i]
  · rw [blockTrace_single_same B]
  · intro k _ hki
    rw [blockTrace_single_of_ne B hki.symm]
    simp
  · simp

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The Lie identity of a normalized parabolic evaluation on upper triangular
directions. The Levi operators act on the diagonal blocks and the half-modulus
contributes `blockHalfDifferential`. -/
def IsNormalizedBlockLieEvaluation (π : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ E)
    (ev : W →ₗ[ℂ] E) : Prop :=
  ∀ X : L, X.IsUpperTriangular → ∀ w : W,
    ev (π (1 ⊗ₜ X) w) =
      (∑ i, A i (X.submatrix (B.index i) (B.index i)) (ev w)) +
        blockHalfDifferential B X • ev w

private theorem probe_vanishes_of_strictUpper
    {B : BlockShape n} {lie : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W}
    {A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ E}
    {ev : W →ₗ[ℂ] E} (hEv : IsNormalizedBlockLieEvaluation B lie A ev)
    (probe : E →ₗ[ℂ] ℂ)
    (hN : ∀ (i : Fin B.length) (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R),
      (∀ a b : Fin (B.size i), (b : ℕ) ≤ a → X a b = 0) → ∀ z, probe (A i X z) = 0)
    (X : L)
    (hX : ∀ a b : Fin n, (b : ℕ) ≤ a → X a b = 0) (w : W) :
    probe (ev (lie (1 ⊗ₜ X) w)) = 0 := by
  have hU : X.IsUpperTriangular := fun a b hab => hX a b hab.le
  have hδ : blockHalfDifferential B X = 0 := by
    simp [blockHalfDifferential, blockTrace_eq_zero_of_strictUpper B hX]
  rw [hEv X hU, hδ, zero_smul, add_zero, map_sum]
  exact Finset.sum_eq_zero fun i _ => hN i _ (submatrix_strictUpper B hX i) _

private theorem probe_single_diagonal
    {B : BlockShape n} {lie : (ℂ ⊗[ℝ] L) →ₗ⁅ℂ⁆ Module.End ℂ W}
    {A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) R → Module.End ℂ E}
    {ev : W →ₗ[ℂ] E} (hEv : IsNormalizedBlockLieEvaluation B lie A ev)
    (probe : E →ₗ[ℂ] ℂ)
    (hN : ∀ (i : Fin B.length) (X : Matrix (Fin (B.size i)) (Fin (B.size i)) R),
      (∀ a b : Fin (B.size i), (b : ℕ) ≤ a → X a b = 0) → ∀ z, probe (A i X z) = 0)
    (i : Fin B.length) (a : Fin (B.size i)) (z : R)
    (c : ℂ) (hc : ∀ e, probe (A i (Matrix.single a a z) e) = c * probe e) (w : W) :
    probe (ev (lie (1 ⊗ₜ Matrix.single (B.index i a) (B.index i a) z) w)) =
      (c + blockHalfDifferential B (Matrix.single (B.index i a) (B.index i a) z)) * probe (ev w) := by
  let X : L := Matrix.single (B.index i a) (B.index i a) z
  have hU : X.IsUpperTriangular := by
    intro b d hdb
    apply Matrix.single_apply_of_ne
    rintro ⟨hb, hd⟩
    exact hdb.ne (hd.symm.trans hb)
  change probe (ev (lie (1 ⊗ₜ X) w)) = _
  rw [hEv X hU, map_add, map_sum, map_smul, smul_eq_mul, add_mul, Finset.sum_eq_single i]
  · rw [submatrix_single_same B, hc]
  · intro k _ hki
    rw [submatrix_single_of_ne B hki.symm]
    exact hN k 0 (fun _ _ _ => rfl) _
  · simp

end Common

section Real

private theorem realPositionLookup_flat {D : Type*} (f : List RealBlock → ℕ → D)
    (happend : ∀ ds es p, f (ds ++ es) p =
      if p < realRank ds then f ds p else f es (p - realRank ds)) :
    ∀ {c : ℕ} (ds : Fin c → List RealBlock) (i : Fin c) (a : ℕ), a < sz ds i →
      f (flat ds) (start (sz ds) i + a) = f (ds i) a
  | 0, _, i, _, _ => i.elim0
  | c + 1, ds, i, a, ha => by
    rw [flat_succ, happend]
    induction i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, start_zero', zero_add, ite_eq_left (show a < realRank (ds 0) from ha)]
    | succ i =>
      rw [Fin.val_succ, start_succ', add_assoc, show sz ds 0 = realRank (ds 0) from rfl,
        ite_eq_right (by omega), Nat.add_sub_cancel_left]
      exact realPositionLookup_flat f happend (fun j => ds j.succ) i a ha

theorem realShiftedExponent_index (ds : Fin B.length → List RealBlock)
    (hs : ∀ i, realRank (ds i) = B.size i) (i : Fin B.length) (a : Fin (B.size i)) :
    shiftedExponent n (flat ds) (B.index i a) =
      shiftedExponent (B.size i) (ds i) a + (blockHalfExponent B.size i : ℂ) := by
  have hsize : B.size = sz ds := funext fun k => (hs k).symm
  have ha : (a : ℕ) < sz ds i := by
    change (a : ℕ) < realRank (ds i)
    rw [hs i]
    exact a.isLt
  have hexp : GramFormula.realPositionExponent (flat ds) (B.index i a) =
      GramFormula.realPositionExponent (ds i) a := by
    rw [val_index, congrArg (fun s => start s i) hsize]
    exact realPositionLookup_flat _ realPositionExponent_append ds i a ha
  unfold shiftedExponent
  rw [hexp, val_index, blockHalfExponent_eq_rank, B.sum_eq]
  push_cast
  ring

theorem realPositionSign_index (ds : Fin B.length → List RealBlock)
    (hs : ∀ i, realRank (ds i) = B.size i) (i : Fin B.length) (a : Fin (B.size i)) :
    positionSign n (flat ds) (B.index i a) = positionSign (B.size i) (ds i) a := by
  have hsize : B.size = sz ds := funext fun k => (hs k).symm
  have ha : (a : ℕ) < sz ds i := by
    change (a : ℕ) < realRank (ds i)
    rw [hs i]
    exact a.isLt
  unfold positionSign
  rw [val_index, congrArg (fun s => start s i) hsize]
  exact realPositionLookup_flat _ realPositionSign_append ds i a ha

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The upper triangular Lie and sign equations on block evaluations give the
Jacquet equations of the ordered concatenation of real standard blocks. -/
theorem isRealJacquetFunctional_of_normalizedBlockEvaluation
    (ds : Fin B.length → List RealBlock) (hs : ∀ i, realRank (ds i) = B.size i)
    (κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) W)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) ℝ → Module.End ℂ E)
    (ev : W →ₗ[ℂ] E) (hEv : IsNormalizedBlockLieEvaluation B π A ev)
    (probe : E →ₗ[ℂ] ℂ)
    (hN : ∀ (i : Fin B.length) (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℝ),
      (∀ a b : Fin (B.size i), (b : ℕ) ≤ a → X a b = 0) → ∀ e, probe (A i X e) = 0)
    (hD : ∀ (i : Fin B.length) (a : Fin (B.size i)) e,
      probe (A i (Matrix.single a a 1) e) = shiftedExponent (B.size i) (ds i) a * probe e)
    (hS : ∀ (i : Fin B.length) (a : Fin (B.size i)) w,
      probe (ev (κ (signReflection n (B.index i a)) w)) =
        (-1) ^ (positionSign (B.size i) (ds i) a).val * probe (ev w)) :
    IsRealJacquetFunctional n κ π (probe.comp ev) (shiftedExponent n (flat ds))
      (positionSign n (flat ds)) := by
  refine ⟨probe_vanishes_of_strictUpper hEv probe hN, ?_⟩
  intro j w
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective j
  change probe (ev (π (1 ⊗ₜ Matrix.single (B.index i a) (B.index i a) 1) w)) =
      shiftedExponent n (flat ds) (B.index i a) * probe (ev w) ∧
    probe (ev (κ (signReflection n (B.index i a)) w)) =
      (-1) ^ (positionSign n (flat ds) (B.index i a)).val * probe (ev w)
  rw [realShiftedExponent_index B ds hs, realPositionSign_index B ds hs]
  refine ⟨?_, hS i a w⟩
  rw [probe_single_diagonal hEv probe hN i a 1 _ (hD i a),
    blockHalfDifferential_single B]
  simp

end Real

section Complex

variable {d : Fin n → ComplexCharacterData}
  {ds : ∀ i : Fin B.length, Fin (B.size i) → ComplexCharacterData}

theorem complexShiftedExponent_index (hd : ∀ i a, d (B.index i a) = ds i a)
    (i : Fin B.length) (a : Fin (B.size i)) :
    complexShiftedExponent d (B.index i a) =
      complexShiftedExponent (ds i) a + 2 * (blockHalfExponent B.size i : ℂ) := by
  unfold complexShiftedExponent
  rw [hd, val_index, blockHalfExponent_eq_rank, B.sum_eq]
  push_cast
  ring

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {E : Type uE} [AddCommGroup E] [Module ℂ E]

/-- The upper triangular Lie equations on block evaluations give the complex
Jacquet equations, with the outer half-modulus contributing to the real direction. -/
theorem isComplexJacquetFunctional_of_normalizedBlockEvaluation
    (hd : ∀ i a, d (B.index i a) = ds i a)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (A : ∀ i : Fin B.length, Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ → Module.End ℂ E)
    (ev : W →ₗ[ℂ] E) (hEv : IsNormalizedBlockLieEvaluation B π A ev)
    (probe : E →ₗ[ℂ] ℂ)
    (hN : ∀ (i : Fin B.length) (X : Matrix (Fin (B.size i)) (Fin (B.size i)) ℂ),
      (∀ a b : Fin (B.size i), (b : ℕ) ≤ a → X a b = 0) → ∀ e, probe (A i X e) = 0)
    (hD : ∀ (i : Fin B.length) (a : Fin (B.size i)) e,
      probe (A i (Matrix.single a a 1) e) = complexShiftedExponent (ds i) a * probe e)
    (hPhase : ∀ (i : Fin B.length) (a : Fin (B.size i)) e,
      probe (A i (Matrix.single a a Complex.I) e) = (Complex.I * ((ds i a).weight : ℂ)) * probe e) :
    IsComplexJacquetFunctional n π (probe.comp ev) (complexShiftedExponent d)
      (fun j => Complex.I * ((d j).weight : ℂ)) := by
  refine ⟨probe_vanishes_of_strictUpper hEv probe hN, ?_⟩
  intro j w
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective j
  change probe (ev (π (1 ⊗ₜ Matrix.single (B.index i a) (B.index i a) 1) w)) =
      complexShiftedExponent d (B.index i a) * probe (ev w) ∧
    probe (ev (π (1 ⊗ₜ Matrix.single (B.index i a) (B.index i a) Complex.I) w)) =
      (Complex.I * ((d (B.index i a)).weight : ℂ)) * probe (ev w)
  rw [complexShiftedExponent_index B hd, hd]
  constructor
  · rw [probe_single_diagonal hEv probe hN i a 1 _ (hD i a), blockHalfDifferential_single B]
    simp [Complex.finrank_real_complex, mul_comm]
  · rw [probe_single_diagonal hEv probe hN i a Complex.I _ (hPhase i a),
      blockHalfDifferential_single B]
    simp

end Complex

end Langlands.Global

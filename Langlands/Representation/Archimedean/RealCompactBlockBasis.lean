import Langlands.Representation.Archimedean.RealCompactWitnessExtension
import Langlands.Representation.Archimedean.RealInducedStandardBound
import Langlands.Representation.Archimedean.RealBlockFlatJacquet
import Langlands.Representation.Archimedean.RealBlockPositionData
import Langlands.Representation.Archimedean.RealStandardBlockPolynomial
import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Complex coordinates for real compact standard modules

Each two-dimensional induction block is split into its two rotation eigencoordinates.
The other coordinates are unchanged.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.RealCompactBlockBasis

open Langlands.LocalFactor.Archimedean RealBlockRotation
open RealBlockFlatJacquet (rot_mul_ia rot_mul_ib rot_mul_of_ne expMode_one_eq expMode_neg_one_eq)
open RealBlockFourierFinite RealCompactWitnessExtension PrincipalSeriesExtension GramFormula

local notation "O(" n ")" => Matrix.unitaryGroup (Fin n) ℝ

/-- Starting positions of the two-dimensional blocks. -/
abbrev Pair (n : ℕ) (ds : List RealBlock) :=
  {p : Fin n // (realInducedBlockAt ds p).isSome}

/-- Positions outside the two-dimensional blocks. -/
abbrev Singleton (n : ℕ) (ds : List RealBlock) :=
  {i : Fin n // ∀ p : Pair n ds, i.val ≠ p.val.val ∧ i.val ≠ p.val.val + 1}

/-- The two coordinates of each induction block and one of each residual position. -/
abbrev Rows (n : ℕ) (ds : List RealBlock) := (Pair n ds × Bool) ⊕ Singleton n ds

variable {n : ℕ} {ds : List RealBlock}

/-- The inducing datum at a block's starting position. -/
def Pair.datum (p : Pair n ds) : ComplexCharacterData :=
  (realInducedBlockAt ds p.val).get p.prop

theorem Pair.induced_at (p : Pair n ds) : realInducedBlockAt ds p.val = some p.datum :=
  (Option.some_get p.prop).symm

theorem Pair.second_lt (p : Pair n ds) (hRank : realRank ds = n) : p.val.val + 1 < n := by
  have h := realInducedBlockAt_lt p.induced_at
  omega

private theorem no_adjacent_starts (p q : Pair n ds) : p.val.val ≠ q.val.val + 1 := by
  intro h
  have hp := p.induced_at
  change realInducedBlockAt ds p.val.val = some p.datum at hp
  rw [h, (RealInducedStandardBound.induced_at q.induced_at).2.2.2.2.2.2] at hp
  cases hp

/-- The original axis of a block, with `true` denoting the first position. -/
def axis (hRank : realRank ds = n) (p : Pair n ds) : Bool → Fin n
  | true => p.val
  | false => ib (p.second_lt hRank)

private theorem axis_injective (hRank : realRank ds = n) :
    Function.Injective (fun x : Pair n ds × Bool => axis hRank x.1 x.2) := by
  rintro ⟨p, b⟩ ⟨q, c⟩ h
  have hv := congrArg Fin.val h
  change (axis hRank p b).val = (axis hRank q c).val at hv
  have hp := no_adjacent_starts p q
  have hq := no_adjacent_starts q p
  cases b <;> cases c <;> simp only [axis, ib] at hv
  · have e : p.val.val = q.val.val := by omega
    exact Prod.ext (Subtype.ext (Fin.ext e)) rfl
  · exact (hq hv.symm).elim
  · exact (hp hv).elim
  · exact Prod.ext (Subtype.ext (Fin.ext hv)) rfl

private def position (hRank : realRank ds = n) : Rows n ds → Fin n
  | .inl (p, b) => axis hRank p b
  | .inr i => i.val

/-- Enumerate all original axes by their block and coordinate. -/
def placement (hRank : realRank ds = n) : Rows n ds ≃ Fin n :=
  Equiv.ofBijective (position hRank) (by
    constructor
    · intro i j h
      cases i with
      | inl pb =>
        obtain ⟨p, b⟩ := pb
        cases j with
        | inl qc => exact congrArg Sum.inl (axis_injective hRank (a₁ := (p, b)) (a₂ := qc) h)
        | inr j =>
          have hj := j.prop p
          have hv := congrArg Fin.val h
          cases b <;> simp only [position, axis, ib] at hv
          · exact (hj.2 hv.symm).elim
          · exact (hj.1 hv.symm).elim
      | inr i =>
        cases j with
        | inl qc =>
          obtain ⟨q, c⟩ := qc
          have hi := i.prop q
          have hv := congrArg Fin.val h
          cases c <;> simp only [position, axis, ib] at hv
          · exact (hi.2 hv).elim
          · exact (hi.1 hv).elim
        | inr j => exact congrArg Sum.inr (Subtype.ext h)
    · intro i
      by_cases h : ∃ x : Pair n ds × Bool, axis hRank x.1 x.2 = i
      · obtain ⟨⟨p, b⟩, e⟩ := h
        exact ⟨.inl (p, b), e⟩
      · refine ⟨.inr ⟨i, fun p => ⟨?_, ?_⟩⟩, rfl⟩
        · exact fun e => h ⟨(p, true), Fin.ext e.symm⟩
        · exact fun e => h ⟨(p, false), Fin.ext e.symm⟩)

@[simp] theorem placement_inl (hRank : realRank ds = n) (p : Pair n ds) (b : Bool) :
    placement hRank (.inl (p, b)) = axis hRank p b := rfl

@[simp] theorem placement_inr (hRank : realRank ds = n) (i : Singleton n ds) :
    placement hRank (.inr i) = i.val := rfl

private def imaginarySign : Bool → ℂ
  | true => Complex.I
  | false => -Complex.I

private def basisMatrix : Matrix (Rows n ds) (Rows n ds) ℂ := Matrix.of fun
  | .inl (p, b), j =>
    (if j = .inl (p, true) then 1 else 0) +
      (if j = .inl (p, false) then imaginarySign b else 0)
  | .inr i, j => if j = .inr i then 1 else 0

private def basisInverse : Matrix (Rows n ds) (Rows n ds) ℂ := Matrix.of fun
  | .inl (p, b), j =>
    (if j = .inl (p, true) then (if b then 1 else -Complex.I) / 2 else 0) +
      (if j = .inl (p, false) then (if b then 1 else Complex.I) / 2 else 0)
  | .inr i, j => if j = .inr i then 1 else 0

private theorem basisMatrix_mul_pair (M : Matrix (Rows n ds) (Rows n ds) ℂ)
    (p : Pair n ds) (b : Bool) (j : Rows n ds) :
    (basisMatrix (n := n) (ds := ds) * M) (.inl (p, b)) j =
      M (.inl (p, true)) j + imaginarySign b * M (.inl (p, false)) j := by
  simp only [basisMatrix, Matrix.mul_apply, Matrix.of_apply, add_mul,
    ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

private theorem basisMatrix_mul_single (M : Matrix (Rows n ds) (Rows n ds) ℂ)
    (i : Singleton n ds) (j : Rows n ds) :
    (basisMatrix (n := n) (ds := ds) * M) (.inr i) j = M (.inr i) j := by
  simp only [basisMatrix, Matrix.mul_apply, Matrix.of_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem basis_mul_inverse :
    basisMatrix * basisInverse = (1 : Matrix (Rows n ds) (Rows n ds) ℂ) := by
  ext i j
  cases i with
  | inl pb =>
    obtain ⟨p, b⟩ := pb
    rw [basisMatrix_mul_pair, Matrix.one_apply]
    cases j with
    | inl qc =>
      obtain ⟨q, c⟩ := qc
      by_cases e : p = q
      · subst q
        cases b <;> cases c <;> norm_num [basisInverse, imaginarySign, ← mul_div_assoc]
      · have e' : q ≠ p := Ne.symm e
        simp [basisInverse, e, e']
    | inr j => simp [basisInverse]
  | inr i =>
    rw [basisMatrix_mul_single, Matrix.one_apply]
    simp [basisInverse, eq_comm]

private theorem inverse_mul_basis :
    basisInverse * basisMatrix = (1 : Matrix (Rows n ds) (Rows n ds) ℂ) :=
  mul_eq_one_comm.mp basis_mul_inverse

private def originalMatrix (hRank : realRank ds = n) :
    O(n) →* Matrix (Rows n ds) (Rows n ds) ℂ :=
  Complex.ofRealHom.mapMatrix.toMonoidHom.comp
    ((Matrix.reindexRingEquiv ℝ (placement hRank).symm).toMonoidHom.comp
      (Matrix.unitaryGroup (Fin n) ℝ).subtype)

private theorem originalMatrix_apply (hRank : realRank ds = n) (k : O(n))
    (i j : Rows n ds) :
    originalMatrix hRank k i j = ((k.val (placement hRank i) (placement hRank j) : ℝ) : ℂ) :=
  rfl

/-- The orthogonal action expressed in complex rotation coordinates. -/
def compactMatrix (hRank : realRank ds = n) :
    O(n) →* Matrix (Rows n ds) (Rows n ds) ℂ where
  toFun k := basisMatrix * originalMatrix hRank k * basisInverse
  map_one' := by rw [map_one, Matrix.mul_one, basis_mul_inverse]
  map_mul' k l := by
    rw [map_mul]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc basisInverse basisMatrix, inverse_mul_basis, Matrix.one_mul]

theorem continuous_compactMatrix (hRank : realRank ds = n) :
    Continuous (compactMatrix hRank) := by
  have h : Continuous (originalMatrix hRank) := by
    apply continuous_matrix
    intro i j
    simp only [originalMatrix_apply]
    exact Complex.continuous_ofReal.comp
      ((continuous_apply_apply _ _).comp continuous_subtype_val)
  exact (continuous_const.mul h).mul continuous_const

private theorem compactMatrix_eq_of_intertwine (hRank : realRank ds = n) (k : O(n))
    (M : Matrix (Rows n ds) (Rows n ds) ℂ)
    (h : basisMatrix * originalMatrix hRank k = M * basisMatrix) : compactMatrix hRank k = M := by
  change basisMatrix * originalMatrix hRank k * basisInverse = M
  rw [h, Matrix.mul_assoc, basis_mul_inverse, Matrix.mul_one]

/-- The integer mode of a row under rotation in the indicated block. -/
def rotationMode (p : Pair n ds) : Rows n ds → ℤ
  | .inl (q, b) => if q = p then if b then 1 else -1 else 0
  | .inr _ => 0

/-- A rotation acts by the two opposite modes of its block. -/
theorem compactMatrix_rotation (hRank : realRank ds = n) (p : Pair n ds) (θ : ℝ) :
    compactMatrix hRank (compactBlockRotation n p.val θ) =
      Matrix.diagonal (fun i => expMode (rotationMode p i) θ) := by
  apply compactMatrix_eq_of_intertwine
  let R := originalMatrix hRank (compactBlockRotation n p.val θ)
  let U : Matrix (Rows n ds) (Rows n ds) ℂ := 1
  let hb := p.second_lt hRank
  have hR (i j : Rows n ds) :
      R i j = (((blockRotation n p.val θ : Matrix (Fin n) (Fin n) ℝ)
        (placement hRank i) (placement hRank j) : ℝ) : ℂ) := rfl
  have hU (i j : Rows n ds) :
      (((1 : Matrix (Fin n) (Fin n) ℝ) (placement hRank i) (placement hRank j) : ℝ) : ℂ) =
        U i j := by
    change originalMatrix hRank (1 : O(n)) i j = U i j
    rw [map_one]
  have ht : placement hRank (.inl (p, true)) = ia hb := rfl
  have hf : placement hRank (.inl (p, false)) = ib hb := rfl
  have hFirst (j : Rows n ds) : R (.inl (p, true)) j =
      (Real.cos θ : ℂ) * U (.inl (p, true)) j - (Real.sin θ : ℂ) * U (.inl (p, false)) j := by
    have h := rot_mul_ia hb θ 1 (placement hRank j)
    rw [Matrix.mul_one, ← ht, ← hf] at h
    rw [hR, h, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_mul, hU, hU]
  have hSecond (j : Rows n ds) : R (.inl (p, false)) j =
      (Real.sin θ : ℂ) * U (.inl (p, true)) j + (Real.cos θ : ℂ) * U (.inl (p, false)) j := by
    have h := rot_mul_ib hb θ 1 (placement hRank j)
    rw [Matrix.mul_one, ← ht, ← hf] at h
    rw [hR, h, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_mul, hU, hU]
  have hOther (i j : Rows n ds) (h₁ : i ≠ .inl (p, true)) (h₂ : i ≠ .inl (p, false)) :
      R i j = U i j := by
    have hi₁ : placement hRank i ≠ ia hb := fun e => h₁ ((placement hRank).injective (e.trans ht.symm))
    have hi₂ : placement hRank i ≠ ib hb := fun e => h₂ ((placement hRank).injective (e.trans hf.symm))
    have h := rot_mul_of_ne hb θ 1 hi₁ hi₂ (placement hRank j)
    rw [Matrix.mul_one] at h
    rw [hR, h, hU]
  change basisMatrix * R = _
  ext i j
  rw [Matrix.diagonal_mul]
  cases i with
  | inl qb =>
    obtain ⟨q, b⟩ := qb
    have hB := basisMatrix_mul_pair U q b j
    rw [show basisMatrix * U = basisMatrix from Matrix.mul_one _] at hB
    rw [basisMatrix_mul_pair, hB]
    by_cases hqp : q = p
    · subst q
      rw [hFirst, hSecond]
      cases b
      · simp only [rotationMode, ite_true, Bool.false_eq_true, ite_false, expMode_neg_one_eq,
          imaginarySign]
        linear_combination (-(Real.sin θ : ℂ) * U (.inl (p, false)) j) * Complex.I_sq
      · simp only [rotationMode, ite_true, expMode_one_eq, imaginarySign]
        linear_combination (-(Real.sin θ : ℂ) * U (.inl (p, false)) j) * Complex.I_sq
    · rw [hOther _ _ (by simp [hqp]) (by simp), hOther _ _ (by simp) (by simp [hqp])]
      simp [rotationMode, hqp, expMode_zero_left]
  | inr i =>
    have hB := basisMatrix_mul_single U i j
    rw [show basisMatrix * U = basisMatrix from Matrix.mul_one _] at hB
    rw [basisMatrix_mul_single, hB, hOther _ _ (by simp) (by simp)]
    simp [rotationMode, expMode_zero_left]

/-- The relative sign of the second axis of a block with respect to its first. -/
def signFlip (hRank : realRank ds = n) (a : Fin n → ℝ) (p : Pair n ds) : Bool :=
  decide (signReal (a (axis hRank p true)) ≠ signReal (a (axis hRank p false)))

/-- The common sign on a block after extracting its relative second-axis reflection. -/
def signGain (a : Fin n → ℝ) : Rows n ds → ℂ
  | .inl (p, _) => signReal (a p.val)
  | .inr i => signReal (a i.val)

private theorem signs_opposite {x y : ℝ} (h : signReal x ≠ signReal y) :
    signReal y = -signReal x := by
  rcases RealStandardNontrivial.signReal_eq_one_or x with hx | hx <;>
    rcases RealStandardNontrivial.signReal_eq_one_or y with hy | hy <;> simp_all

/-- A sign diagonal acts by common signs and interchanges the two eigencoordinates
of precisely the pairs whose original axes have different signs. -/
theorem compactMatrix_signDiagonal (hRank : realRank ds = n) (a : Fin n → ℝ)
    (σ : Equiv.Perm (Rows n ds))
    (hp : ∀ p b, σ (.inl (p, b)) = .inl (p, if signFlip hRank a p then !b else b))
    (hi : ∀ i, σ (.inr i) = .inr i) :
    compactMatrix hRank (signDiagonal a) = Matrix.diagonal (signGain a) * σ.permMatrix ℂ := by
  let s (i : Rows n ds) : ℂ := signReal (a (placement hRank i))
  have hA : originalMatrix hRank (signDiagonal a) = Matrix.diagonal s := by
    ext i j
    rw [originalMatrix_apply]
    change (↑(Matrix.diagonal (fun k => signReal (a k)) (placement hRank i) (placement hRank j)) :
      ℂ) = Matrix.diagonal s i j
    simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]
    split_ifs <;> simp [s]
  apply compactMatrix_eq_of_intertwine
  rw [hA, Matrix.mul_assoc, Equiv.Perm.permMatrix, PEquiv.toMatrix_toPEquiv_mul]
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.submatrix_apply, id_eq]
  cases i with
  | inl pb =>
    obtain ⟨p, b⟩ := pb
    rw [hp]
    change basisMatrix (.inl (p, b)) j * s j =
      s (.inl (p, true)) * basisMatrix (.inl (p, if signFlip hRank a p then !b else b)) j
    by_cases ht : j = .inl (p, true)
    · subst j
      simp [basisMatrix]
    · by_cases hf : j = .inl (p, false)
      · subst j
        simp only [basisMatrix, Matrix.of_apply, Sum.inl.injEq, Prod.mk.injEq,
          Bool.false_eq_true, and_false, ite_false, ite_true, zero_add]
        by_cases he : signReal (a (axis hRank p true)) = signReal (a (axis hRank p false))
        · have he' : s (.inl (p, false)) = s (.inl (p, true)) :=
            congrArg (fun x : ℝ => (x : ℂ)) he.symm
          simp [signFlip, he, he', mul_comm]
        · have he' : s (.inl (p, false)) = -s (.inl (p, true)) := by
            change (signReal (a (axis hRank p false)) : ℂ) =
              -(signReal (a (axis hRank p true)) : ℂ)
            rw [signs_opposite he, Complex.ofReal_neg]
          cases b <;> simp [signFlip, he, he', imaginarySign, mul_comm]
      · simp [basisMatrix, ht, hf]
  | inr i =>
    rw [hi]
    change basisMatrix (.inr i) j * s j = s (.inr i) * basisMatrix (.inr i) j
    by_cases e : j = .inr i
    · subst j
      simp [basisMatrix]
    · simp [basisMatrix, e]

/-- The inducing character on a sign diagonal factors into first-axis signs to
the block thresholds and singleton signs to the original parities. -/
theorem signCharacter_eq (hRank : realRank ds = n) (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds) (fun i => signUnit (a i)) =
      (∏ p : Pair n ds, (signReal (a p.val) : ℂ) ^ (p.datum.weight.natAbs + 1)) *
        ∏ i : Singleton n ds, (signReal (a i.val) : ℂ) ^
          (RealBlockPosition.realPositionSign ds i.val).val := by
  simp only [principalSeriesCharacter, Module.finrank_self, pow_one, Real.norm_eq_abs,
    signUnit_val, abs_signReal, Complex.ofReal_one, Complex.one_cpow, mul_one]
  rw [← (placement hRank).prod_comp (fun i => realPositionCharacter ds i (signUnit (a i))),
    Fintype.prod_sum_type, Fintype.prod_prod_type]
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    have hp := RealInducedStandardBound.induced_at p.induced_at
    rw [Fintype.prod_bool]
    simp only [placement_inl, axis, ib]
    rw [show realPositionCharacter ds (p.val.val + 1) = realInducedSecondCharacter p.datum
      from hp.2.1, show realPositionCharacter ds p.val.val = realInducedFirstCharacter p.datum
      from hp.1, RealStandardNontrivial.realInducedSecondCharacter_signUnit,
      RealStandardNontrivial.realInducedFirstCharacter_signUnit, mul_one]
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [placement_inr, RealBlockPosition.realPositionCharacter_eq_charFun,
      RealJacquetFrobenius.charFun, signUnit_val, abs_signReal, div_one,
      Complex.ofReal_one, Complex.one_cpow, mul_one]

private def axisSign (ε δ : Pair n ds → Bool) (τ : Singleton n ds → Bool) :
    Rows n ds → Bool
  | .inl (p, true) => ε p
  | .inl (p, false) => if δ p then !(ε p) else ε p
  | .inr i => τ i

/-- Choose the first-axis signs, relative second-axis flips, and single-axis
signs independently. A `true` sign flag denotes `-1`. -/
def signParameters (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) (i : Fin n) : ℝˣ :=
  if axisSign ε δ τ ((placement hRank).symm i) then -1 else 1

private theorem signParameters_on_row (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) (i : Rows n ds) :
    signReal (signParameters hRank ε δ τ (placement hRank i) : ℝ) =
      if axisSign ε δ τ i then -1 else 1 := by
  simp only [signParameters, Equiv.symm_apply_apply]
  cases axisSign ε δ τ i <;> norm_num [signReal]

@[simp] theorem signFlip_signParameters (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) (p : Pair n ds) :
    signFlip hRank (fun i => (signParameters hRank ε δ τ i : ℝ)) p = δ p := by
  rw [signFlip, ← placement_inl hRank p true, ← placement_inl hRank p false,
    signParameters_on_row, signParameters_on_row]
  cases hδ : δ p <;> cases hε : ε p <;> norm_num [axisSign, hδ, hε]

theorem signGain_signParameters (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) :
    signGain (fun i => (signParameters hRank ε δ τ i : ℝ)) =
      fun
      | .inl (p, _) => if ε p then -1 else 1
      | .inr i => if τ i then -1 else 1 := by
  funext j
  cases j with
  | inl pb =>
    obtain ⟨p, b⟩ := pb
    simp only [signGain]
    rw [show p.val = placement hRank (.inl (p, true)) from rfl, signParameters_on_row, axisSign]
    cases ε p <;> simp
  | inr i =>
    simp only [signGain]
    rw [← placement_inr hRank i, signParameters_on_row, axisSign]
    cases τ i <;> simp

theorem compactMatrix_signParameters (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) (σ : Equiv.Perm (Rows n ds))
    (hp : ∀ p b, σ (.inl (p, b)) = .inl (p, if δ p then !b else b))
    (hi : ∀ i, σ (.inr i) = .inr i) :
    compactMatrix hRank (signDiagonal (fun i => (signParameters hRank ε δ τ i : ℝ))) =
      Matrix.diagonal (fun
        | .inl (p, _) => if ε p then -1 else 1
        | .inr i => if τ i then -1 else 1) * σ.permMatrix ℂ := by
  rw [compactMatrix_signDiagonal hRank _ σ (by simpa only [signFlip_signParameters]) hi,
    signGain_signParameters]

theorem signCharacter_signParameters (hRank : realRank ds = n) (ε δ : Pair n ds → Bool)
    (τ : Singleton n ds → Bool) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds)
        (fun i => signUnit (signParameters hRank ε δ τ i)) =
      (∏ p : Pair n ds, (if ε p then (-1 : ℂ) else 1) ^ (p.datum.weight.natAbs + 1)) *
        ∏ i : Singleton n ds, (if τ i then (-1 : ℂ) else 1) ^
          (RealBlockPosition.realPositionSign ds i.val).val := by
  rw [signCharacter_eq hRank]
  have h := signGain_signParameters hRank ε δ τ
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    exact congrArg (fun z : ℂ => z ^ (p.datum.weight.natAbs + 1)) (congrFun h (.inl (p, true)))
  · refine Finset.prod_congr rfl fun i _ => ?_
    exact congrArg (fun z : ℂ => z ^ (RealBlockPosition.realPositionSign ds i.val).val)
      (congrFun h (.inr i))

end Langlands.Archimedean.RealCompactBlockBasis

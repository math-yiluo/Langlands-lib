import Langlands.Global.RankinSelberg.RealParabolicSectionEquivariance
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Compact parabolic sections in the real standard module -/

noncomputable section

open Matrix
open scoped ContDiff Manifold Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.Shahidi (blockWeyl swapRank)
open Langlands.Archimedean.InductionStages

local notation "G" => fun n => Langlands.GeneralLinear n ℝ
local notation "M" => fun n => Matrix (Fin n) (Fin n) ℝ
local notation "X" => fun m n => Matrix (Fin m) (Fin n) ℝ
local notation "D" => Langlands.GeneralLinear.Iwasawa.diagonalUnits

variable {m n : ℕ}

/-- Reorder the two row blocks of the normalized parabolic section to obtain upper-Borel
covariance. The right group coordinates keep their original order. -/
def standardSection (f : G m → ℂ) (g : G n → ℂ) (φ : X m n → ℂ) (u : G (n + m)) : ℂ :=
  compactSection (-(n : ℂ) / 2) ((m : ℂ) / 2) f g φ
    (blockWeyl m n ℝ * swapRank m n ℝ u)

private theorem contMDiff_standardSection (f : G m → ℂ) (g : G n → ℂ) (φ : X m n → ℂ)
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) : ContMDiff (matrixModel ℝ (n + m)) 𝓘(ℝ, ℂ) ∞
      (standardSection f g φ) := by
  let L : M (n + m) →L[ℝ] M (m + n) :=
    (show M (n + m) →ₗ[ℝ] M (m + n) from {
      toFun := fun A => A.submatrix (finCongr (Nat.add_comm m n)) (finCongr (Nat.add_comm m n))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }).toContinuousLinearMap
  let F := compactSection (-(n : ℂ) / 2) ((m : ℂ) / 2) f g φ
  have hF : ContMDiff (matrixModel ℝ (m + n)) 𝓘(ℝ, ℂ) ∞ F :=
    (realParabolicCompactSection m n _ _ f g φ hf hg hφ hC).1
  have hval (u : G (n + m)) : (blockWeyl m n ℝ).val * L u.val =
      (blockWeyl m n ℝ * swapRank m n ℝ u).val := rfl
  refine contMDiff_of_contDiffOn (ψ := fun A =>
    unitsExtension F ((blockWeyl m n ℝ).val * L A)) ?_ ?_
  · apply (contDiffOn_unitsExtension hF).comp
      (contDiff_const.mul L.contDiff).contDiffOn
    rintro _ ⟨u, rfl⟩
    change IsUnit ((blockWeyl m n ℝ).val * L u.val)
    rw [hval]
    exact Units.isUnit _
  · intro u
    rw [hval, unitsExtension_val]
    rfl

private theorem detWeight_eq_cpow {r : ℕ} (z : ℂ) (a : G r) :
    detWeight z a.val = ((|a.val.det| : ℝ) : ℂ) ^ z := by
  have h : 0 < |a.val.det| := abs_pos.mpr (determinant a).ne_zero
  rw [detWeight, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr h.ne'),
    Complex.ofReal_log h.le, mul_comm]

private theorem detWeight_diagonal_mul_unipotent {r : ℕ} (z : ℂ) (t : Fin r → ℝˣ)
    (u : upperUnipotent r ℝ) :
    detWeight z (D t * u.val).val = ∏ i, ((|(t i : ℝ)| : ℝ) : ℂ) ^ z := by
  rw [detWeight_eq_cpow, Units.val_mul, Matrix.det_mul,
    MaximalParabolicIntegration.det_upperUnipotent u, mul_one, Iwasawa.diagonalUnits_val,
    Matrix.det_diagonal, Finset.abs_prod]
  exact cpow_prod_ofReal _ _ (fun _ => abs_nonneg _) _

private theorem detWeight_orthogonal {r : ℕ} {a : G r} (ha : a ∈ unitaryCompact ℝ r) (z : ℂ) :
    detWeight z a.val = 1 := by
  have h := Unitary.star_mul_self_of_mem (Matrix.det_of_mem_unitary ha)
  rw [star_trivial] at h
  rw [detWeight_eq_cpow]
  rcases mul_self_eq_one_iff.mp h with h' | h' <;> simp [h']

private def unipotentBlock {N r : ℕ} (u : upperUnipotent N ℝ) (e : Fin r → Fin N)
    (he : StrictMono e) : upperUnipotent r ℝ := by
  let A : M r := u.val.val.submatrix e e
  have htri : A.IsUpperTriangular := fun i j hji => u.2.1 (he hji)
  have hdiag : ∀ i, A i i = 1 := fun i => u.2.2 (e i)
  have hdet : A.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  have ha : IsUnit A := (Matrix.isUnit_iff_isUnit_det _).mpr (hdet ▸ isUnit_one)
  refine ⟨ha.unit, ?_⟩
  change ha.unit.val.IsUpperTriangular ∧ ∀ i, ha.unit.val i i = 1
  rw [ha.unit_spec]
  exact ⟨htri, hdiag⟩

private theorem unipotentBlock_entry {N r : ℕ} (u : upperUnipotent N ℝ) (e : Fin r → Fin N)
    (he : StrictMono e) (i j : Fin r) :
    (unipotentBlock u e he).val i j = u.val (e i) (e j) := by
  simp only [unipotentBlock, IsUnit.unit_spec]
  rfl

private abbrev first (i : Fin n) : Fin (n + m) := i.castAdd m
private abbrev second (i : Fin m) : Fin (n + m) := i.natAdd n

private theorem first_mono : StrictMono (first (n := n) (m := m)) := fun _ _ h => h
private theorem second_mono : StrictMono (second (n := n) (m := m)) :=
  fun _ _ h => Nat.add_lt_add_left h n

private abbrev firstUnipotent (u : upperUnipotent (n + m) ℝ) : upperUnipotent n ℝ :=
  unipotentBlock u first first_mono

private abbrev secondUnipotent (u : upperUnipotent (n + m) ℝ) : upperUnipotent m ℝ :=
  unipotentBlock u second second_mono

private abbrev shuffleConjugate (u : G (n + m)) : G (m + n) :=
  blockWeyl m n ℝ * swapRank m n ℝ u * (blockWeyl m n ℝ)⁻¹

private theorem shuffleConjugate_entry (u : G (n + m)) (i j : Fin (m + n)) :
    shuffleConjugate u i j =
      u (Fin.cast (Nat.add_comm m n) ((Langlands.Shahidi.blockWeylPermutation m n).symm i))
        (Fin.cast (Nat.add_comm m n) ((Langlands.Shahidi.blockWeylPermutation m n).symm j)) := by
  rw [shuffleConjugate, blockWeyl, GeneralLinear.permutation_conjugate_entry]
  rfl

private theorem diagonal_mul_entry {r : ℕ} (t : Fin r → ℝˣ) (u : G r) (i j : Fin r) :
    (D t * u) i j = (t i : ℝ) * u i j := by
  change ((Matrix.diagonal fun i => (t i : ℝ)) * u.val) i j = _
  exact Matrix.diagonal_mul _ _ _ _

private theorem split_shuffleConjugate_borel (t : Fin (n + m) → ℝˣ)
    (u : upperUnipotent (n + m) ℝ) :
    ∃ C : X n m, split (shuffleConjugate (D t * u.val)).val =
      Matrix.fromBlocks (D (t ∘ second) * (secondUnipotent u).val).val 0 C
        (D (t ∘ first) * (firstUnipotent u).val).val := by
  refine ⟨fun i j => (D t * u.val) (first i) (second j), ?_⟩
  ext i j
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      change shuffleConjugate (D t * u.val) (i.castAdd n) (j.castAdd n) =
        (D (t ∘ second) * (secondUnipotent u).val) i j
      simp [shuffleConjugate_entry, diagonal_mul_entry, unipotentBlock_entry]
    | inr j =>
      change shuffleConjugate (D t * u.val) (i.castAdd n) (j.natAdd m) = 0
      have hij : first (m := m) j < second (n := n) i := by
        change (j : ℕ) < n + (i : ℕ)
        omega
      have hz : u.val.val (i.natAdd n) (j.castAdd m) = 0 := u.2.1 hij
      simp [shuffleConjugate_entry, diagonal_mul_entry, hz]
  | inr i =>
    cases j with
    | inl j =>
      change shuffleConjugate (D t * u.val) (i.natAdd m) (j.castAdd n) = _
      simp [shuffleConjugate_entry]
    | inr j =>
      change shuffleConjugate (D t * u.val) (i.natAdd m) (j.natAdd m) =
        (D (t ∘ first) * (firstUnipotent u).val) i j
      simp [shuffleConjugate_entry, diagonal_mul_entry, unipotentBlock_entry]

private theorem principalSeriesCharacter_add_rank {d₁ d₂ : List RealBlock}
    (hn : realRank d₂ = n) (t : Fin (n + m) → ℝˣ) :
    principalSeriesCharacter ℝ (n + m) (realPositionCharacter (d₂ ++ d₁)) t =
      (∏ i : Fin m, ((|(t (second i) : ℝ)| : ℝ) : ℂ) ^ (-(n : ℂ) / 2)) *
      (∏ j : Fin n, ((|(t (first j) : ℝ)| : ℝ) : ℂ) ^ ((m : ℂ) / 2)) *
      (principalSeriesCharacter ℝ m (realPositionCharacter d₁) (t ∘ second) *
        principalSeriesCharacter ℝ n (realPositionCharacter d₂) (t ∘ first)) := by
  unfold principalSeriesCharacter
  rw [Fin.prod_univ_add, mul_mul_mul_comm]
  have hleft : (∏ i : Fin n, realPositionCharacter (d₂ ++ d₁) i
        (t (first i)) * ((|(t (first i) : ℝ)| : ℝ) : ℂ) ^
          ((((n + m : ℕ) : ℂ) - 1) / 2 - (i : ℕ))) =
      (∏ j : Fin n, ((|(t (first j) : ℝ)| : ℝ) : ℂ) ^ ((m : ℂ) / 2)) *
      ∏ j : Fin n, realPositionCharacter d₂ j (t (first j)) *
        ((|(t (first j) : ℝ)| : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - (j : ℕ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [realPositionCharacter_append_right _ _ _ (by simp [hn]),
      mul_left_comm, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr
        (abs_ne_zero.mpr (t (first j)).ne_zero))]
    congr 2
    push_cast
    ring
  have hright : (∏ i : Fin m, realPositionCharacter (d₂ ++ d₁) (n + (i : ℕ))
        (t (second i)) * ((|(t (second i) : ℝ)| : ℝ) : ℂ) ^
          ((((n + m : ℕ) : ℂ) - 1) / 2 - ((n + (i : ℕ) : ℕ) : ℂ))) =
      (∏ j : Fin m, ((|(t (second j) : ℝ)| : ℝ) : ℂ) ^ (-(n : ℂ) / 2)) *
      ∏ j : Fin m, realPositionCharacter d₁ j (t (second j)) *
        ((|(t (second j) : ℝ)| : ℝ) : ℂ) ^ (((m : ℂ) - 1) / 2 - (j : ℕ)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have hpos : realPositionCharacter (d₂ ++ d₁) (n + (j : ℕ)) = realPositionCharacter d₁ j := by
      simpa only [hn] using realPositionCharacter_append_left d₂ d₁ j
    rw [hpos, mul_left_comm,
      ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr (t (second j)).ne_zero))]
    congr 2
    push_cast
    ring
  simp only [Real.norm_eq_abs, Module.finrank_self, pow_one, Function.comp_apply,
    Fin.val_castAdd, Fin.val_natAdd]
  change (∏ i : Fin n, realPositionCharacter (d₂ ++ d₁) i (t (first i)) * _) *
      (∏ i : Fin m, realPositionCharacter (d₂ ++ d₁) (n + (i : ℕ)) (t (second i)) * _) = _
  rw [hleft, hright, mul_comm]

private theorem split_blockSum (a : G m) (b : G n) :
    split (blockSum (a, b)).val = Matrix.fromBlocks a.val 0 0 b.val := by
  ext i j
  cases i <;> cases j <;>
    simp [split, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

private theorem first_ne_second (i : Fin n) (j : Fin m) : i.castAdd m ≠ j.natAdd n := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

private theorem blockEmb_first (b : G n) :
    blockEmb (show 0 + n ≤ n + m by omega) b = blockSum (b, (1 : G m)) := by
  apply Units.ext
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · let h : 0 + n ≤ n + m := by omega
    have hidx (l : Fin n) : idx h l = l.castAdd m := Fin.ext (zero_add _)
    rw [blockEmb_val, ← hidx i, ← hidx j, blockMat_apply_idx, hidx, hidx,
      blockSum_apply_left]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_right _ _ (by simp [IsMid]),
      blockSum_apply_left_right, Matrix.one_apply_ne (first_ne_second i j)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid]),
      blockSum_apply_right_left, Matrix.one_apply_ne ((first_ne_second j i).symm)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid]),
      blockSum_apply_right, Units.val_one]
    simp [Matrix.one_apply]

private theorem blockEmb_second (a : G m) :
    blockEmb (show n + m ≤ n + m by omega) a = blockSum ((1 : G n), a) := by
  apply Units.ext
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid, Nat.not_le_of_lt i.isLt]),
      blockSum_apply_left, Units.val_one]
    simp [Matrix.one_apply]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_left _ (by simp [IsMid, Nat.not_le_of_lt i.isLt]),
      blockSum_apply_left_right, Matrix.one_apply_ne (first_ne_second i j)]
  · rw [blockEmb_val, blockMat_apply_of_not_isMid_right _ _ (by simp [IsMid, Nat.not_le_of_lt j.isLt]),
      blockSum_apply_right_left, Matrix.one_apply_ne ((first_ne_second j i).symm)]
  · exact blockMat_apply_idx (show n + m ≤ n + m by omega) a.val i j |>.trans
      (blockSum_apply_right (1 : G n) a i j).symm

private theorem translated_shuffle (v u : G (n + m)) :
    blockWeyl m n ℝ * swapRank m n ℝ (v * u) =
      shuffleConjugate v * (blockWeyl m n ℝ * swapRank m n ℝ u) := by
  simp only [shuffleConjugate, map_mul, mul_assoc, inv_mul_cancel_left]

private theorem compactSection_leftOrthogonal {f : G m → ℂ} {g : G n → ℂ}
    {φ : X m n → ℂ} (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (z₁ z₂ : ℂ) (u : G (m + n))
    (a' : G m) (b' : G n) (ha' : a' ∈ unitaryCompact ℝ m) (hb' : b' ∈ unitaryCompact ℝ n) :
    compactSection z₁ z₂ f g φ (blockSum (a', b') * u) =
      compactSection z₁ z₂ (fun a => f (a' * a)) (fun b => g (b' * b)) φ u := by
  rw [(realParabolicSectionEquivariance m n z₁ z₂ f g φ hf hg hφ hC).2 _ _ _ _ 0
    (split_blockSum _ _), detWeight_orthogonal ha', detWeight_orthogonal hb', one_mul, one_mul]

private theorem compactSection_Fourier_first {f : G m → ℂ} {g : G n → ℂ} {φ : X m n → ℂ}
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (z₁ z₂ : ℂ) (u : G (m + n)) (p : ℕ) (k : ℤ)
    (hvanish : ∀ a, blockFourierCoefficient m p k f a = 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      compactSection z₁ z₂ f g φ (blockSum (blockRotation m p θ, (1 : G n)) * u) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) = 0 := by
  by_cases hu : u ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hY⟩ := exists_cellCoordinates u hu
    let c := detWeight z₁ a.val * detWeight z₂ b.val * g b * φ Y
    have heq (θ : ℝ) :
        compactSection z₁ z₂ f g φ (blockSum (blockRotation m p θ, (1 : G n)) * u) =
          c * f (blockRotation m p θ * a) := by
      rw [compactSection_leftOrthogonal hf hg hφ hC z₁ z₂ u
        _ _ (blockRotation_mem_unitaryCompact m p θ) (one_mem _)]
      change compactSection z₁ z₂ (fun a => f (blockRotation m p θ * a))
        (fun b => g (1 * b)) φ u = _
      rw [(realParabolicCompactSection m n z₁ z₂
        (fun v => f (blockRotation m p θ * v)) (fun v => g (1 * v))
        φ (hf.comp (contMDiff_const.mul contMDiff_id))
        (hg.comp (contMDiff_const.mul contMDiff_id)) hφ hC).2.2 _ _ _ _ _ hY, one_mul]
      dsimp only [c]
      ring
    simp only [heq]
    simp_rw [show ∀ v w : ℂ, (c * v) * w = c * (v * w) from mul_assoc c]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ (hvanish a)
  · have heq (θ : ℝ) :
        compactSection z₁ z₂ f g φ (blockSum (blockRotation m p θ, (1 : G n)) * u) = 0 := by
      rw [compactSection_leftOrthogonal hf hg hφ hC z₁ z₂ u
        _ _ (blockRotation_mem_unitaryCompact m p θ) (one_mem _)]
      simp [compactSection, hu]
    simp [heq]

private theorem compactSection_Fourier_second {f : G m → ℂ} {g : G n → ℂ} {φ : X m n → ℂ}
    (hf : ContMDiff (matrixModel ℝ m) 𝓘(ℝ, ℂ) ∞ f)
    (hg : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ g) (hφ : ContDiff ℝ ∞ φ)
    (hC : HasCompactSupport φ) (z₁ z₂ : ℂ) (u : G (m + n)) (p : ℕ) (k : ℤ)
    (hvanish : ∀ b, blockFourierCoefficient n p k g b = 0) :
    (∫ θ in (0 : ℝ)..2 * Real.pi,
      compactSection z₁ z₂ f g φ (blockSum ((1 : G m), blockRotation n p θ) * u) *
        Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) = 0 := by
  by_cases hu : u ∈ parabolicCell m n
  · obtain ⟨a, b, C, Y, hY⟩ := exists_cellCoordinates u hu
    let c := detWeight z₁ a.val * detWeight z₂ b.val * f a * φ Y
    have heq (θ : ℝ) :
        compactSection z₁ z₂ f g φ (blockSum ((1 : G m), blockRotation n p θ) * u) =
          c * g (blockRotation n p θ * b) := by
      rw [compactSection_leftOrthogonal hf hg hφ hC z₁ z₂ u _ _
        (one_mem _) (blockRotation_mem_unitaryCompact n p θ)]
      change compactSection z₁ z₂ (fun a => f (1 * a))
        (fun b => g (blockRotation n p θ * b)) φ u = _
      rw [(realParabolicCompactSection m n z₁ z₂
        (fun v => f (1 * v)) (fun v => g (blockRotation n p θ * v))
        φ (hf.comp (contMDiff_const.mul contMDiff_id))
        (hg.comp (contMDiff_const.mul contMDiff_id)) hφ hC).2.2 _ _ _ _ _ hY, one_mul]
      dsimp only [c]
      ring
    simp only [heq]
    simp_rw [show ∀ v w : ℂ, (c * v) * w = c * (v * w) from mul_assoc c]
    rw [intervalIntegral.integral_const_mul]
    exact mul_eq_zero_of_right _ (hvanish b)
  · have heq (θ : ℝ) :
        compactSection z₁ z₂ f g φ (blockSum ((1 : G m), blockRotation n p θ) * u) = 0 := by
      rw [compactSection_leftOrthogonal hf hg hφ hC z₁ z₂ u _ _
        (one_mem _) (blockRotation_mem_unitaryCompact n p θ)]
      simp [compactSection, hu]
    simp [heq]

/-- Normalized compact parabolic sections of two real standard functions lie in the exact
standard module for the concatenation in upper-Borel order. -/
def RealParabolicStandardSectionStatement : Prop :=
  ∀ (m n : ℕ) (d₁ d₂ : List RealBlock), realRank d₁ = m → realRank d₂ = n →
    ∀ (f : G m → ℂ) (g : G n → ℂ),
    f ∈ realStandardModule m d₁ → g ∈ realStandardModule n d₂ →
    ∀ φ : X m n → ℂ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      standardSection f g φ ∈ realStandardModule (n + m) (d₂ ++ d₁)

theorem realParabolicStandardSection : RealParabolicStandardSectionStatement := by
  intro m n d₁ d₂ hm hn f g hf hg φ hφ hC
  let leftLaw := (realParabolicSectionEquivariance m n (-(n : ℂ) / 2) ((m : ℂ) / 2)
    f g φ hf.1.1 hg.1.1 hφ hC).2
  refine ⟨⟨contMDiff_standardSection f g φ hf.1.1 hg.1.1 hφ hC, ?_⟩, ?_⟩
  · intro t u x
    obtain ⟨C, hC'⟩ := split_shuffleConjugate_borel t u
    have hf' : (fun a => f (D (t ∘ second) * (secondUnipotent u).val * a)) =
        principalSeriesCharacter ℝ m (realPositionCharacter d₁) (t ∘ second) • f :=
      funext fun a => hf.1.2 _ _ a
    have hg' : (fun b => g (D (t ∘ first) * (firstUnipotent u).val * b)) =
        principalSeriesCharacter ℝ n (realPositionCharacter d₂) (t ∘ first) • g :=
      funext fun b => hg.1.2 _ _ b
    unfold standardSection
    rw [translated_shuffle, leftLaw _ _ _ _ C hC', hf', hg',
      detWeight_diagonal_mul_unipotent, detWeight_diagonal_mul_unipotent,
      principalSeriesCharacter_add_rank hn]
    let y := blockWeyl m n ℝ * swapRank m n ℝ x
    by_cases hy : y ∈ parabolicCell m n
    · obtain ⟨a, b, C₀, Y, hY⟩ := exists_cellCoordinates y hy
      have hF := (realParabolicCompactSection m n (-(n : ℂ) / 2) ((m : ℂ) / 2)
        f g φ hf.1.1 hg.1.1 hφ hC).2.2
      have hF' := (realParabolicCompactSection m n (-(n : ℂ) / 2) ((m : ℂ) / 2) _ _ φ
        ((principalSeries ℝ m (realPositionCharacter d₁)).smul_mem
          (principalSeriesCharacter ℝ m (realPositionCharacter d₁) (t ∘ second)) hf.1).1
        ((principalSeries ℝ n (realPositionCharacter d₂)).smul_mem
          (principalSeriesCharacter ℝ n (realPositionCharacter d₂) (t ∘ first)) hg.1).1
        hφ hC).2.2
      rw [hF' y a b C₀ Y hY, hF y a b C₀ Y hY]
      simp only [Pi.smul_apply, smul_eq_mul, Function.comp_apply]
      ring
    · simp [compactSection, ← show y = blockWeyl m n ℝ * swapRank m n ℝ x from rfl, hy]
  · intro p d hd k hk x
    rcases realInducedBlockAt_append_cases d₂ d₁ p d hd with ⟨hp, hblock⟩ | ⟨hp, hblock⟩
    · rw [hn] at hp
      have hr (θ : ℝ) : blockRotation (n + m) p θ = blockSum (blockRotation n p θ, (1 : G m)) := by
        rw [← blockEmb_first, blockEmb_blockRotation _ hp, zero_add]
      unfold blockFourierCoefficient standardSection
      simp_rw [translated_shuffle, hr, Langlands.Shahidi.blockWeyl_conjugate_blockSum]
      exact compactSection_Fourier_second hf.1.1 hg.1.1 hφ hC _ _ _ p k (hg.2 p d hblock k hk)
    · rw [hn] at hp hblock
      have hp₁ : p - n + 1 < m := by simpa [← hm] using realInducedBlockAt_lt hblock
      have hr (θ : ℝ) :
          blockRotation (n + m) p θ = blockSum ((1 : G n), blockRotation m (p - n) θ) := by
        rw [← blockEmb_second, blockEmb_blockRotation _ hp₁, Nat.add_sub_of_le hp]
      unfold blockFourierCoefficient standardSection
      simp_rw [translated_shuffle, hr, Langlands.Shahidi.blockWeyl_conjugate_blockSum]
      exact compactSection_Fourier_first hf.1.1 hg.1.1 hφ hC _ _ _ _ k (hf.2 _ d hblock k hk)

end Langlands.Global.RankinSelbergGlobal.RealParabolicCompactSection

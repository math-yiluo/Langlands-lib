import Langlands.Representation.Archimedean.JacquetMinorNonvanishing
import Langlands.Representation.Archimedean.RealTemperedCommutantReduction
import Langlands.Representation.Archimedean.RealStrictCharacterLanglandsQuotient

/-!
# The scalar step for the minor vector of a real standard module without discrete series
-/

noncomputable section

open Matrix Finset

open Langlands.LocalFactor.Archimedean Langlands.GeneralLinear

open scoped TensorProduct

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

namespace RealTiedMinorScalar

open MatrixMinor JacquetMinor GramFormula PrincipalSeriesExtension
  RealTemperedCommutantReduction RealStrictCharacterLanglandsQuotient

/-- Every real induction block of `ds` has weight `0`: `ds` has no discrete-series block. -/
def IsPrincipal (ds : List RealBlock) : Prop :=
  ∀ (p : ℕ) (d : ComplexCharacterData), realInducedBlockAt ds p = some d → d.weight = 0

theorem realStandardModule_eq {n : ℕ} {ds : List RealBlock} (h : IsPrincipal ds) :
    realStandardModule n ds = principalSeries ℝ n (realPositionCharacter ds) := by
  ext f
  constructor
  · exact fun hf => hf.1
  · intro hf
    refine ⟨hf, fun p d hd k hk => ?_⟩
    rw [h p d hd, abs_zero] at hk
    exact absurd hk (not_lt.mpr (abs_nonneg k))

variable (n : ℕ) (ds : List RealBlock)

/-- The positions `l < n` whose character is odd. -/
def signSet : Finset (Fin n) :=
  univ.filter fun l : Fin n => realPositionCharacter ds l (-1) = -1

theorem sign_eq (l : Fin n) :
    realPositionCharacter ds l (-1) = if l ∈ signSet n ds then -1 else 1 := by
  simp only [signSet, mem_filter, mem_univ, true_and]
  rcases realPositionCharacter_neg_one ds l with h | h
  · rw [h]
    norm_num
  · simp [h]

variable {n ds}

/-- The minor vector `φ_{A,B}` (`A` the sign set) as an element of `KF n ds`, and `0` if
`|B| ≠ |A|`. -/
def vec (hds : IsPrincipal ds) (B : Finset (Fin n)) : KF n ds :=
  if hB : B.card = (signSet n ds).card then
    ⟨minorVector n (realPositionExponent ds) (signSet n ds) B, by
      have hmem := minorVector_mem (isSignedPower ds) (sign_eq n ds) hB
      refine ⟨?_, hmem.2⟩
      rw [realStandardModule_eq hds]
      exact hmem.1⟩
  else 0

theorem vec_coe (hds : IsPrincipal ds) {B : Finset (Fin n)} (hB : B.card = (signSet n ds).card) :
    ((vec hds B : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) =
      minorVector n (realPositionExponent ds) (signSet n ds) B := by
  rw [vec, dite_eq_left_of_eq_true (eq_true hB)]

/-- The lowest `O(n)`-type vector `φ_{A,A}` of `KF n ds`. -/
def minorElem (hds : IsPrincipal ds) : KF n ds := vec hds (signSet n ds)

/-- Right translation of `φ_{A,B}` by `k ∈ O(n)` (Cauchy–Binet). -/
theorem rep_vec (hds : IsPrincipal ds) {B : Finset (Fin n)} (hB : B.card = (signSet n ds).card)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realStandardRep n ds k (vec hds B) =
      ∑ C ∈ powersetCard (signSet n ds).card univ,
        ((minor (k : Matrix (Fin n) (Fin n) ℝ) C B : ℝ) : ℂ) • vec hds C := by
  apply Subtype.ext
  funext g
  rw [realStandardRep_apply_coe, Submodule.coe_sum, Finset.sum_apply]
  change ((vec hds B : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (g * Unitary.toUnits k) = _
  rw [vec_coe hds hB,
    minorVector_mul (isSignedPower ds) (sign_eq n ds) hB g (k₀ := Unitary.toUnits k) k.2]
  refine Finset.sum_congr rfl fun C hC => ?_
  rw [Submodule.coe_smul, Pi.smul_apply, vec_coe hds (mem_powersetCard.mp hC).2, smul_eq_mul]
  rfl

/-- The diagonal sign matrix with `-1` at `j` and `1` elsewhere, in `O(n)`. -/
def flip (j : Fin n) : Matrix.unitaryGroup (Fin n) ℝ :=
  ⟨Matrix.diagonal fun i => if i = j then -1 else 1, by
    rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, star_trivial]
    split_ifs <;> norm_num⟩

/-- The sign units `-1` at `j` and `1` elsewhere. -/
def flipUnits (j : Fin n) : Fin n → ℝˣ := fun i => if i = j then -1 else 1

theorem toUnits_flip (j : Fin n) :
    Unitary.toUnits (flip j) =
      (Iwasawa.diagonalUnits (flipUnits j) : Langlands.GeneralLinear n ℝ) := by
  apply Units.ext
  change (Matrix.diagonal fun i => if i = j then (-1 : ℝ) else 1) = _
  rw [Iwasawa.diagonalUnits_val]
  congr 1
  funext i
  unfold flipUnits
  split_ifs <;> simp

theorem principalSeriesCharacter_flip (j : Fin n) :
    principalSeriesCharacter ℝ n (realPositionCharacter ds) (flipUnits j) =
      if j ∈ signSet n ds then -1 else 1 := by
  rw [principalSeriesCharacter, Fintype.prod_eq_single j]
  · rw [show flipUnits j j = -1 by simp [flipUnits]]
    rw [← sign_eq n ds j]
    simp
  · intro i hi
    rw [show flipUnits j i = 1 by simp [flipUnits, hi]]
    simp [realPositionCharacter_one]

/-- Evaluation at `1` transforms under `flip j` by the sign of the `j`-th character. -/
theorem eval_rep_flip (hds : IsPrincipal ds) (j : Fin n) (v : KF n ds) :
    kFiniteEval (realStandardModule n ds) 1 (realStandardRep n ds (flip j) v) =
      (if j ∈ signSet n ds then -1 else 1) * kFiniteEval (realStandardModule n ds) 1 v := by
  rw [kFiniteEval_apply, kFiniteEval_apply, realStandardRep_apply_coe]
  change (v : Langlands.GeneralLinear n ℝ → ℂ) (1 * Unitary.toUnits (flip j)) = _
  have hv : (v : Langlands.GeneralLinear n ℝ → ℂ) ∈ principalSeries ℝ n (realPositionCharacter ds) := by
    rw [← realStandardModule_eq hds]
    exact v.2.1
  have h := hv.2 (flipUnits j) 1 1
  rw [one_mul, toUnits_flip]
  simp only [OneMemClass.coe_one, mul_one] at h
  rw [h, principalSeriesCharacter_flip]

/-- `flip j` acts on `φ_{A,C}` by `-1` if `j ∈ C` and by `1` otherwise. -/
theorem rep_flip_vec (hds : IsPrincipal ds) (j : Fin n) {C : Finset (Fin n)}
    (hC : C.card = (signSet n ds).card) :
    realStandardRep n ds (flip j) (vec hds C) = (if j ∈ C then -1 else 1 : ℂ) • vec hds C := by
  apply Subtype.ext
  funext g
  rw [realStandardRep_apply_coe, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
  change ((vec hds C : KF n ds) : Langlands.GeneralLinear n ℝ → ℂ) (g * Unitary.toUnits (flip j)) = _
  rw [vec_coe hds hC, minorVector_mul (isSignedPower ds) (sign_eq n ds) hC g
    (k₀ := Unitary.toUnits (flip j)) (flip j).2]
  rw [Finset.sum_eq_single C]
  · change (((minor (Matrix.diagonal fun i => if i = j then (-1 : ℝ) else 1) C C : ℝ) : ℂ)) * _ = _
    rw [minor_diagonal, ite_eq_left_of_eq_true _ _ (eq_self C), Finset.prod_ite_eq']
    split_ifs <;> simp
  · intro D _ hD
    change (((minor (Matrix.diagonal fun i => if i = j then (-1 : ℝ) else 1) D C : ℝ) : ℂ)) * _ = 0
    rw [minor_diagonal, ite_eq_right_of_eq_false _ _ (eq_false hD)]
    simp
  · intro hC'
    exact absurd (mem_powersetCard.mpr ⟨subset_univ _, hC⟩) hC'

/-- **The multiplicity-one computation.** A functional transforming under the sign matrices
like evaluation at `1` sees the right translates of `φ_{A,B}` only through `det k_{A,B}`. -/
theorem functional_rep_vec (hds : IsPrincipal ds) (ψ : KF n ds →ₗ[ℂ] ℂ)
    (hψ : ∀ (j : Fin n) (v : KF n ds),
      ψ (realStandardRep n ds (flip j) v) = (if j ∈ signSet n ds then -1 else 1) * ψ v)
    {B : Finset (Fin n)} (hB : B.card = (signSet n ds).card)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    ψ (realStandardRep n ds k (vec hds B)) =
      ((minor (k : Matrix (Fin n) (Fin n) ℝ) (signSet n ds) B : ℝ) : ℂ) *
        ψ (minorElem hds) := by
  rw [rep_vec hds hB, map_sum, Finset.sum_eq_single (signSet n ds)]
  · rw [map_smul, smul_eq_mul]
    rfl
  · intro C hC hCA
    have hCcard := (mem_powersetCard.mp hC).2
    obtain ⟨j, hjC, hjA⟩ : ∃ j ∈ C, j ∉ signSet n ds := by
      by_contra hcon
      push Not at hcon
      exact hCA (Finset.eq_of_subset_of_card_le hcon hCcard.ge)
    have h1 := hψ j (vec hds C)
    rw [rep_flip_vec hds j hCcard, map_smul, smul_eq_mul] at h1
    simp only [hjC, hjA, ↓reduceIte, one_mul] at h1
    have h0 : ψ (vec hds C) = 0 := by
      have : (2 : ℂ) * ψ (vec hds C) = 0 := by linear_combination -h1
      simpa using this
    rw [map_smul, h0, smul_zero]
  · intro h
    exact absurd (mem_powersetCard.mpr ⟨subset_univ _, rfl⟩) h

/-- **The scalar step.** An endomorphism commuting with `O(n)` multiplies every minor vector
`φ_{A,B}` by one and the same scalar. -/
theorem exists_forall_vec_eq_smul (hds : IsPrincipal ds) (E : KF n ds →ₗ[ℂ] KF n ds)
    (hE : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (v : KF n ds),
      E (realStandardRep n ds k v) = realStandardRep n ds k (E v)) :
    ∃ c : ℂ, ∀ B : Finset (Fin n), B.card = (signSet n ds).card →
      E (vec hds B) = c • vec hds B := by
  let ev := kFiniteEval (realStandardModule n ds) 1
  have hev : ∀ (j : Fin n) (v : KF n ds),
      ev (realStandardRep n ds (flip j) v) = (if j ∈ signSet n ds then -1 else 1) * ev v :=
    eval_rep_flip hds
  have hevE : ∀ (j : Fin n) (v : KF n ds),
      (ev ∘ₗ E) (realStandardRep n ds (flip j) v) =
        (if j ∈ signSet n ds then -1 else 1) * (ev ∘ₗ E) v := by
    intro j v
    rw [LinearMap.comp_apply, hE, hev]
    rfl
  have hf₁ : ev (minorElem hds) = 1 := by
    change kFiniteEval (realStandardModule n ds) 1 (minorElem hds) = 1
    rw [kFiniteEval_apply, minorElem, vec_coe hds rfl, minorVector_of_mem (one_mem _)]
    simp [minor_one]
  refine ⟨(ev ∘ₗ E) (minorElem hds), fun B hB => ?_⟩
  rw [← sub_eq_zero]
  apply eq_zero_of_compact_eval n ds
  intro k
  have h1 := functional_rep_vec hds (ev ∘ₗ E) hevE hB k
  have h2 := functional_rep_vec hds ev hev hB k
  rw [LinearMap.comp_apply, hE] at h1
  change ev (realStandardRep n ds k (E (vec hds B) - (ev ∘ₗ E) (minorElem hds) • vec hds B))
    = 0
  rw [map_sub, map_sub, map_smul, map_smul, h1, h2, hf₁, smul_eq_mul]
  ring

/-- **Reduction.** If every subspace of `KF n ds` that is stable under `O(n)` and the Lie
algebra and contains all minor vectors `φ_{A,B}` is everything, then the simultaneous commutant
is scalar. -/
theorem hasScalarCommutant_of_cyclic (hds : IsPrincipal ds)
    (hcyc : ∀ W : Submodule ℂ (KF n ds),
      (∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ v ∈ W, realStandardRep n ds k v ∈ W) →
      (∀ Z : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ, ∀ v ∈ W, realStandardLie n ds Z v ∈ W) →
      (∀ B : Finset (Fin n), B.card = (signSet n ds).card → vec hds B ∈ W) → W = ⊤) :
    HasScalarCommutant n ds := by
  intro E hEK hEL
  obtain ⟨c, hc⟩ := exists_forall_vec_eq_smul hds E hEK
  set W := LinearMap.ker (E - c • LinearMap.id)
  have hW : W = ⊤ := by
    refine hcyc W (fun k v hv => ?_) (fun Z v hv => ?_) fun B hB => ?_
    · rw [LinearMap.mem_ker] at hv ⊢
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
      rw [hEK, sub_eq_zero.mp hv, map_smul, sub_self]
    · rw [LinearMap.mem_ker] at hv ⊢
      rw [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hv ⊢
      rw [hEL, sub_eq_zero.mp hv, map_smul, sub_self]
    · rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
        hc B hB, sub_self]
  refine ⟨c, fun v => ?_⟩
  have hv : v ∈ W := hW ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero] at hv
  exact hv

end RealTiedMinorScalar

end Langlands.Archimedean

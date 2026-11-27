import Langlands.Global.Factors.CuspidalPairEisensteinOpenCellExhaustion
import Langlands.Global.CompletionResidue
import Langlands.Global.Factors.HeckeEulerProduct

/-! # Local sums of the open-cell majorant

At a finite place `v` with residue cardinality `q = N(v)`, let `‖y‖` be the maximum of the
norms of the entries of `y ∈ M_(a×b)(F_v)`. The function `max(1, ‖y‖)` is constant on the
classes of `M_(a×b)(F_v) / M_(a×b)(𝒪_v)`, and for `β ≥ 0` with `q^(a b - β) ≤ 1/2`
`∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β) ≤ 1 + 2 q^(a b - β)`.
See the paired Markdown. -/

noncomputable section

set_option autoImplicit false

universe u

open NumberField IsDedekindDomain
open scoped NNReal ENNReal Valued

namespace Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)

section Norm

open HeightOneSpectrum Valuation.IsRankOneDiscrete WithZero in
theorem one_lt_absNorm : (1 : ℝ) < Ideal.absNorm v.asIdeal := by
  exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm v

theorem absNorm_pos : (0 : ℝ) < Ideal.absNorm v.asIdeal :=
  zero_lt_one.trans (one_lt_absNorm v)

/-- A norm value below `N(v)` is at most one. -/
theorem norm_le_one_of_lt_absNorm {x : FiniteCompletion F v}
    (h : ‖x‖ < Ideal.absNorm v.asIdeal) : ‖x‖ ≤ 1 := by
  by_contra h'
  exact absurd (Langlands.Global.AdelicMatrixHeight.absNorm_le_norm_of_one_lt F v (lt_of_not_ge h')) (not_le.mpr h)

/-- A uniformizer of `F_v`, of norm `N(v)⁻¹`. -/
def uniformizer : FiniteCompletion F v :=
  ((LocalFactor.PadicAbelian.uniformizerUnit (CompletionPadic.topologicalData v) :
    (FiniteCompletion F v)ˣ) : FiniteCompletion F v)

theorem norm_uniformizer : ‖uniformizer v‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ :=
  HeckeEulerProduct.norm_uniformizerUnit v

theorem uniformizer_ne_zero : uniformizer v ≠ 0 := Units.ne_zero _

end Norm

section Matrix

variable {v} {a b : ℕ}

/-- The maximum of the norms of the entries of a matrix over `F_v`. -/
def entryNorm (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) : ℝ :=
  ‖(Matrix.of.symm y : Fin a → Fin b → FiniteCompletion F v)‖

theorem entryNorm_nonneg (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    0 ≤ entryNorm y :=
  norm_nonneg _

theorem norm_entry_le_entryNorm (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v))
    (i : Fin a) (j : Fin b) : ‖y i j‖ ≤ entryNorm y :=
  (norm_le_pi_norm (Matrix.of.symm y i) j).trans (norm_le_pi_norm (Matrix.of.symm y) i)

theorem entryNorm_le_iff {y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)} {C : ℝ}
    (hC : 0 ≤ C) : entryNorm y ≤ C ↔ ∀ i j, ‖y i j‖ ≤ C := by
  unfold entryNorm
  rw [pi_norm_le_iff_of_nonneg hC]
  exact forall_congr' fun i => pi_norm_le_iff_of_nonneg hC

theorem entryNorm_smul (c : FiniteCompletion F v)
    (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    entryNorm (c • y) = ‖c‖ * entryNorm y :=
  norm_smul c (Matrix.of.symm y : Fin a → Fin b → FiniteCompletion F v)

theorem entryNorm_neg (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    entryNorm (-y) = entryNorm y :=
  norm_neg (Matrix.of.symm y : Fin a → Fin b → FiniteCompletion F v)

/-- An entry norm above one is at least `N(v)`. -/
theorem absNorm_le_entryNorm_of_one_lt {y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)}
    (h : 1 < entryNorm y) : (Ideal.absNorm v.asIdeal : ℝ) ≤ entryNorm y := by
  by_contra hlt
  push Not at hlt
  have hle : entryNorm y ≤ 1 := (entryNorm_le_iff zero_le_one).2 fun i j =>
    norm_le_one_of_lt_absNorm v ((norm_entry_le_entryNorm y i j).trans_lt hlt)
  linarith

/-- Adding a matrix with integral entries does not change `max(1, ‖y‖)`. -/
theorem max_one_entryNorm_add (y o : Matrix (Fin a) (Fin b) (FiniteCompletion F v))
    (ho : entryNorm o ≤ 1) : max 1 (entryNorm (y + o)) = max 1 (entryNorm y) := by
  have key : ∀ y o : Matrix (Fin a) (Fin b) (FiniteCompletion F v), entryNorm o ≤ 1 →
      max 1 (entryNorm (y + o)) ≤ max 1 (entryNorm y) := by
    intro y o ho
    refine max_le (le_max_left _ _) ?_
    refine (entryNorm_le_iff (zero_le_one.trans (le_max_left _ _))).2 fun i j => ?_
    refine (IsUltrametricDist.norm_add_le_max (y i j) (o i j)).trans (max_le ?_ ?_)
    · exact (norm_entry_le_entryNorm y i j).trans (le_max_right _ _)
    · exact ((norm_entry_le_entryNorm o i j).trans ho).trans (le_max_left _ _)
  refine le_antisymm (key y o ho) ?_
  have h := key (y + o) (-o) (by rwa [entryNorm_neg])
  rwa [add_neg_cancel_right] at h

end Matrix

section Quotient

open scoped Classical

variable {a b : ℕ}

/-- The lattice `M_(a×b)(𝒪_v)`. -/
abbrev integralLattice : AddSubgroup (Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :=
  Shahidi.integralMatrices (CompletionPadic.padicField v) a b

/-- The quotient `M_(a×b)(F_v) / M_(a×b)(𝒪_v)`. -/
abbrev MatrixQuotient (a b : ℕ) :=
  Matrix (Fin a) (Fin b) (CompletionPadic.padicField v).Carrier ⧸
    Shahidi.integralMatrices (CompletionPadic.padicField v) a b

variable {v}

theorem mem_integralLattice_iff (y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    y ∈ integralLattice v ↔ entryNorm y ≤ 1 := by
  rw [entryNorm_le_iff zero_le_one]
  constructor
  · intro h i j
    have hm : y i j ∈ v.adicCompletionIntegers F :=
      (OpenCellExhaustion.mem_adicCompletionIntegers_iff_canonical v _).2
        (h i (Set.mem_univ _) j (Set.mem_univ _))
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at hm
    exact Valued.toNormedField.norm_le_one_iff.2 hm
  · intro h i _ j _
    refine (OpenCellExhaustion.mem_adicCompletionIntegers_iff_canonical v _).1 ?_
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    exact Valued.toNormedField.norm_le_one_iff.1 (h i j)

variable (v) in
/-- `max(1, ‖y‖)` at the chosen representative of a class. -/
def classHeight (y : MatrixQuotient v a b) : ℝ :=
  max 1 (entryNorm (Quotient.out y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)))

theorem one_le_classHeight (y : MatrixQuotient v a b) : 1 ≤ classHeight v y :=
  le_max_left _ _

/-- `classHeight` does not depend on the representative. -/
theorem classHeight_mk (z : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    classHeight v (QuotientAddGroup.mk z : MatrixQuotient v a b) = max 1 (entryNorm z) := by
  set y : MatrixQuotient v a b := QuotientAddGroup.mk z
  have h : (QuotientAddGroup.mk (Quotient.out y) : MatrixQuotient v a b) = y := Quotient.out_eq _
  have hmem := QuotientAddGroup.eq.mp h
  have hz : z = (Quotient.out y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) +
      (-Quotient.out y + z) := by abel
  rw [classHeight, hz, max_one_entryNorm_add _ _ ((mem_integralLattice_iff _).1 hmem)]

theorem eq_zero_of_classHeight_le_one {y : MatrixQuotient v a b} (h : classHeight v y ≤ 1) :
    y = 0 := by
  have hmem : (Quotient.out y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) ∈
      integralLattice v :=
    (mem_integralLattice_iff _).2 ((le_max_right _ _).trans h)
  rw [← Quotient.out_eq y]
  exact (QuotientAddGroup.eq_zero_iff _).2 hmem

/-- A nonzero class has `classHeight` equal to the entry norm of its representative, and at
least `N(v)`. -/
theorem classHeight_of_ne_zero {y : MatrixQuotient v a b} (hy : y ≠ 0) :
    classHeight v y = entryNorm (Quotient.out y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) ∧
      (Ideal.absNorm v.asIdeal : ℝ) ≤ classHeight v y := by
  have h1 : 1 < entryNorm (Quotient.out y : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) := by
    by_contra h
    exact hy (eq_zero_of_classHeight_le_one (max_le le_rfl (le_of_not_gt h)))
  have he : classHeight v y = entryNorm (Quotient.out y :
      Matrix (Fin a) (Fin b) (FiniteCompletion F v)) := max_eq_right h1.le
  exact ⟨he, he ▸ absNorm_le_entryNorm_of_one_lt h1⟩

variable (v a b) in
/-- Multiplication by the uniformizer on `M(F_v)/M(𝒪_v)`. -/
def scaleMap : MatrixQuotient v a b →+ MatrixQuotient v a b :=
  QuotientAddGroup.map _ _
    { toFun := fun y => uniformizer v • y
      map_zero' := smul_zero _
      map_add' := smul_add _ } (by
    intro y hy
    rw [AddSubgroup.mem_comap]
    change uniformizer v • y ∈ integralLattice v
    rw [mem_integralLattice_iff, entryNorm_smul, norm_uniformizer]
    have hy' := (mem_integralLattice_iff y).1 hy
    have hq : (Ideal.absNorm v.asIdeal : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_lt_absNorm v).le
    calc (Ideal.absNorm v.asIdeal : ℝ)⁻¹ * entryNorm y ≤ 1 * 1 :=
          mul_le_mul hq hy' (entryNorm_nonneg _) zero_le_one
      _ = 1 := one_mul 1)

theorem scaleMap_mk (z : Matrix (Fin a) (Fin b) (FiniteCompletion F v)) :
    scaleMap v a b (QuotientAddGroup.mk z) = QuotientAddGroup.mk (uniformizer v • z) :=
  rfl

theorem classHeight_scaleMap {y : MatrixQuotient v a b} (hy : y ≠ 0) :
    classHeight v (scaleMap v a b y) = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ * classHeight v y := by
  obtain ⟨he, hq⟩ := classHeight_of_ne_zero hy
  have hy' : scaleMap v a b y = QuotientAddGroup.mk (uniformizer v • (Quotient.out y :
      Matrix (Fin a) (Fin b) (FiniteCompletion F v))) := by
    rw [← scaleMap_mk, QuotientAddGroup.out_eq']
  rw [hy', classHeight_mk, entryNorm_smul, norm_uniformizer, ← he]
  apply max_eq_right
  rw [← div_eq_inv_mul, le_div_iff₀ (absNorm_pos v), one_mul]
  exact hq

/-- A section of `scaleMap`: multiplication of a representative by the inverse uniformizer. -/
def scaleSection (z : MatrixQuotient v a b) : MatrixQuotient v a b :=
  QuotientAddGroup.mk ((uniformizer v)⁻¹ • (Quotient.out z :
    Matrix (Fin a) (Fin b) (FiniteCompletion F v)))

theorem scaleMap_scaleSection (z : MatrixQuotient v a b) :
    scaleMap v a b (scaleSection z) = z := by
  rw [scaleSection, scaleMap_mk, smul_smul, mul_inv_cancel₀ (uniformizer_ne_zero v), one_smul]
  exact Quotient.out_eq z

variable (v a b) in
/-- The residue of `ϖ y`, for `y` in the kernel of `scaleMap`. -/
def kernelResidue (κ : (scaleMap v a b).ker) :
    Fin a → Fin b → IsLocalRing.ResidueField (LocalGalois.baseIntegers (FiniteCompletion F v)) :=
  fun i j => IsLocalRing.residue _ ⟨uniformizer v * (Quotient.out κ.val :
      Matrix (Fin a) (Fin b) (FiniteCompletion F v)) i j, by
    have h := κ.property
    rw [AddMonoidHom.mem_ker, ← QuotientAddGroup.out_eq' κ.val, scaleMap_mk,
      QuotientAddGroup.eq_zero_iff, mem_integralLattice_iff] at h
    have hij := (norm_entry_le_entryNorm _ i j).trans h
    change ‖uniformizer v * _‖₊ ≤ 1
    exact_mod_cast hij⟩

theorem kernelResidue_injective : Function.Injective (kernelResidue v a b) := by
  intro κ κ' h
  apply Subtype.ext
  rw [← QuotientAddGroup.out_eq' κ.val, ← QuotientAddGroup.out_eq' κ'.val]
  apply QuotientAddGroup.eq.mpr
  rw [mem_integralLattice_iff, entryNorm_le_iff zero_le_one]
  intro i j
  have hij := congrFun (congrFun h i) j
  simp only [kernelResidue] at hij
  rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff,
    Valuation.mem_maximalIdeal_iff] at hij
  change ‖uniformizer v * _ - uniformizer v * _‖ < 1 at hij
  rw [← mul_sub, norm_mul, norm_uniformizer, ← div_eq_inv_mul,
    div_lt_one (absNorm_pos v)] at hij
  have hle := norm_le_one_of_lt_absNorm v hij
  rw [← norm_neg] at hle
  simpa only [neg_sub, Matrix.add_apply, Matrix.neg_apply, neg_add_eq_sub] using hle

instance finite_kernel : Finite (scaleMap v a b).ker :=
  Finite.of_injective _ kernelResidue_injective

theorem card_kernel_le :
    Nat.card (scaleMap v a b).ker ≤ Ideal.absNorm v.asIdeal ^ (a * b) := by
  refine (Nat.card_le_card_of_injective _ kernelResidue_injective).trans (le_of_eq ?_)
  rw [Nat.card_fun, Nat.card_fun, CompletionResidue.card_residueField, Nat.card_fin,
    Nat.card_fin, ← pow_mul, mul_comm b a]

/-- **Fibre bound.** Summing a function along `scaleMap` multiplies the sum by at most the
order of the kernel. -/
theorem tsum_comp_scaleMap_le (g : MatrixQuotient v a b → ℝ≥0∞) :
    ∑' y, g (scaleMap v a b y) ≤ (Nat.card (scaleMap v a b).ker : ℝ≥0∞) * ∑' z, g z := by
  let Φ : MatrixQuotient v a b → MatrixQuotient v a b × (scaleMap v a b).ker := fun y =>
    (scaleMap v a b y, ⟨y - scaleSection (scaleMap v a b y), by
      rw [AddMonoidHom.mem_ker, map_sub, scaleMap_scaleSection, sub_self]⟩)
  have hΦ : Function.Injective Φ := by
    intro y y' h
    have h1 : scaleMap v a b y = scaleMap v a b y' := congrArg Prod.fst h
    have h2 := congrArg (fun p => (p.2 : MatrixQuotient v a b)) h
    simp only [Φ, h1] at h2
    exact sub_left_injective h2
  have := ENNReal.tsum_comp_le_tsum_of_injective hΦ (fun p => g p.1)
  refine this.trans (le_of_eq ?_)
  rw [show (∑' p : MatrixQuotient v a b × (scaleMap v a b).ker, g p.1) =
      ∑' z, ∑' (_κ : (scaleMap v a b).ker), g z from
    ENNReal.tsum_prod (f := fun z (_ : (scaleMap v a b).ker) => g z)]
  have := Fintype.ofFinite (scaleMap v a b).ker
  simp only [tsum_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [ENNReal.tsum_mul_left, Nat.card_eq_fintype_card]

variable (v) in
/-- The truncated terms `max(1, ‖y‖)^(-β)` for `max(1, ‖y‖) ≤ N(v)^k`. -/
def truncatedTerm (β : ℝ) (k : ℕ) (y : MatrixQuotient v a b) : ℝ≥0∞ :=
  if classHeight v y ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ k then
    ENNReal.ofReal (classHeight v y ^ (-β)) else 0

theorem ofReal_classHeight_rpow_le_one {β : ℝ} (hβ : 0 ≤ β) (y : MatrixQuotient v a b) :
    ENNReal.ofReal (classHeight v y ^ (-β)) ≤ 1 := by
  rw [ENNReal.ofReal_le_one]
  exact Real.rpow_le_one_of_one_le_of_nonpos (one_le_classHeight y) (neg_nonpos.mpr hβ)

theorem truncatedTerm_zero_le {β : ℝ} (hβ : 0 ≤ β) (y : MatrixQuotient v a b) :
    truncatedTerm v β 0 y ≤ if y = 0 then 1 else 0 := by
  unfold truncatedTerm
  split_ifs with h hy hy
  · exact ofReal_classHeight_rpow_le_one hβ y
  · rw [pow_zero] at h
    exact absurd (eq_zero_of_classHeight_le_one h) hy
  · exact zero_le
  · exact le_rfl

theorem truncatedTerm_succ_le {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) (y : MatrixQuotient v a b) :
    truncatedTerm v β (k + 1) y ≤ (if y = 0 then 1 else 0) +
      ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (-β)) *
        truncatedTerm v β k (scaleMap v a b y) := by
  by_cases hy : y = 0
  · rw [ite_eq_left hy]
    refine le_trans ?_ le_self_add
    unfold truncatedTerm
    split_ifs
    · exact ofReal_classHeight_rpow_le_one hβ y
    · exact zero_le
  rw [ite_eq_right hy, zero_add]
  have hq := absNorm_pos v
  have hs := classHeight_scaleMap hy
  unfold truncatedTerm
  split_ifs with h1 h2
  · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _), hs,
      Real.mul_rpow (inv_nonneg.mpr hq.le) (zero_le_one.trans (one_le_classHeight y)),
      Real.inv_rpow hq.le, Real.rpow_neg hq.le, inv_inv, ← mul_assoc,
      inv_mul_cancel₀ (Real.rpow_pos_of_pos hq _).ne', one_mul]
  · exfalso
    apply h2
    rw [hs, ← div_eq_inv_mul, div_le_iff₀ hq, ← pow_succ]
    exact h1
  · exact zero_le
  · exact zero_le

/-- The truncated sums are bounded by `1 + 2 N(v)^(a b - β)` when `β ≥ 0` and
`N(v)^(a b - β) ≤ 1/2`. -/
theorem tsum_truncatedTerm_le {β : ℝ} (hβ : 0 ≤ β)
    (hε : (Ideal.absNorm v.asIdeal : ℝ) ^ ((a * b : ℕ) - β) ≤ 1 / 2) (k : ℕ) :
    ∑' y : MatrixQuotient v a b, truncatedTerm v β k y ≤
      ENNReal.ofReal (1 + 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ ((a * b : ℕ) - β)) := by
  set ε := (Ideal.absNorm v.asIdeal : ℝ) ^ ((a * b : ℕ) - β) with hεdef
  have hq := absNorm_pos v
  have hε0 : 0 ≤ ε := Real.rpow_nonneg hq.le _
  have hδ : ∑' y : MatrixQuotient v a b, (if y = 0 then (1 : ℝ≥0∞) else 0) = 1 := by
    rw [tsum_ite_eq]
  induction k with
  | zero =>
    refine (ENNReal.tsum_le_tsum (truncatedTerm_zero_le hβ)).trans ?_
    rw [hδ, ← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  | succ k ih =>
    refine (ENNReal.tsum_le_tsum (truncatedTerm_succ_le hβ k)).trans ?_
    rw [ENNReal.tsum_add, hδ, ENNReal.tsum_mul_left]
    have hcard : (Nat.card (scaleMap v a b).ker : ℝ≥0∞) ≤
        ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (a * b)) := by
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal (by exact_mod_cast card_kernel_le)
    calc 1 + ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (-β)) *
          ∑' y, truncatedTerm v β k (scaleMap v a b y)
        ≤ 1 + ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (-β)) *
          (ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (a * b)) *
            ENNReal.ofReal (1 + 2 * ε)) := by
          gcongr
          exact (tsum_comp_scaleMap_le _).trans (mul_le_mul' hcard ih)
      _ = ENNReal.ofReal (1 + ε * (1 + 2 * ε)) := by
          rw [← ENNReal.ofReal_mul (pow_nonneg hq.le _),
            ← ENNReal.ofReal_mul (Real.rpow_nonneg hq.le _), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by positivity)]
          congr 2
          rw [← mul_assoc, hεdef, ← Real.rpow_natCast, ← Real.rpow_add hq]
          congr 2
          ring
      _ ≤ ENNReal.ofReal (1 + 2 * ε) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith

/-- **The local sum.** If `β ≥ 0` and `N(v)^(a b - β) ≤ 1/2`, then
`∑_(y ∈ M(F_v)/M(𝒪_v)) max(1, ‖y‖)^(-β) ≤ 1 + 2 N(v)^(a b - β)`. -/
theorem tsum_classHeight_rpow_le {β : ℝ} (hβ : 0 ≤ β)
    (hε : (Ideal.absNorm v.asIdeal : ℝ) ^ ((a * b : ℕ) - β) ≤ 1 / 2) :
    ∑' y : MatrixQuotient v a b, ENNReal.ofReal (classHeight v y ^ (-β)) ≤
      ENNReal.ofReal (1 + 2 * (Ideal.absNorm v.asIdeal : ℝ) ^ ((a * b : ℕ) - β)) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hq1 := one_lt_absNorm v
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ y ∈ s, classHeight v y ≤ (Ideal.absNorm v.asIdeal : ℝ) ^ K := by
    choose k hk using fun y : MatrixQuotient v a b => pow_unbounded_of_one_lt (classHeight v y) hq1
    refine ⟨s.sup k, fun y hy => (hk y).le.trans ?_⟩
    exact pow_le_pow_right₀ hq1.le (Finset.le_sup hy)
  calc ∑ y ∈ s, ENNReal.ofReal (classHeight v y ^ (-β))
      = ∑ y ∈ s, truncatedTerm v β K y :=
        Finset.sum_congr rfl fun y hy => by rw [truncatedTerm, ite_eq_left (hK y hy)]
    _ ≤ ∑' y, truncatedTerm v β K y := ENNReal.sum_le_tsum _
    _ ≤ _ := tsum_truncatedTerm_le hβ hε K

end Quotient

end Langlands.Global.CuspidalPairEisenstein.OpenCellMajorant

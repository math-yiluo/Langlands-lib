import Langlands.Representation.Conductor.UnramifiedPrincipalSeries
import Langlands.Representation.Induction.Equivalences
import Langlands.Representation.Induction.RankCast
import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.RankinSelberg.LocalFactor
import Langlands.AllField.Representation.Induction.BlockFactors
import Langlands.AllField.Representation.RankinSelberg.LocalFieldUnequalRankFunctionalEquationReduction
import Mathlib.RingTheory.PiTensorProduct

/-!
# The unramified principal series as normalized product induction

Over every nonarchimedean local field `F`, the normalized unramified principal series
`I(z) = Conductor.UnramifiedPrincipalSeries.principalSeries hϖ n hq z` of `GL_(n+1)(F)`
is equivalent to the all-field normalized product induction
`(⟨⟩ : LocalFieldData F).normalizedProductInduced` of the rank-one characters
`χ_{z_0}, …, χ_{z_n}` from the standard parabolic with `n + 1` blocks of size one.

Both are smooth induction by right translation. The parabolic of the singleton shape is
the upper triangular group; the tensor product of `n + 1` copies of `ℂ` is identified with
`ℂ` by multiplication of the entries; and the positive half modulus
`δ_B(b)^(1/2) = ∏_(i<j) (|b_ii| / |b_jj|)^(1/2)` of the all-field normalization equals
`√q ^ (-∑_i (n - 2i) ord(b_ii))`, the half modulus used by `principalSeries`.
-/

noncomputable section

namespace Langlands.AllField.Conductor.UnramifiedPrincipalSeries

open Langlands.GeneralLinear Langlands.GeneralLinear.Iwasawa Langlands.Induction
open Langlands.Conductor.UnramifiedPrincipalSeries
open scoped BigOperators NNReal

universe uF

section Exponents

/-- `∑_(i<j) (λ_i - λ_j) = ∑_i (n - 2i) λ_i` on `Fin (n + 1)`. -/
theorem sum_pairs_sub_eq (n : ℕ) (lam : Fin (n + 1) → ℤ) :
    ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      (lam i - lam j) = ∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * lam i := by
  have hswap : ∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
      lam j = ∑ j : Fin (n + 1), ∑ _i ∈ Finset.univ.filter (fun i : Fin (n + 1) => i < j),
      lam j := by
    apply Finset.sum_comm'
    intro i j
    simp
  have hcard1 (i : Fin (n + 1)) :
      ((Finset.univ.filter (fun j : Fin (n + 1) => i < j)).card : ℤ) = n - i := by
    rw [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.mp i.isLt
    rw [show n + 1 - 1 - (i : ℕ) = n - i by omega, Nat.cast_sub hi]
  have hcard2 (j : Fin (n + 1)) :
      ((Finset.univ.filter (fun i : Fin (n + 1) => i < j)).card : ℤ) = j := by
    rw [Finset.filter_gt_eq_Iio, Fin.card_Iio]
  simp only [Finset.sum_sub_distrib]
  rw [hswap]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard1, hcard2]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem prod_zpow_eq_zpow_sum' {ι : Type*} (s : Finset ι) (f : ι → ℤ) {x : ℝ} (hx : x ≠ 0) :
    ∏ i ∈ s, x ^ f i = x ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hx]

end Exponents

/-- The shape of `n + 1` blocks of size one, written as the `succBlockShape` of the
multiplicativity statement. It is the singleton shape. -/
abbrev borelBlocks (n : ℕ) : BlockShape (n + 1) :=
  RankinSelberg.succBlockShape (fun _ : Fin (n + 1) => 0) (by simp)

theorem borelBlocks_eq_singletons (n : ℕ) :
    borelBlocks n = BlockShape.singletons (n + 1) := rfl

section Field

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {ϖ : Fˣ} (hϖ : IsUniformizingElement (ValuativeRel.valuation F) ϖ)

/-- The order of the ambient local-field data is the order relative to `ϖ`. -/
theorem ord_ofInstances (a : Fˣ) :
    (LocalFieldData.ofInstances F).ord (a : F) = ord hϖ a := by
  have hvx : ValuativeRel.valuation F (a : F) =
      ValuativeRel.valuation F ((ϖ : F) ^ ord hϖ a) := by
    rw [valuation_eq_pow_ord hϖ a, map_zpow₀]
  have hdv := AllField.RankinSelberg.discreteValuation_eq_of_valuation_eq hvx
  rw [LocalFieldData.ord, hdv, map_zpow₀,
    AllField.RankinSelberg.discreteValuation_of_isUniformizingElement hϖ,
    ← WithZero.exp_zsmul, WithZero.log_exp, smul_eq_mul]
  ring

/-- On units, the normalized absolute value of the ambient data is `q ^ (-ord)`. -/
theorem normalizedAbs_units {q : ℕ} (hq : IsResidueCardinality (F := F) q) (a : Fˣ) :
    (LocalFieldData.ofInstances F).normalizedAbs (a : F) = (q : ℝ) ^ (-ord hϖ a) := by
  rw [LocalFieldData.normalizedAbs_of_ne_zero _ a.ne_zero, ord_ofInstances hϖ,
    AllField.RankinSelberg.residueCardinality_ofInstances, ← hq]

/-- An unramified character is continuous: its kernel is open. -/
theorem continuous_character (z : ℂˣ) : Continuous (character hϖ z) := by
  apply continuous_of_continuousAt_one
  have hmem : ((character hϖ z).ker : Set Fˣ) ∈ nhds (1 : Fˣ) :=
    (isOpen_ker_character hϖ z).mem_nhds (one_mem _)
  have heq : (fun _ : Fˣ => (1 : ℂˣ)) =ᶠ[nhds 1] (character hϖ z) :=
    Filter.mem_of_superset hmem (fun x hx => (MonoidHom.mem_ker.mp hx).symm)
  exact continuousAt_const.congr heq

/-- The unramified character `χ_z` as a continuous quasicharacter. -/
def quasicharacter (z : ℂˣ) : HarmonicAnalysis.Quasicharacter F :=
  ⟨character hϖ z, continuous_character hϖ z⟩

@[simp]
theorem quasicharacter_toMonoidHom (z : ℂˣ) :
    ((quasicharacter hϖ z : HarmonicAnalysis.Quasicharacter F) : Fˣ →* ℂˣ) =
      character hϖ z := rfl

variable (n : ℕ)

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem mem_borelBlocks_parabolic_iff (g : GeneralLinear (n + 1) F) :
    g ∈ (borelBlocks n).parabolic F ↔ g ∈ upperTriangularSubgroup (n + 1) F :=
  BlockShape.singletons_mem_parabolic_iff F g

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem borelBlocks_parabolic_le :
    (borelBlocks n).parabolic F ≤ upperTriangularSubgroup (n + 1) F :=
  fun g hg => (mem_borelBlocks_parabolic_iff n g).mp hg

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem upperTriangular_le_borelBlocks_parabolic :
    upperTriangularSubgroup (n + 1) F ≤ (borelBlocks n).parabolic F :=
  fun g hg => (mem_borelBlocks_parabolic_iff n g).mpr hg

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- The `1 × 1` diagonal blocks of a singleton-shape parabolic element are its diagonal
entries. -/
theorem determinant_leviProjection (p : (borelBlocks n).parabolic F) (i : Fin (n + 1)) :
    determinant ((borelBlocks n).leviProjection F p i) =
      diagonalUnit n i (Subgroup.inclusion (borelBlocks_parabolic_le n) p) := by
  apply Units.ext
  change ((borelBlocks n).leviProjection F p i).val.det = p.val.val i i
  have : Unique (Fin ((borelBlocks n).size i)) := inferInstanceAs (Unique (Fin 1))
  rw [Matrix.det_unique, BlockShape.leviProjection_apply]
  exact congrArg₂ (fun a b => p.val.val a b) (BlockShape.singletons_index i _)
    (BlockShape.singletons_index i _)

/-- The all-field block modulus of the singleton shape is `q ^ (-∑_i (n - 2i) ord(b_ii))`. -/
theorem leviModulus_borelBlocks {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (p : (borelBlocks n).parabolic F) :
    ((((⟨⟩ : LocalFieldData F).leviModulus (borelBlocks n)
        ((borelBlocks n).leviProjection F p) : ℝ≥0ˣ) : ℝ≥0) : ℝ) =
      (q : ℝ) ^ (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) *
        ord hϖ (diagonalUnit n i (Subgroup.inclusion (borelBlocks_parabolic_le n) p))) := by
  set o : Fin (n + 1) → ℤ := fun i =>
    ord hϖ (diagonalUnit n i (Subgroup.inclusion (borelBlocks_parabolic_le n) p)) with ho
  have hq0 : (q : ℝ) ≠ 0 := by
    have := residueCardinality_pos hq
    positivity
  have hd : ∀ i : Fin (n + 1),
      ((((⟨⟩ : LocalFieldData F).determinantNorm ((borelBlocks n).size i)
        ((borelBlocks n).leviProjection F p i) : ℝ≥0ˣ) : ℝ≥0) : ℝ) = (q : ℝ) ^ (-o i) := by
    intro i
    rw [LocalFieldData.determinantNorm_coe, determinant_leviProjection]
    exact normalizedAbs_units hϖ hq _
  rw [LocalFieldData.leviModulus_apply]
  push_cast
  simp only [hd, pow_one]
  calc ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j => i < j),
        (q : ℝ) ^ (-o i) / (q : ℝ) ^ (-o j)
      = ∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j => i < j),
          (q : ℝ) ^ (-(o i - o j)) := by
        refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
        rw [← zpow_sub₀ hq0]
        ring_nf
    _ = (q : ℝ) ^ (∑ i : Fin (n + 1), ∑ j ∈ Finset.univ.filter (fun j => i < j),
          -(o i - o j)) := by
        rw [← prod_zpow_eq_zpow_sum' _ _ hq0]
        exact Finset.prod_congr rfl fun i _ => prod_zpow_eq_zpow_sum' _ _ hq0
    _ = (q : ℝ) ^ (-∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) * o i) := by
        rw [← sum_pairs_sub_eq n o]
        simp only [Finset.sum_neg_distrib]

/-- The all-field positive half modulus of the singleton parabolic is the half modulus of
`principalSeries`. -/
theorem parabolicHalfModulus_borelBlocks {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (p : (borelBlocks n).parabolic F) :
    ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (borelBlocks n) p : ℂ) =
      (halfModulusCharacter hϖ n hq (Subgroup.inclusion (borelBlocks_parabolic_le n) p) : ℂ) := by
  rw [LocalFieldData.parabolicHalfModulus_apply, LocalFieldData.leviHalfModulus_apply,
    halfModulusCharacter_apply, Real.coe_sqrt, leviModulus_borelBlocks hϖ n hq p]
  set E : ℤ := -∑ i : Fin (n + 1), ((n : ℤ) - 2 * (i : ℤ)) *
    ord hϖ (diagonalUnit n i (Subgroup.inclusion (borelBlocks_parabolic_le n) p))
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hsq : (q : ℝ) ^ E = (Real.sqrt q ^ E) ^ 2 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, Real.sq_sqrt hq0]
  rw [hsq, Real.sqrt_sq (zpow_nonneg (Real.sqrt_nonneg _) _), Complex.ofReal_zpow]

/-- The rank-one blocks `χ_{z_0}, …, χ_{z_n}` of `I(z)`. -/
abbrev blocks (z : Fin (n + 1) → ℂˣ) :
    ∀ i : Fin (borelBlocks n).length,
      Representation ℂ (GeneralLinear ((borelBlocks n).size i) F) ℂ :=
  fun i => RankinSelberg.rankOneCharacter (character hϖ (z i))

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
@[simp]
theorem blocks_apply (z : Fin (n + 1) → ℂˣ) (i : Fin (borelBlocks n).length)
    (g : GeneralLinear ((borelBlocks n).size i) F) (x : ℂ) :
    blocks hϖ n z i g x = (character hϖ (z i) (determinant g) : ℂ) * x := rfl

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Multiplication of the entries identifies the block tensor product of the rank-one
characters with the scalar product of their values. -/
theorem constantBaseRingEquiv_blockTensor (z : Fin (n + 1) → ℂˣ)
    (L : (borelBlocks n).Levi F) (x : PiTensorProduct ℂ (fun _ : Fin (n + 1) => ℂ)) :
    PiTensorProduct.constantBaseRingEquiv (Fin (n + 1)) ℂ
        ((borelBlocks n).blockTensor (blocks hϖ n z) L x) =
      (∏ i : Fin (n + 1), (character hϖ (z i) (determinant (L i)) : ℂ)) *
        PiTensorProduct.constantBaseRingEquiv (Fin (n + 1)) ℂ x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r v =>
    rw [map_smul, map_smul, map_smul, BlockShape.blockTensor_tprod,
      PiTensorProduct.constantBaseRingEquiv_tprod, PiTensorProduct.constantBaseRingEquiv_tprod]
    rw [Finset.prod_congr rfl (fun i _ => blocks_apply hϖ n z i (L i) (v i)),
      Finset.prod_mul_distrib, smul_eq_mul]
    ring
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, mul_add]

/-- The normalized Borel character of `I(z)` restricted to the singleton-shape parabolic
(which is the upper triangular group). -/
abbrev parabolicCharacter {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) : (borelBlocks n).parabolic F →* ℂˣ :=
  (normalizedCharacter hϖ n hq z).comp (Subgroup.inclusion (borelBlocks_parabolic_le n))

/-- On the singleton-shape parabolic, the inducing representation of the all-field normalized
product induction (half modulus times the block tensor of the characters) is the normalized
Borel character of `I(z)`, along multiplication of the entries of the tensor. -/
def inducingEquiv {q : ℕ} (hq : IsResidueCardinality (F := F) q) (z : Fin (n + 1) → ℂˣ) :
    (twist ((⟨⟩ : LocalFieldData F).parabolicHalfModulus (borelBlocks n))
      (((borelBlocks n).blockTensor (blocks hϖ n z)).comp
        ((borelBlocks n).leviProjection F))).Equiv
      (characterRepresentation (parabolicCharacter hϖ n hq z)) where
  toLinearEquiv := (PiTensorProduct.constantBaseRingEquiv (Fin (n + 1)) ℂ).toLinearEquiv
  isIntertwining' p := LinearMap.ext fun v => by
    change PiTensorProduct.constantBaseRingEquiv (Fin (n + 1)) ℂ
        (((⟨⟩ : LocalFieldData F).parabolicHalfModulus (borelBlocks n) p : ℂ) •
          (borelBlocks n).blockTensor (blocks hϖ n z) ((borelBlocks n).leviProjection F p) v) =
      (normalizedCharacter hϖ n hq z (Subgroup.inclusion (borelBlocks_parabolic_le n) p) : ℂ) •
        PiTensorProduct.constantBaseRingEquiv (Fin (n + 1)) ℂ v
    rw [map_smul, constantBaseRingEquiv_blockTensor, parabolicHalfModulus_borelBlocks hϖ n hq,
      normalizedCharacter_apply, smul_eq_mul, smul_eq_mul]
    have hdet : ∀ i : Fin (n + 1),
        (character hϖ (z i) (determinant ((borelBlocks n).leviProjection F p i)) : ℂ) =
          (character hϖ (z i)
            (diagonalUnit n i (Subgroup.inclusion (borelBlocks_parabolic_le n) p)) : ℂ) :=
      fun i => by rw [determinant_leviProjection]
    rw [Finset.prod_congr rfl fun i _ => hdet i]
    ring

/-- **The unramified principal series is a normalized product induction.** Over every
nonarchimedean local field, `I(z)` is equivalent to the all-field normalized induction of the
rank-one characters `χ_{z_0}, …, χ_{z_n}` from the parabolic of `n + 1` blocks of size one. -/
def principalSeriesEquiv {q : ℕ} (hq : IsResidueCardinality (F := F) q)
    (z : Fin (n + 1) → ℂˣ) :
    (principalSeries hϖ n hq z).Equiv
      ((⟨⟩ : LocalFieldData F).normalizedProductInduced (borelBlocks n) (blocks hϖ n z)) :=
  (Induction.comapSmoothInducedEquiv (MulEquiv.refl _) continuous_id continuous_id
      (fun g => (mem_borelBlocks_parabolic_iff n g).symm) (fun _ => rfl)).trans
    (Induction.smoothInducedEquiv _ (inducingEquiv hϖ n hq z)).symm

end Field

end Langlands.AllField.Conductor.UnramifiedPrincipalSeries

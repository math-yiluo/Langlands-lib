import Langlands.Shimura.Unitary.PositiveArithmeticFinite
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Localization.Module
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! # Rational lattices of finite adelic matrices

Every invertible matrix `X` over the rational finite adeles `𝔸_f` factors as `X = B W` with `B`
rational and `W, W⁻¹` integral: `GL_n(𝔸_f) = GL_n(ℚ) GL_n(Ẑ)`. The matrix `B` is a basis matrix of
the lattice `ℚ^n ∩ X Ẑ^n`. For `n = 1` this says that every finite idele of `ℚ` is a positive
rational times a unit of `Ẑ`.
-/

noncomputable section

namespace Langlands.Global.RationalLattice

open Matrix Module

local notation "𝔸f" => FiniteAdeles ℚ
local notation "Ẑ" => integralFiniteAdeles ℚ
local notation "ϕ" => algebraMap ℚ (FiniteAdeles ℚ)

section Integral

variable {m n o : Type*}

/-- A matrix over the finite adeles is integral if all its entries lie in `Ẑ`. -/
def IsIntegral (M : Matrix m n 𝔸f) : Prop := ∀ i j, M i j ∈ Ẑ

theorem IsIntegral.mul [Fintype n] {M : Matrix m n 𝔸f} {M' : Matrix n o 𝔸f}
    (hM : IsIntegral M) (hM' : IsIntegral M') : IsIntegral (M * M') := fun i j => by
  rw [Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _ (hM i k) (hM' k j)

theorem IsIntegral.intCast_smul {M : Matrix m n 𝔸f} (hM : IsIntegral M) (k : ℤ) :
    IsIntegral ((k : 𝔸f) • M) := fun i j => by
  rw [Matrix.smul_apply, smul_eq_mul]
  exact Subring.mul_mem _ (intCast_mem _ k) (hM i j)

theorem isIntegral_map_intCast (M : Matrix m n ℤ) : IsIntegral (M.map (Int.cast : ℤ → 𝔸f)) :=
  fun i j => intCast_mem _ (M i j)

theorem isIntegral_one [DecidableEq n] : IsIntegral (1 : Matrix n n 𝔸f) := fun i j => by
  by_cases h : i = j
  · rw [h, Matrix.one_apply_eq]
    exact Subring.one_mem _
  · rw [Matrix.one_apply_ne h]
    exact Subring.zero_mem _

/-- A rational matrix which is integral over `𝔸_f` has integer entries (`ℚ ∩ Ẑ = ℤ`). -/
theorem exists_int_of_isIntegral {M : Matrix m n ℚ} (hM : IsIntegral (M.map ϕ)) :
    ∃ M' : Matrix m n ℤ, M'.map (Int.cast : ℤ → ℚ) = M := by
  choose M' hM' using fun i j => exists_intCast_eq_of_mem_integralFiniteAdeles (hM i j)
  exact ⟨Matrix.of M', by ext i j; exact hM' i j⟩

/-- Every finite adele has an integer multiple in `Ẑ`. -/
theorem exists_intCast_mul_mem (a : 𝔸f) : ∃ N : ℤ, N ≠ 0 ∧ (N : 𝔸f) * a ∈ Ẑ := by
  obtain ⟨d, hd0, hd⟩ := exists_mul_mem_integralFiniteAdeles a
  refine ⟨Rat.ringOfIntegersEquiv d, (map_ne_zero_iff _ Rat.ringOfIntegersEquiv.injective).2 hd0,
    ?_⟩
  have h : algebraMap (NumberField.RingOfIntegers ℚ) 𝔸f d =
      ((Rat.ringOfIntegersEquiv d : ℤ) : 𝔸f) := by
    rw [IsScalarTower.algebraMap_apply (NumberField.RingOfIntegers ℚ) ℚ 𝔸f, ← map_intCast ϕ,
      Rat.ringOfIntegersEquiv_apply_coe]
  rwa [← h]

/-- Every finite adelic matrix has an integral nonzero integer multiple. -/
theorem exists_intCast_smul_isIntegral [Fintype m] [Fintype n] (M : Matrix m n 𝔸f) :
    ∃ N : ℤ, N ≠ 0 ∧ IsIntegral ((N : 𝔸f) • M) := by
  classical
  choose N hN0 hN using fun i j => exists_intCast_mul_mem (M i j)
  refine ⟨∏ p : m × n, N p.1 p.2, Finset.prod_ne_zero_iff.2 fun p _ => hN0 p.1 p.2,
    fun i j => ?_⟩
  rw [Matrix.smul_apply, smul_eq_mul, ← Finset.prod_erase_mul _ _ (Finset.mem_univ (i, j)),
    Int.cast_mul, mul_assoc]
  exact Subring.mul_mem _ (intCast_mem _ _) (hN i j)

/-- Strong approximation for `ℚ`: `𝔸_f = ℚ + N Ẑ`. -/
theorem exists_rat_add_mul (N : ℤ) (hN : N ≠ 0) (a : 𝔸f) :
    ∃ (q : ℚ) (t : 𝔸f), t ∈ Ẑ ∧ a = ϕ q + (N : 𝔸f) * t := by
  obtain ⟨x, hx⟩ := exists_sub_mem_integralFiniteAdeles (ϕ (N : ℚ)⁻¹ * a)
  refine ⟨N * x, ϕ (N : ℚ)⁻¹ * a - ϕ x, hx, ?_⟩
  have hN' : (N : 𝔸f) * ϕ ((N : ℚ)⁻¹) = 1 := by
    rw [← map_intCast ϕ N, ← map_mul, mul_inv_cancel₀ (Int.cast_ne_zero.2 hN), map_one]
  rw [mul_sub, ← mul_assoc, hN', one_mul, map_mul, map_intCast]
  ring

end Integral

section Lattice

variable {ι : Type*} [Fintype ι]

/-- A vector of `𝔸_f^ι` lies in `B Ẑ^ι`. -/
def InSpan (B : Matrix ι ι ℚ) (v : ι → 𝔸f) : Prop :=
  ∃ w : ι → 𝔸f, (∀ i, w i ∈ Ẑ) ∧ v = B.map ϕ *ᵥ w

theorem InSpan.add {B : Matrix ι ι ℚ} {v v' : ι → 𝔸f} (hv : InSpan B v) (hv' : InSpan B v') :
    InSpan B (v + v') := by
  obtain ⟨w, hw, rfl⟩ := hv
  obtain ⟨w', hw', rfl⟩ := hv'
  exact ⟨w + w', fun i => Subring.add_mem _ (hw i) (hw' i), (Matrix.mulVec_add _ _ _).symm⟩

theorem InSpan.smul {B : Matrix ι ι ℚ} {v : ι → 𝔸f} (hv : InSpan B v) {t : 𝔸f} (ht : t ∈ Ẑ) :
    InSpan B (t • v) := by
  obtain ⟨w, hw, rfl⟩ := hv
  exact ⟨t • w, fun i => Subring.mul_mem _ ht (hw i), (Matrix.mulVec_smul _ _ _).symm⟩

theorem inSpan_zero (B : Matrix ι ι ℚ) : InSpan B 0 :=
  ⟨0, fun _ => Subring.zero_mem _, (Matrix.mulVec_zero _).symm⟩

theorem InSpan.sum {B : Matrix ι ι ℚ} {κ : Type*} (s : Finset κ) {v : κ → ι → 𝔸f}
    (hv : ∀ k ∈ s, InSpan B (v k)) : InSpan B (∑ k ∈ s, v k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using inSpan_zero B
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hv a (Finset.mem_insert_self a s)).add
      (ih fun k hk => hv k (Finset.mem_insert_of_mem hk))

variable [DecidableEq ι]

/-- The `ℤ`-submodule of rational vectors `q` with `X⁻¹ q` integral, where `X⁻¹` is Mathlib's
totalized inverse (zero when `X` is singular). For `X` with unit determinant this is the lattice
`ℚ^ι ∩ X Ẑ^ι` (`mem_lattice_iff`); for singular `X` it is not. -/
def lattice (X : Matrix ι ι 𝔸f) : Submodule ℤ (ι → ℚ) where
  carrier := {q | ∀ i, (X⁻¹ *ᵥ fun j => ϕ (q j)) i ∈ Ẑ}
  add_mem' {q q'} hq hq' := by
    change ∀ i, (X⁻¹ *ᵥ fun j => ϕ ((q + q') j)) i ∈ Ẑ
    intro i
    have : (fun j => ϕ ((q + q') j)) = (fun j => ϕ (q j)) + fun j => ϕ (q' j) := by
      ext j
      simp
    rw [this, Matrix.mulVec_add]
    exact Subring.add_mem _ (hq i) (hq' i)
  zero_mem' := by
    change ∀ i, (X⁻¹ *ᵥ fun j => ϕ ((0 : ι → ℚ) j)) i ∈ Ẑ
    intro i
    simp only [Pi.zero_apply, map_zero]
    rw [show (fun _ : ι => (0 : 𝔸f)) = 0 from rfl, Matrix.mulVec_zero]
    exact Subring.zero_mem _
  smul_mem' k q hq := by
    change ∀ i, (X⁻¹ *ᵥ fun j => ϕ ((k • q) j)) i ∈ Ẑ
    intro i
    have : (fun j => ϕ ((k • q) j)) = (k : 𝔸f) • fun j => ϕ (q j) := by
      ext j
      simp [zsmul_eq_mul]
    rw [this, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    exact Subring.mul_mem _ (intCast_mem _ k) (hq i)

theorem mem_lattice {X : Matrix ι ι 𝔸f} {q : ι → ℚ} :
    q ∈ lattice X ↔ ∀ i, (X⁻¹ *ᵥ fun j => ϕ (q j)) i ∈ Ẑ :=
  Iff.rfl

/-- For `X` with unit determinant, `lattice X` is `ℚ^ι ∩ X Ẑ^ι`. -/
theorem mem_lattice_iff {X : Matrix ι ι 𝔸f} (hX : IsUnit X.det) {q : ι → ℚ} :
    q ∈ lattice X ↔ ∃ w : ι → 𝔸f, (∀ i, w i ∈ Ẑ) ∧ (fun j => ϕ (q j)) = X *ᵥ w := by
  constructor
  · intro hq
    refine ⟨X⁻¹ *ᵥ fun j => ϕ (q j), hq, ?_⟩
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv X hX, Matrix.one_mulVec]
  · rintro ⟨w, hw, hqw⟩
    intro i
    rw [hqw, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul X hX, Matrix.one_mulVec]
    exact hw i

theorem intCast_smul_single_mem {X : Matrix ι ι 𝔸f} {N : ℤ}
    (hN : IsIntegral ((N : 𝔸f) • X⁻¹)) (i : ι) :
    (N : ℚ) • Pi.single i (1 : ℚ) ∈ lattice X := by
  intro k
  have hv : (fun j => ϕ (((N : ℚ) • Pi.single i (1 : ℚ)) j)) = Pi.single i (N : 𝔸f) := by
    ext j
    by_cases h : j = i
    · subst h
      simp
    · simp [h]
  rw [hv, Matrix.mulVec_single]
  have := hN k i
  rw [Matrix.smul_apply, smul_eq_mul, mul_comm] at this
  simpa using this

theorem exists_intCast_eq_mul_of_mem {X : Matrix ι ι 𝔸f} (hX : IsUnit X.det) {N : ℤ}
    (hN : IsIntegral ((N : 𝔸f) • X)) {q : ι → ℚ} (hq : q ∈ lattice X) (i : ι) :
    ∃ z : ℤ, (z : ℚ) = N * q i := by
  apply exists_intCast_eq_of_mem_integralFiniteAdeles
  have h : ((N : 𝔸f) • X) *ᵥ (X⁻¹ *ᵥ fun j => ϕ (q j)) = (N : 𝔸f) • fun j => ϕ (q j) := by
    rw [Matrix.mulVec_mulVec, Matrix.smul_mul, Matrix.mul_nonsing_inv X hX, Matrix.smul_mulVec,
      Matrix.one_mulVec]
  have h2 := congrFun h i
  rw [Pi.smul_apply, smul_eq_mul] at h2
  rw [map_mul, map_intCast, ← h2]
  exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hN i j) (hq j)

/-- **`GL_ι(𝔸_f) = GL_ι(ℚ) GL_ι(Ẑ)`.** Every invertible finite adelic matrix `X` is `B W` with `B`
rational invertible and `W`, `W⁻¹ = X⁻¹ B` integral. -/
theorem exists_rat_mul_integral (X : Matrix ι ι 𝔸f) (hX : IsUnit X.det) :
    ∃ (B : Matrix ι ι ℚ) (W : Matrix ι ι 𝔸f), IsUnit B.det ∧ IsIntegral W ∧
      IsIntegral (X⁻¹ * B.map ϕ) ∧ X = B.map ϕ * W := by
  classical
  obtain ⟨N₁, hN₁, h₁⟩ := exists_intCast_smul_isIntegral X
  obtain ⟨N₂, hN₂, h₂⟩ := exists_intCast_smul_isIntegral X⁻¹
  set N := N₁ * N₂ with hNdef
  have hN : N ≠ 0 := mul_ne_zero hN₁ hN₂
  have hNX : IsIntegral ((N : 𝔸f) • X) := by
    have := h₁.intCast_smul N₂
    rwa [smul_smul, ← Int.cast_mul, mul_comm] at this
  have hNXi : IsIntegral ((N : 𝔸f) • X⁻¹) := by
    have := h₂.intCast_smul N₁
    rwa [smul_smul, ← Int.cast_mul] at this
  have hNq : (N : ℚ) ≠ 0 := Int.cast_ne_zero.2 hN
  set L := lattice X
  -- `L` lies in the span of the vectors `N⁻¹ e_i`
  let b0 : ι → ι → ℚ := fun i => (N : ℚ)⁻¹ • Pi.single i 1
  have hb0 : LinearIndependent ℤ b0 := by
    rw [LinearIndependent.iff_fractionRing ℤ ℚ]
    convert (Pi.basisFun ℚ ι).linearIndependent.units_smul
      (fun _ => Units.mk0 ((N : ℚ)⁻¹) (inv_ne_zero hNq)) using 1
    ext i j
    simp [b0, Pi.basisFun_apply]
  have hle : L ≤ Submodule.span ℤ (Set.range b0) := by
    intro q hq
    choose z hz using exists_intCast_eq_mul_of_mem hX hNX hq
    have hqz : q = ∑ i, z i • b0 i := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j
        (fun i _ hij => by simp [b0, hij.symm]) (by simp)]
      simp only [b0, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, zsmul_eq_mul]
      rw [hz j]
      field_simp
    rw [hqz]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  obtain ⟨n, bL⟩ := Submodule.basisOfPidOfLESpan hb0 hle
  -- the rank of `L` is `card ι`
  have : Module.Finite ℤ L := Module.Finite.of_basis bL
  have hv : LinearIndependent ℤ (fun k => (bL k : ι → ℚ)) :=
    bL.linearIndependent.map' L.subtype (Submodule.ker_subtype L)
  have hvQ : LinearIndependent ℚ (fun k => (bL k : ι → ℚ)) :=
    (LinearIndependent.iff_fractionRing ℤ ℚ).1 hv
  have h1 : n ≤ Fintype.card ι := by
    have := hvQ.fintype_card_le_finrank
    simpa [Module.finrank_fintype_fun_eq_card] using this
  have h2 : Fintype.card ι ≤ n := by
    let u : ι → L := fun i => ⟨(N : ℚ) • Pi.single i 1, intCast_smul_single_mem hNXi i⟩
    have hu : LinearIndependent ℤ u := by
      apply LinearIndependent.of_comp L.subtype
      rw [LinearIndependent.iff_fractionRing ℤ ℚ]
      convert (Pi.basisFun ℚ ι).linearIndependent.units_smul
        (fun _ => Units.mk0 (N : ℚ) hNq) using 1
      ext i j
      simp [u, Pi.basisFun_apply]
    have := hu.fintype_card_le_finrank
    rwa [Module.finrank_eq_card_basis bL, Fintype.card_fin] at this
  have hcard : Fintype.card (Fin n) = Fintype.card ι := by
    rw [Fintype.card_fin]
    omega
  let e : Fin n ≃ ι := Fintype.equivOfCardEq hcard
  let B : Matrix ι ι ℚ := Matrix.of fun i j => (bL (e.symm j) : ι → ℚ) i
  -- every vector of `L` is an integer combination of the columns of `B`
  have hrepr : ∀ q ∈ L, ∃ z : ι → ℤ, q = B *ᵥ fun j => (z j : ℚ) := by
    intro q hq
    refine ⟨fun j => bL.repr ⟨q, hq⟩ (e.symm j), ?_⟩
    have hs : q = ∑ k, bL.repr ⟨q, hq⟩ k • (bL k : ι → ℚ) := by
      have := congrArg Subtype.val (bL.sum_repr ⟨q, hq⟩)
      rw [Submodule.coe_sum] at this
      simp only [Submodule.coe_smul] at this
      exact this.symm
    ext i
    conv_lhs => rw [hs]
    rw [Finset.sum_apply, ← e.symm.sum_comp]
    simp only [Matrix.mulVec, dotProduct, B, Matrix.of_apply, Pi.smul_apply, zsmul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hspanL : ∀ q ∈ L, InSpan B fun i => ϕ (q i) := by
    intro q hq
    obtain ⟨z, rfl⟩ := hrepr q hq
    refine ⟨fun j => (z j : 𝔸f), fun j => intCast_mem _ _, ?_⟩
    have hz : (ϕ ∘ fun j => ((z j : ℤ) : ℚ)) = fun j => ((z j : ℤ) : 𝔸f) := by
      ext j
      simp
    ext i
    rw [RingHom.map_mulVec, hz]
  -- every column of `X` lies in `B Ẑ^ι`
  have hcol : ∀ j, InSpan B fun i => X i j := by
    intro j
    choose q t ht hqt using fun i => exists_rat_add_mul N hN (X i j)
    have hqL : q ∈ L := by
      intro k
      have hxq : (fun i => ϕ (q i)) = (fun i => X i j) - (N : 𝔸f) • t := by
        ext i
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
        rw [hqt i, add_sub_cancel_right]
      rw [hxq, Matrix.mulVec_sub, Pi.sub_apply]
      have hc : (X⁻¹ *ᵥ fun i => X i j) k = (X⁻¹ * X) k j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [hc, Matrix.nonsing_inv_mul X hX, Matrix.mulVec_smul, ← Matrix.smul_mulVec]
      refine Subring.sub_mem _ (isIntegral_one k j) ?_
      exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (hNXi k i) (ht i)
    have hNt : (N : 𝔸f) • t = ∑ i, t i • fun k => ϕ (((N : ℚ) • Pi.single i (1 : ℚ)) k) := by
      ext k
      simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply, mul_ite, mul_one,
        mul_zero, map_intCast, apply_ite ϕ, map_zero]
      rw [Finset.sum_ite_eq]
      simp [mul_comm]
    have hx : (fun i => X i j) = (fun i => ϕ (q i)) + (N : 𝔸f) • t := by
      ext i
      rw [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hqt i]
    rw [hx, hNt]
    exact (hspanL q hqL).add (InSpan.sum _ fun i _ =>
      (hspanL _ (intCast_smul_single_mem hNXi i)).smul (ht i))
  choose w hw hwx using hcol
  refine ⟨B, Matrix.of fun i j => w j i, ?_, fun i j => hw j i, ?_, ?_⟩
  · -- the columns of `B` are a `ℚ`-basis
    have hli : LinearIndependent ℚ B.col := hvQ.comp e.symm e.symm.injective
    exact (Matrix.isUnit_iff_isUnit_det B).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli)
  · intro i j
    have hmem : (fun k => (bL (e.symm j) : ι → ℚ) k) ∈ L := (bL (e.symm j)).2
    have := hmem i
    convert this using 1
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, B]
  · ext i j
    have := congrFun (hwx j) i
    rw [this]
    simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]

/-- **Finite ideles of `ℚ`.** Every unit `c` of `𝔸_f` is a positive rational times a unit of `Ẑ`:
`c = r u` with `r > 0` and `u, u⁻¹ ∈ Ẑ`. -/
theorem exists_pos_rat_mul_unit (c : 𝔸f) (hc : IsUnit c) :
    ∃ r : ℚ, 0 < r ∧ ∃ u u' : 𝔸f, u ∈ Ẑ ∧ u' ∈ Ẑ ∧ u * u' = 1 ∧ c = ϕ r * u := by
  classical
  set X : Matrix Unit Unit 𝔸f := Matrix.of fun _ _ => c with hXdef
  have hX : IsUnit X.det := by rwa [Matrix.det_unique]
  obtain ⟨B, W, hB, hW, hXB, hXW⟩ := exists_rat_mul_integral X hX
  set b := B () ()
  have hb : b ≠ 0 := by
    rw [Matrix.det_unique] at hB
    exact hB.ne_zero
  have hcw : c = ϕ b * W () () := by
    have := congrFun (congrFun hXW ()) ()
    simpa [X, Matrix.mul_apply] using this
  have hinv : X⁻¹ () () * c = 1 := by
    have := congrFun (congrFun (Matrix.nonsing_inv_mul X hX) ()) ()
    simpa [X, Matrix.mul_apply] using this
  have hu' : X⁻¹ () () * ϕ b ∈ Ẑ := by
    have := hXB () ()
    simpa [Matrix.mul_apply] using this
  have hWu : W () () * (X⁻¹ () () * ϕ b) = 1 := by
    rw [← hinv, hcw]
    ring
  rcases lt_or_gt_of_ne hb with hneg | hpos
  · refine ⟨-b, neg_pos.2 hneg, -W () (), -(X⁻¹ () () * ϕ b), Subring.neg_mem _ (hW () ()),
      Subring.neg_mem _ hu', by rw [neg_mul_neg]; exact hWu, ?_⟩
    rw [map_neg, neg_mul_neg]
    exact hcw
  · exact ⟨b, hpos, W () (), X⁻¹ () () * ϕ b, hW () (), hu', hWu, hcw⟩

end Lattice

end Langlands.Global.RationalLattice

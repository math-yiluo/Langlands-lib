import Langlands.Global.RankinSelberg.ComplexGapRetainedMellin

/-! # The tail coordinates observed by the column tests -/

noncomputable section

open Filter Set Topology
open scoped Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

open Langlands.Archimedean (unitaryCompact)
open Langlands.Archimedean (offDiag_eq_zero_of_upper_unitary norm_diag_eq_one_of_unitary)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (mul_conjTranspose_one)
open Langlands.GeneralLinear
open ComplexGapDualArguments (tailColumn)
open ComplexGapDualChart (retainedTail)
open ComplexGapLeadingHaar (outerWithLeading)
open ComplexGapTriangularChart (retainedMatrix)
open ComplexGapUnitDeterminant (unitRetained leadingScalar normalizingScalar)
open ComplexGapUpperTail (packedTail firstRectangle)
open ComplexLocalIwasawa (continuous_logTorus logTorus_neg)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)

variable (t q : ℕ)
local notation "k" => t + 1
local notation "m" => q + 1
local notation "n" => t + 1 + q + 1
local notation "G" => fun j => Langlands.GeneralLinear j ℂ
local notation "K" => fun j => unitaryCompact ℂ j
local notation "M" => fun i j => Matrix (Fin i) (Fin j) ℂ
local notation "P" => RetainedPoint t q
local notation "Vec" => (Fin n → ℂ)
local notation "e" => (finSumFinEquiv : Fin k ⊕ Fin m ≃ Fin n)
local notation "lead" => Fin.castAdd m
local notation "trail" => Fin.natAdd k

/-- The head column and every inverse-transpose tail column, in the order of the tests. -/
def tailObservation (p : P) : Fin (q + 2) → Vec :=
  Fin.cons (tailColumn k q (retainedGroup t q p) 0)
    (fun j => tailColumn k q (inverseTranspose n ℂ (retainedGroup t q p)) j)

theorem continuous_tailObservation : Continuous (tailObservation t q) := by
  apply continuous_pi
  intro j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [tailObservation, Fin.cons_zero]
    exact continuous_pi fun i => (Units.continuous_val.comp (continuous_retainedGroup t q)).matrix_elem i _
  · simp only [tailObservation, Fin.cons_succ]
    apply continuous_pi
    intro i
    exact (Units.continuous_val.comp ((continuous_inverseTranspose n ℂ).comp
      (continuous_retainedGroup t q))).matrix_elem i _

private def tailRows (A : M n n) : M m n := fun i j => A (trail i) j

private def selectTail : M m n := tailRows t q 1

private def firstBasis : Vec := fun i => (1 : M n n) i (trail (0 : Fin m))

/-- The observation at the identity has one basis column and the standard trailing rows. -/
def standardTailObservation : Fin (q + 2) → Vec :=
  Fin.cons (firstBasis t q) (selectTail t q)

private def trailingBlock (p : P) : G m := logTorus p.1.1.1 * p.2.val

private theorem retained_blocks (p : P) :
    Matrix.reindex (e).symm (e).symm ((p.1.1.2.val)⁻¹ * retainedGroup t q p).val =
      Matrix.fromBlocks (leadingScalar k q p.1.1.1).val
        (firstRectangle k q p.1.2 * p.2.val.val) 0 (trailingBlock t q p).val := by
  let S := leadingScalar k q p.1.1.1
  let D := logTorus p.1.1.1
  let X := firstRectangle k q p.1.2
  let Z := p.2
  have hRe : (p.1.1.2.val)⁻¹ * retainedGroup t q p =
      blockSum ((1 : G k), D) * (packedTail k q X 1).val * rankInclusion m S * (packedTail k q 0 Z).val := by
    unfold retainedGroup retainedTail unitRetained retainedMatrix
    change (p.1.1.2.val)⁻¹ * (p.1.1.2.val * blockSum ((1 : G k), D) * (packedTail k q X 1).val *
      rankInclusion m S * (packedTail k q 0 Z).val) = _
    simp only [mul_assoc, inv_mul_cancel_left]
  rw [hRe]
  let E := Matrix.reindexRingEquiv ℂ (e).symm
  change E ((Matrix.reindex e e (Matrix.fromBlocks (1 : M k k) 0 0 D.val)) *
      (Matrix.reindex e e (Matrix.fromBlocks (1 : M k k) X 0 (1 : M m m))) *
      (Matrix.reindex e e (Matrix.fromBlocks S.val 0 0 (1 : M m m))) *
      (Matrix.reindex e e (Matrix.fromBlocks (1 : M k k) 0 0 Z.val.val))) = _
  have hE (A : Matrix (Fin k ⊕ Fin m) (Fin k ⊕ Fin m) ℂ) : E (Matrix.reindex e e A) = A := by
    ext i j
    change A ((e).symm (e i)) ((e).symm (e j)) = _
    simp only [Equiv.symm_apply_apply]
  simp only [map_mul, hE, Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rfl

private theorem tailRows_mul (A B : M n n) : tailRows t q (A * B) = tailRows t q A * B := rfl

private theorem selectTail_entry_left (i : Fin m) (j : Fin k) : selectTail t q i (lead j) = 0 := by
  unfold selectTail tailRows
  apply Matrix.one_apply_ne
  intro h
  have h' := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h'
  omega

private theorem selectTail_entry_right (i j : Fin m) : selectTail t q i (trail j) = (1 : M m m) i j := by
  simp only [selectTail, tailRows, Matrix.one_apply, Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff]

private theorem mul_selectTail_left (D : M m m) (i : Fin m) (j : Fin k) :
    (D * selectTail t q) i (lead j) = 0 := by
  simp only [Matrix.mul_apply, selectTail_entry_left, mul_zero, Finset.sum_const_zero]

private theorem mul_selectTail_right (D : M m m) (i j : Fin m) :
    (D * selectTail t q) i (trail j) = D i j := by
  simp only [Matrix.mul_apply, selectTail_entry_right, Matrix.one_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]

private theorem selectTail_mul_conjTranspose : selectTail t q * (selectTail t q)ᴴ = (1 : M m m) := by
  ext i j
  rw [Matrix.mul_apply]
  change (∑ l : Fin n, (1 : M n n) (trail i) l * star ((1 : M n n) (trail j) l)) = _
  simp only [Matrix.one_apply, apply_ite star, star_one, star_zero, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  simp only [Fin.ext_iff, Fin.val_natAdd, Nat.add_left_cancel_iff, eq_comm]

private theorem retained_tailRows (p : P) :
    tailRows t q ((p.1.1.2.val⁻¹ * retainedGroup t q p).val) = (trailingBlock t q p).val * selectTail t q := by
  ext i j
  let A := (p.1.1.2.val⁻¹ * retainedGroup t q p).val
  have h (j : Fin k ⊕ Fin m) := congrFun (congrFun (retained_blocks t q p) (.inr i)) j
  refine Fin.addCases («m» := k) («n» := m) (fun j₀ => ?_) (fun j₁ => ?_) j
  · rw [mul_selectTail_left]
    exact h (.inl j₀)
  · rw [mul_selectTail_right]
    exact h (.inr j₁)

private theorem multiply_inverseRows (p : P) :
    tailRows t q (retainedGroup t q p)⁻¹.val * p.1.1.2.val.val = (trailingBlock t q p)⁻¹.val * selectTail t q := by
  let C := retainedGroup t q p
  let U := p.1.1.2.val
  let D := trailingBlock t q p
  have hm : (D.val * selectTail t q) * (C⁻¹ * U).val = selectTail t q := by
    rw [← retained_tailRows t q p, ← tailRows_mul, ← Units.val_mul]
    simp only [C, U, mul_assoc, mul_inv_cancel_left, inv_mul_cancel, Units.val_one, selectTail]
  calc
    _ = selectTail t q * (C⁻¹ * U).val := by
      rw [selectTail, ← tailRows_mul, ← tailRows_mul, Matrix.one_mul, Units.val_mul]
    _ = D⁻¹.val * ((D.val * selectTail t q) * (C⁻¹ * U).val) := by
      simp only [← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
    _ = _ := by rw [hm]

private theorem head_of_firstColumn (p : P) (i : Fin k) :
    (p.1.1.2.val⁻¹.val *ᵥ tailColumn k q (retainedGroup t q p) 0) (lead i) = p.1.2 i := by
  have h := congrFun (congrFun (retained_blocks t q p) (.inl i)) (.inr (0 : Fin m))
  change (p.1.1.2.val⁻¹ * retainedGroup t q p).val (lead i) (trail (0 : Fin m)) =
    (firstRectangle k q p.1.2 * p.2.val.val) i 0 at h
  change (p.1.1.2.val⁻¹ * retainedGroup t q p).val (lead i) (trail (0 : Fin m)) = _
  rw [h, Matrix.mul_apply, Fin.sum_univ_succ]
  simp only [firstRectangle, Fin.cons_zero, Fin.cons_succ, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero, UpperUnipotent.entry_diag, mul_one]

private theorem tailGram (p : P) :
    let R := tailRows t q (retainedGroup t q p)⁻¹.val
    let D := (trailingBlock t q p)⁻¹.val
    R * Rᴴ = D * Dᴴ := by
  intro R D
  let U := p.1.1.2.val.val
  have prodGram {i j l : Type} [Fintype j] [Fintype l] (A : Matrix i j ℂ) (B : Matrix j l ℂ) :
      (A * B) * (A * B)ᴴ = A * (B * Bᴴ) * Aᴴ := by
    rw [Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  calc
    R * Rᴴ = (R * U) * (R * U)ᴴ := by
      rw [prodGram, show U * Uᴴ = 1 from mul_conjTranspose_one p.1.1.2, Matrix.mul_one]
    _ = D * Dᴴ := by rw [show R * U = D * selectTail t q from multiply_inverseRows t q p, prodGram,
      selectTail_mul_conjTranspose, Matrix.mul_one]

private theorem trailingInv_triangular (p : P) : ((trailingBlock t q p)⁻¹.val).IsUpperTriangular := by
  intro i j hij
  have hz : (p.2.val⁻¹).val i j = 0 := UpperUnipotent.entry_eq_zero (p.2⁻¹) hij
  rw [trailingBlock, mul_inv_rev, ← logTorus_neg, Units.val_mul, logTorus_val, Matrix.mul_diagonal, hz, zero_mul]

private theorem trailingInv_diag (p : P) (i : Fin m) :
    (trailingBlock t q p)⁻¹.val i i = (Real.exp (-(p.1.1.1 i)) : ℂ) := by
  have hz : (p.2.val⁻¹).val i i = 1 := UpperUnipotent.entry_diag (p.2⁻¹) i
  rw [trailingBlock, mul_inv_rev, ← logTorus_neg, Units.val_mul, logTorus_val, Matrix.mul_diagonal, hz, one_mul]
  rfl

private theorem unitary_inverse_val (U : K n) : U.val⁻¹.val = U.val.valᴴ := by
  have h : U.val⁻¹.val * U.val.val = 1 := U.val.inv_mul
  calc
    _ = (U.val⁻¹.val * U.val.val) * U.val.valᴴ := by rw [Matrix.mul_assoc, mul_conjTranspose_one U, Matrix.mul_one]
    _ = _ := by rw [h, Matrix.one_mul]

private theorem logTorus_at_zero : logTorus (0 : Fin m → ℝ) = 1 := by
  apply Units.ext
  rw [logTorus_val]
  simp only [Pi.zero_apply, Real.exp_zero, Complex.ofReal_one, Units.val_one, Matrix.diagonal_one]

private theorem zero_retained (U : K n) : retainedGroup t q (((0, U), 0), 1) = U.val := by
  let p : P := (((0, U), 0), 1)
  have hS : leadingScalar k q (0 : Fin m → ℝ) = 1 := by
    unfold leadingScalar
    have hu : normalizingScalar k q (0 : Fin m → ℝ) = 1 := by
      apply Units.ext
      simp [normalizingScalar]
    rw [hu]
    exact map_one (Matrix.GeneralLinearGroup.scalar (Fin k))
  have hX : firstRectangle k q (0 : Fin k → ℂ) * (1 : M m m) = 0 := by
    rw [Matrix.mul_one]
    ext i j
    exact Fin.cases (by rfl) (fun _ => rfl) j
  have h : Matrix.reindex (e).symm (e).symm ((U.val⁻¹ * retainedGroup t q p).val) = 1 := by
    have he := retained_blocks t q p
    change _ = Matrix.fromBlocks (leadingScalar k q (0 : Fin m → ℝ)).val
      (firstRectangle k q (0 : Fin k → ℂ) * (1 : M m m)) 0 (trailingBlock t q p).val at he
    rw [hS, hX] at he
    have hD : trailingBlock t q p = 1 := by
      simp only [trailingBlock, p, logTorus_at_zero, OneMemClass.coe_one, mul_one]
    rw [hD, Units.val_one, Units.val_one, Matrix.fromBlocks_one] at he
    exact he
  have h' : U.val⁻¹ * retainedGroup t q p = 1 := by
    apply Units.ext
    apply (Matrix.reindex (e).symm (e).symm).injective
    rw [h, Units.val_one]
    exact (map_one (Matrix.reindexRingEquiv ℂ (e).symm)).symm
  exact eq_mul_of_inv_mul_eq h' |>.trans (mul_one _)

private theorem block_unitary_of_tailRows (U : K n) (hU : tailRows t q U.val.val = selectTail t q) :
    ∃ u : K k, U.val = rankInclusion m u.val := by
  let B := U.val.val
  have hRow (j : Fin m) (i : Fin n) : B (trail j) i = (1 : M n n) (trail j) i :=
    congrFun (congrFun hU j) i
  have hCol (i : Fin n) (j : Fin m) : B i (trail j) = (1 : M n n) i (trail j) := by
    have h := congrFun (congrFun (mul_conjTranspose_one U) i) (trail j)
    change (B * Bᴴ) i (trail j) = (1 : M n n) i (trail j) at h
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, hRow, Matrix.one_apply, apply_ite star,
      star_one, star_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using h
  let A : M k k := fun i j => B (lead i) (lead j)
  have hB : Matrix.reindex (e).symm (e).symm B = Matrix.fromBlocks A 0 0 (1 : M m m) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j
    · rfl
    · change B (lead i) (trail j) = _
      rw [hCol, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, Matrix.one_apply_ne]
      intro h
      have hh := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at hh
      omega
    · change B (trail i) (lead j) = 0
      rw [hRow]
      exact selectTail_entry_left t q i j
    · change B (trail i) (trail j) = (1 : M m m) i j
      rw [hRow]
      exact selectTail_entry_right t q i j
  have hA : A ∈ Matrix.unitaryGroup (Fin k) ℂ := by
    apply Matrix.mem_unitaryGroup_iff.mpr
    let r := Matrix.reindexRingEquiv ℂ (e).symm
    have h : r B * (r B)ᴴ = 1 := by
      rw [show (r B)ᴴ = r Bᴴ from rfl, ← map_mul, show B * Bᴴ = 1 from mul_conjTranspose_one U, map_one]
    change Matrix.reindex (e).symm (e).symm B * (Matrix.reindex (e).symm (e).symm B)ᴴ = _ at h
    rw [hB, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply] at h
    ext i j
    change (A * Aᴴ) i j = _
    have hi := congrFun (congrFun h (.inl i)) (.inl j)
    simpa only [Matrix.fromBlocks_apply₁₁, Matrix.conjTranspose_zero, Matrix.zero_mul, add_zero,
      Matrix.one_apply, Sum.inl.injEq] using hi
  let u : K k := ⟨Unitary.toUnits ⟨A, hA⟩, hA⟩
  refine ⟨u, Units.ext ?_⟩
  apply (Matrix.reindex (e).symm (e).symm).injective
  refine hB.trans ?_
  ext i j
  change _ = (Matrix.fromBlocks A 0 0 (1 : M m m)) ((e).symm (e i)) ((e).symm (e j))
  simp only [Equiv.symm_apply_apply]

/-- As the observed columns tend to their values at the identity, a subsequence of
retained points tends to a point with only an embedded leading unitary matrix. -/
def ComplexGapTailObservationStatement : Prop :=
  ∀ p : ℕ → P, Tendsto (fun i => tailObservation t q (p i)) atTop (𝓝 (standardTailObservation t q)) →
    ∃ (u : K k) (x : P) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (p ∘ φ) atTop (𝓝 x) ∧
      retainedGroup t q x = rankInclusion m u.val

private theorem continuous_matGram {i j : Type} [Fintype j] :
    Continuous (fun A : Matrix i j ℂ => A * Aᴴ) :=
  continuous_id.matrix_mul (continuous_matrix fun i j => (continuous_id.matrix_elem j i).star)

private theorem tendsto_matrix_mul {l i j : Type} [Fintype i]
    {f : ℕ → Matrix l i ℂ} {g : ℕ → Matrix i j ℂ} {F : Matrix l i ℂ} {G₀ : Matrix i j ℂ}
    (hf : Tendsto f atTop (𝓝 F)) (hg : Tendsto g atTop (𝓝 G₀)) :
    Tendsto (fun a => f a * g a) atTop (𝓝 (F * G₀)) := by
  apply tendsto_pi_nhds.mpr
  intro l₀
  apply tendsto_pi_nhds.mpr
  intro j₀
  simp only [Matrix.mul_apply]
  exact tendsto_finsetSum _ fun i₀ _ =>
    ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hf l₀)) i₀).mul
      ((tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hg i₀)) j₀)

set_option maxHeartbeats 2700000 in
theorem complexGapTailObservation : ComplexGapTailObservationStatement t q := by
  intro p hp
  obtain ⟨U, φ, hφ, hU⟩ := CompactSpace.tendsto_subseq (fun i => (p i).1.1.2)
  let z := p ∘ φ
  have ho := hp.comp hφ.tendsto_atTop
  let R (x : P) := tailRows t q (retainedGroup t q x)⁻¹.val
  let A (x : P) := (trailingBlock t q x)⁻¹.val
  let C (i : ℕ) := (z i).1.1.2.val.val
  let C₀ := U.val.val
  let rowView (X : Fin (q + 2) → Vec) : M m n := fun i j => X i.succ j
  have hRow : Continuous rowView := continuous_matrix fun i j => (continuous_apply j).comp (continuous_apply i.succ)
  have hR : Tendsto (fun i => R (z i)) atTop (𝓝 (selectTail t q)) :=
    hRow.continuousAt.tendsto.comp ho
  have hC : Tendsto C atTop (𝓝 C₀) := (Units.continuous_val.comp continuous_subtype_val).continuousAt.tendsto.comp hU
  let B := selectTail t q * C₀
  have hMul : Tendsto (fun i => R (z i) * C i) atTop (𝓝 B) :=
    tendsto_matrix_mul (l := Fin m) (i := Fin n) (j := Fin n) hR hC
  let lastSquare (M₀ : M m n) : M m m := fun i j => M₀ i (trail j)
  have hLast : Continuous lastSquare := continuous_matrix fun i j => continuous_id.matrix_elem i (trail j)
  let L := lastSquare B
  have he (i : ℕ) : lastSquare (R (z i) * C i) = A (z i) := by
    funext j l
    change (R (z i) * C i) j (trail l) = _
    rw [show R (z i) * C i = A (z i) * selectTail t q from multiply_inverseRows t q (z i), mul_selectTail_right]
  have hA : Tendsto (fun i => A (z i)) atTop (𝓝 L) := by
    simpa only [Function.comp_def, he] using hLast.continuousAt.tendsto.comp hMul
  have hGramR := (continuous_matGram (i := Fin m) (j := Fin n)).continuousAt.tendsto.comp hR
  have hGramA := (continuous_matGram (i := Fin m) (j := Fin m)).continuousAt.tendsto.comp hA
  have hUnit : L * Lᴴ = 1 := by
    have he : (fun i => R (z i) * (R (z i))ᴴ) = fun i => A (z i) * (A (z i))ᴴ :=
      funext fun i => tailGram t q (z i)
    change Tendsto (fun i => R (z i) * (R (z i))ᴴ) atTop (𝓝 (selectTail t q * (selectTail t q)ᴴ)) at hGramR
    rw [selectTail_mul_conjTranspose, he] at hGramR
    exact tendsto_nhds_unique hGramA hGramR
  have hLij (i j : Fin m) : Tendsto (fun a => A (z a) i j) atTop (𝓝 (L i j)) :=
    (continuous_id.matrix_elem i j).continuousAt.tendsto.comp hA
  have hUpper : L.IsUpperTriangular := by
    intro i j hij
    exact tendsto_nhds_unique (hLij i j) (by simpa only [A, trailingInv_triangular t q _ hij] using
      (tendsto_const_nhds (x := (0 : ℂ))))
  have hLu : L ∈ Matrix.unitaryGroup (Fin m) ℂ := Matrix.mem_unitaryGroup_iff.mpr hUnit
  have hOff := offDiag_eq_zero_of_upper_unitary hLu hUpper
  have hL₁ : L = 1 := by
    ext i j
    by_cases h : i = j
    · subst j
      have hre := Complex.continuous_re.continuousAt.tendsto.comp (hLij i i)
      have him := Complex.continuous_im.continuousAt.tendsto.comp (hLij i i)
      have hIm : (L i i).im = 0 := tendsto_nhds_unique him (by
        simpa only [Function.comp_def, A, trailingInv_diag, Complex.ofReal_im] using
          (tendsto_const_nhds (x := (0 : ℝ))))
      have hRe : 0 ≤ (L i i).re := ge_of_tendsto hre (.of_forall fun a => by
        change 0 ≤ ((trailingBlock t q (z a))⁻¹.val i i).re
        rw [trailingInv_diag, Complex.ofReal_re]
        positivity)
      have hs : L i i = ((L i i).re : ℂ) := by apply Complex.ext <;> simp [hIm]
      rw [hs, Matrix.one_apply_eq]
      have hn := norm_diag_eq_one_of_unitary hLu hOff i
      rw [hs, Complex.norm_real, Real.norm_of_nonneg hRe] at hn
      exact_mod_cast hn
    · rw [hOff i j h, Matrix.one_apply_ne h]
  rw [hL₁] at hA
  have hB : B = selectTail t q := by
    have hc : Continuous (fun D : M m m => D * selectTail t q) := continuous_id.matrix_mul continuous_const
    have ht := hc.continuousAt.tendsto.comp hA
    have he : (fun i => R (z i) * C i) = fun i => A (z i) * selectTail t q :=
      funext fun i => multiply_inverseRows t q (z i)
    rw [he] at hMul
    exact (tendsto_nhds_unique hMul ht).trans (Matrix.one_mul _)
  have hTail : tailRows t q U.val.val = selectTail t q := by
    change selectTail t q * U.val.val = selectTail t q at hB
    rw [show tailRows t q U.val.val = selectTail t q * U.val.val by
      rw [selectTail, ← tailRows_mul, Matrix.one_mul]]
    exact hB
  have hy : Tendsto (fun i => (z i).1.1.1) atTop (𝓝 (0 : Fin m → ℝ)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have ht := Complex.continuous_re.continuousAt.tendsto.comp
      ((continuous_id.matrix_elem j j).continuousAt.tendsto.comp hA)
    have he : Tendsto (fun i => Real.exp (-((z i).1.1.1 j))) atTop (𝓝 1) := by
      simpa only [Function.comp_def, id_eq, A, trailingInv_diag, Complex.ofReal_re, Matrix.one_apply_eq, Complex.one_re] using ht
    have hl := (Real.continuousAt_log one_ne_zero).tendsto.comp he
    simpa only [Function.comp_def, Real.log_exp, Real.log_one, neg_neg, neg_zero, Pi.zero_apply] using hl.neg
  have hD₁ : Tendsto (fun i => (logTorus (z i).1.1.1).val) atTop (𝓝 (1 : M m m)) := by
    simpa only [Function.comp_def, logTorus_at_zero, Units.val_one] using
      (Units.continuous_val.comp continuous_logTorus).continuousAt.tendsto.comp hy
  have hZa : Tendsto (fun i => ((z i).2⁻¹).val.val) atTop (𝓝 (1 : M m m)) := by
    have he (i : ℕ) : A (z i) * (logTorus (z i).1.1.1).val = ((z i).2⁻¹).val.val := by
      change (logTorus (z i).1.1.1 * (z i).2.val)⁻¹.val * (logTorus (z i).1.1.1).val = _
      rw [← Units.val_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one, Subgroup.coe_inv]
    simpa only [he, mul_one] using hA.mul hD₁
  have hZinv : Tendsto (fun i => (z i).2⁻¹) atTop (𝓝 (1 : Langlands.GeneralLinear.upperUnipotent m ℂ)) := by
    apply ((Units.isOpenEmbedding_val (R := M m m)).isEmbedding.comp IsEmbedding.subtypeVal).tendsto_nhds_iff.mpr
    exact hZa
  have hZ : Tendsto (fun i => (z i).2) atTop (𝓝 (1 : Langlands.GeneralLinear.upperUnipotent m ℂ)) := by simpa only [inv_inv, inv_one] using hZinv.inv
  have hKinv : Tendsto (fun i => ((z i).1.1.2.val)⁻¹.val) atTop (𝓝 (U.val⁻¹.val)) :=
    (Units.continuous_val.comp (continuous_subtype_val.inv)).continuousAt.tendsto.comp hU
  have hBasis : Tendsto (fun i => tailColumn k q (retainedGroup t q (z i)) 0) atTop (𝓝 (firstBasis t q)) :=
    (continuous_apply (0 : Fin (q + 2))).continuousAt.tendsto.comp ho
  have hc₀ : Continuous (fun p : M n n × Vec => p.1 *ᵥ p.2) := continuous_fst.matrix_mulVec continuous_snd
  have hHead : Tendsto (fun i => (z i).1.2) atTop (𝓝 (0 : Fin k → ℂ)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have h := (continuous_apply (lead j)).continuousAt.tendsto.comp (hc₀.continuousAt.tendsto.comp (hKinv.prodMk_nhds hBasis))
    have hv : (U.val⁻¹.val *ᵥ firstBasis t q) (lead j) = 0 := by
      unfold firstBasis
      rw [unitary_inverse_val, Matrix.mulVec, dotProduct]
      simp only [Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
        Matrix.conjTranspose_apply]
      have hh : U.val.val (trail (0 : Fin m)) (lead j) = 0 := by
        exact (congrFun (congrFun hTail 0) _).trans (selectTail_entry_left t q 0 j)
      rw [hh, star_zero]
    simpa only [Function.comp_def, head_of_firstColumn, hv, Pi.zero_apply] using h
  obtain ⟨u, hu⟩ := block_unitary_of_tailRows t q U hTail
  exact ⟨u, (((0, U), 0), 1), φ, hφ, ((hy.prodMk_nhds hU).prodMk_nhds hHead).prodMk_nhds hZ,
    (zero_retained t q U).trans hu⟩

/-- The identity tuple has the standard observed columns. -/
theorem standardTailObservation_mem_range : standardTailObservation t q ∈ range (tailObservation t q) := by
  refine ⟨(((0, 1), 0), 1), ?_⟩
  unfold tailObservation
  rw [zero_retained, Subgroup.coe_one]
  rfl

/-- An open set containing every retained point over an embedded leading unitary
contains the preimage of some neighborhood of the standard observation. -/
theorem exists_tailObservation_neighborhood (S : Set P) (hS : IsOpen S)
    (h : ∀ p : P, (∃ u : K k, retainedGroup t q p = rankInclusion m u.val) → p ∈ S) :
    ∃ V : Set (Fin (q + 2) → Vec), IsOpen V ∧ standardTailObservation t q ∈ V ∧ tailObservation t q ⁻¹' V ⊆ S := by
  let V := (closure (tailObservation t q '' Sᶜ))ᶜ
  have hV : standardTailObservation t q ∈ V := by
    intro hn
    obtain ⟨x, hx, ht⟩ := mem_closure_iff_seq_limit.mp hn
    choose p hp hpx using hx
    have he : (fun i => tailObservation t q (p i)) = x := funext hpx
    obtain ⟨u, x₀, φ, hφ, hφx, hCenter⟩ := complexGapTailObservation t q p (he.symm ▸ ht)
    have hs : ∀ᶠ i in atTop, p (φ i) ∈ S := hφx (hS.mem_nhds (h x₀ ⟨u, hCenter⟩))
    exact (hs.and (.of_forall fun i => hp (φ i))).exists.elim fun _ hh => hh.2 hh.1
  exact ⟨V, isClosed_closure.isOpen_compl, hV, fun p hp => by
    by_contra hnp
    exact hp (subset_closure ⟨p, hnp, rfl⟩)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGapRetained

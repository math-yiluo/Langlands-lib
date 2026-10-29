import Langlands.Group.GL.UpperBruhatCoordinatesStatement
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.Group
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Instances.Matrix

/-!
# Proof of the actual upper Bruhat cell coordinate homeomorphisms

Coordinates on the cell are recovered by column-wise linear solves with principal
blocks whose determinants are nonzero on the cell. See the paired Markdown.
-/

namespace Langlands.GeneralLinear

universe u

namespace UpperBruhatCoordinates

open Matrix

section LinearAlgebra

variable {K : Type u} [Field K] {n : ℕ}

/-- Column `c` is `e c` plus the vector on `{k | Q c k}` that solves the rows
`{r | Q c r}` of `A * Y = 0` in column `c`, using the principal block of `A`. -/
noncomputable def columnSolve (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    (A : Matrix (Fin n) (Fin n) K) : Matrix (Fin n) (Fin n) K :=
  fun k c =>
    if h : Q c k then
      -(((A.toBlock (Q c) (Q c))⁻¹ *ᵥ fun r : {r // Q c r} => A r c) ⟨k, h⟩)
    else if k = c then 1 else 0

theorem columnSolve_apply_of_pos (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    (A : Matrix (Fin n) (Fin n) K) {k c : Fin n} (h : Q c k) :
    columnSolve Q A k c =
      -(((A.toBlock (Q c) (Q c))⁻¹ *ᵥ fun r : {r // Q c r} => A r c) ⟨k, h⟩) := by
  simp only [columnSolve, h, ↓reduceDIte]

theorem columnSolve_apply_of_neg (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    (A : Matrix (Fin n) (Fin n) K) {k c : Fin n} (h : ¬ Q c k) :
    columnSolve Q A k c = if k = c then 1 else 0 := by
  simp only [columnSolve, h, ↓reduceDIte]

/-- A column equal to `e c` off a predicate splits the corresponding product entry. -/
theorem mul_apply_of_support (P : Fin n → Prop) [DecidablePred P]
    (A Y : Matrix (Fin n) (Fin n) K) {c : Fin n} (hc : ¬ P c)
    (hY : ∀ k, ¬ P k → Y k c = if k = c then 1 else 0) (r : Fin n) :
    (A * Y) r c = (∑ k : {k // P k}, A r k * Y k c) + A r c := by
  rw [Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype P (fun k => A r k * Y k c)]
  congr 1
  rw [Finset.sum_eq_single (⟨c, hc⟩ : {k // ¬ P k})]
  · rw [hY c hc]
    simp
  · intro k _ hk
    have hkc : k.val ≠ c := fun h => hk (Subtype.ext h)
    rw [hY k k.2]
    simp [hkc]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The column solve annihilates the prescribed rows when the principal block is invertible. -/
theorem mul_columnSolve_apply (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    (A : Matrix (Fin n) (Fin n) K) {c : Fin n} (hc : ¬ Q c c)
    (hdet : (A.toBlock (Q c) (Q c)).det ≠ 0) {r : Fin n} (hr : Q c r) :
    (A * columnSolve Q A) r c = 0 := by
  rw [mul_apply_of_support (Q c) A _ hc (fun k hk => columnSolve_apply_of_neg Q A hk) r]
  have hx : (∑ k : {k // Q c k}, A r k * columnSolve Q A k c) =
      ((A.toBlock (Q c) (Q c)) *ᵥ
        -((A.toBlock (Q c) (Q c))⁻¹ *ᵥ fun r : {r // Q c r} => A r c)) ⟨r, hr⟩ := by
    simp only [mulVec, dotProduct, toBlock_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [columnSolve_apply_of_pos Q A k.2]
    rfl
  rw [hx, Matrix.mulVec_neg, Matrix.mulVec_mulVec,
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
  simp

/-- Uniqueness of the column solve. -/
theorem eq_columnSolve (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    (A Y : Matrix (Fin n) (Fin n) K) (hQ : ∀ c, ¬ Q c c)
    (hdet : ∀ c, (A.toBlock (Q c) (Q c)).det ≠ 0)
    (hY : ∀ k c, ¬ Q c k → Y k c = if k = c then 1 else 0)
    (hAY : ∀ r c, Q c r → (A * Y) r c = 0) :
    Y = columnSolve Q A := by
  ext k c
  by_cases hk : Q c k
  · rw [columnSolve_apply_of_pos Q A hk]
    have hx : (A.toBlock (Q c) (Q c)) *ᵥ (fun r : {r // Q c r} => Y r c) =
        -(fun r : {r // Q c r} => A r c) := by
      funext r
      have h := hAY r c r.2
      rw [mul_apply_of_support (Q c) A Y (hQ c) (fun k hk => hY k c hk) r] at h
      simp only [mulVec, dotProduct, toBlock_apply, Pi.neg_apply]
      exact eq_neg_of_add_eq_zero_left h
    have hsol : (fun r : {r // Q c r} => Y r c) =
        -((A.toBlock (Q c) (Q c))⁻¹ *ᵥ fun r : {r // Q c r} => A r c) := by
      rw [← Matrix.mulVec_neg, ← hx, Matrix.mulVec_mulVec,
        Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet c)), Matrix.one_mulVec]
    exact congrFun hsol ⟨k, hk⟩
  · rw [columnSolve_apply_of_neg Q A hk, hY k c hk]

/-- A principal block of a product whose right factor has no entries leaving the block. -/
theorem toBlock_mul_of_support (P : Fin n → Prop) [DecidablePred P]
    (A Y : Matrix (Fin n) (Fin n) K) (hY : ∀ k t, ¬ P k → P t → Y k t = 0) :
    (A * Y).toBlock P P = A.toBlock P P * Y.toBlock P P := by
  rw [Matrix.toBlock_mul_eq_add P P P A Y]
  have h0 : Y.toBlock (fun i => ¬ P i) P = 0 := by
    ext k t
    exact hY k t k.2 t.2
  rw [h0, Matrix.mul_zero, add_zero]

/-- Every principal block of an upper triangular matrix with nonzero diagonal is invertible. -/
theorem det_toBlock_ne_zero_of_upper (A : Matrix (Fin n) (Fin n) K) (hA : A.IsUpperTriangular)
    (hd : ∀ i, A i i ≠ 0) (P : Fin n → Prop) [DecidablePred P] :
    (A.toBlock P P).det ≠ 0 := by
  have hT : (A.toBlock P P).IsUpperTriangular := fun i j hij => hA (Subtype.coe_lt_coe.mpr hij)
  rw [Matrix.det_of_isUpperTriangular hT]
  exact Finset.prod_ne_zero_iff.mpr fun i _ => hd i

/-- An invertible upper triangular matrix has nonzero diagonal entries. -/
theorem diag_ne_zero_of_upper (b : Langlands.GeneralLinear n K) (hb : b.val.IsUpperTriangular)
    (i : Fin n) : b.val i i ≠ 0 := by
  intro h0
  apply Matrix.GeneralLinearGroup.det_ne_zero b
  rw [Matrix.det_of_isUpperTriangular hb]
  exact Finset.prod_eq_zero (Finset.mem_univ i) h0

section Topology

variable [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- Matrix inversion is continuous along a continuous family of invertible matrices. -/
theorem continuous_matrix_inv_of_det_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {X : Type*} [TopologicalSpace X] {A : X → Matrix ι ι K} (hA : Continuous A)
    (h : ∀ x, (A x).det ≠ 0) : Continuous fun x => (A x)⁻¹ :=
  continuous_iff_continuousAt.mpr fun x =>
    (continuousAt_matrix_inv (A x) (by
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (h x))).comp hA.continuousAt

/-- Over a topological field, continuity into the general linear group only needs the matrix
values. -/
theorem continuous_generalLinear_of_val {X : Type*} [TopologicalSpace X]
    {f : X → Langlands.GeneralLinear n K} (hf : Continuous fun x => (f x).val) :
    Continuous f := by
  refine Units.continuous_iff.mpr ⟨hf, ?_⟩
  have h : (fun x => ((f x)⁻¹ : Langlands.GeneralLinear n K).val) =
      fun x => ((f x).val)⁻¹ := by
    funext x
    exact Matrix.coe_units_inv (f x)
  rw [h]
  exact continuous_matrix_inv_of_det_ne_zero hf fun x =>
    Matrix.GeneralLinearGroup.det_ne_zero (f x)

/-- The column solve is continuous where all its principal blocks are invertible. -/
theorem continuous_columnSolve (Q : Fin n → Fin n → Prop) [∀ c, DecidablePred (Q c)]
    {X : Type*} [TopologicalSpace X] {A : X → Matrix (Fin n) (Fin n) K} (hA : Continuous A)
    (hdet : ∀ x c, ((A x).toBlock (Q c) (Q c)).det ≠ 0) :
    Continuous fun x => columnSolve Q (A x) := by
  refine continuous_matrix fun k c => ?_
  by_cases hk : Q c k
  · simp only [columnSolve_apply_of_pos Q _ hk]
    have hB : Continuous fun x => (A x).toBlock (Q c) (Q c) :=
      continuous_matrix fun i j => by simpa only [toBlock_apply] using hA.matrix_elem i.val j.val
    have h1 : Continuous fun x => ((A x).toBlock (Q c) (Q c))⁻¹ :=
      continuous_matrix_inv_of_det_ne_zero hB fun x => hdet x c
    exact ((continuous_apply _).comp
      (h1.matrix_mulVec (continuous_pi fun r => hA.matrix_elem r.val c))).neg
  · simp only [columnSolve_apply_of_neg Q _ hk]
    exact continuous_const

end Topology

end LinearAlgebra

section Cell

variable {K : Type u} [Field K] {n : ℕ} (w : Equiv.Perm (Fin n))

/-- An upper triangular matrix that is lower unipotent is the identity. -/
theorem eq_one_of_upper_of_lower {g : Langlands.GeneralLinear n K}
    (hB : g ∈ upperTriangularSubgroup n K) (hL : g ∈ lowerUnipotent n K) : g = 1 := by
  have hU : g ∈ upperUnipotent n K := ⟨hB, ((mem_lowerUnipotent_iff n K g).mp hL).2⟩
  have h : g ∈ upperUnipotent n K ⊓ lowerUnipotent n K := ⟨hU, hL⟩
  rwa [upperUnipotent_inf_lowerUnipotent, Subgroup.mem_bot] at h

/-- The coordinates `(b, v)` of a cell element are unique. -/
theorem upperBruhatCellMap_injective : Function.Injective (upperBruhatCellMap n K w) := by
  rintro ⟨b, v⟩ ⟨b', v'⟩ h
  have h' : b.val * permutation n K w * v.val = b'.val * permutation n K w * v'.val :=
    congrArg Subtype.val h
  have hconj : b'.val⁻¹ * b.val =
      permutation n K w * (v'.val * v.val⁻¹) * (permutation n K w)⁻¹ := by
    calc b'.val⁻¹ * b.val
        = b'.val⁻¹ * (b.val * permutation n K w * v.val) * v.val⁻¹ *
            (permutation n K w)⁻¹ := by group
      _ = b'.val⁻¹ * (b'.val * permutation n K w * v'.val) * v.val⁻¹ *
            (permutation n K w)⁻¹ := by rw [h']
      _ = permutation n K w * (v'.val * v.val⁻¹) * (permutation n K w)⁻¹ := by group
  have hN : v'.val * v.val⁻¹ ∈ permutationUnipotentMinus n K w :=
    mul_mem v'.property (inv_mem v.property)
  have hL : b'.val⁻¹ * b.val ∈ lowerUnipotent n K := by
    rw [hconj]
    exact ((mem_permutationUnipotentMinus_iff n K w _).mp hN).2
  have hone := eq_one_of_upper_of_lower (mul_mem (inv_mem b'.property) b.property) hL
  have hb : b'.val = b.val := inv_mul_eq_one.mp hone
  have hv : v.val = v'.val := by
    rw [← hb] at h'
    exact mul_left_cancel h'
  exact Prod.ext (Subtype.ext hb.symm) (Subtype.ext hv)

/-- Clearing the entries of an upper triangular `b` that `w` moves below the diagonal by a
right factor in `U_w⁻`, solved column by column. -/
theorem exists_minus_conj_upper (b : Langlands.GeneralLinear n K)
    (hb : b ∈ upperTriangularSubgroup n K) :
    ∃ y ∈ permutationUnipotentMinus n K w,
      permutation n K w * (b * y) * (permutation n K w)⁻¹ ∈ upperTriangularSubgroup n K := by
  let Q : Fin n → Fin n → Prop := fun c k => k < c ∧ w c < w k
  let Y := columnSolve Q b.val
  have hQc : ∀ c, ¬ Q c c := fun c h => lt_irrefl c h.1
  have hYoff : ∀ k c, ¬ Q c k → Y k c = if k = c then 1 else 0 :=
    fun k c h => columnSolve_apply_of_neg Q _ h
  have hYup : Y.IsUpperTriangular := by
    intro k c hck
    have hkc : k ≠ c := ne_of_gt hck
    rw [hYoff k c (fun h => lt_asymm h.1 hck)]
    simp [hkc]
  have hYdiag : ∀ i, Y i i = 1 := fun i => by
    rw [hYoff i i (hQc i)]
    simp
  have hdetY : Y.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hYup]
    simp [hYdiag]
  let y := Matrix.GeneralLinearGroup.mkOfDetNeZero Y hdetY
  have hyN : y ∈ permutationUnipotentMinus n K w := by
    rw [mem_permutationUnipotentMinus_iff_entries]
    refine ⟨⟨hYup, hYdiag⟩, fun i j hij => ?_⟩
    change Y i j = 0
    rw [hYoff i j (fun h => lt_asymm hij h.2)]
    simp [ne_of_apply_ne w (ne_of_lt hij)]
  refine ⟨y, hyN, ?_⟩
  rw [mem_upperTriangularSubgroup_iff]
  intro i j hji
  rw [permutation_conjugate_entry]
  change (b.val * Y) (w⁻¹ i) (w⁻¹ j) = 0
  have hbU : b.val.IsUpperTriangular := hb
  rcases lt_trichotomy (w⁻¹ j) (w⁻¹ i) with h | h | h
  · exact (hbU.mul hYup) h
  · exact absurd (by simpa using congrArg w h) (ne_of_lt hji)
  · refine mul_columnSolve_apply Q b.val (hQc _) ?_ ⟨h, by simpa using hji⟩
    exact det_toBlock_ne_zero_of_upper b.val hbU (diag_ne_zero_of_upper b hbU) _

/-- Every element of the actual cell has coordinates `(b, v)`. -/
theorem upperBruhatCellMap_surjective : Function.Surjective (upperBruhatCellMap n K w) := by
  rintro ⟨g, b₁, hb₁, b₂, hb₂, rfl⟩
  obtain ⟨y, hy, hc⟩ := exists_minus_conj_upper w b₂ hb₂
  refine ⟨(⟨b₁ * (permutation n K w * (b₂ * y) * (permutation n K w)⁻¹), mul_mem hb₁ hc⟩,
    ⟨y⁻¹, inv_mem hy⟩), ?_⟩
  apply Subtype.ext
  simp only [upperBruhatCellMap_val]
  group

/-- The coordinate map as an equivalence onto the cell. -/
noncomputable def cellEquiv :
    (upperTriangularSubgroup n K × permutationUnipotentMinus n K w) ≃ UpperBruhatCell n K w :=
  Equiv.ofBijective _ ⟨upperBruhatCellMap_injective w, upperBruhatCellMap_surjective w⟩

theorem cellEquiv_apply (x : upperTriangularSubgroup n K × permutationUnipotentMinus n K w) :
    cellEquiv w x = upperBruhatCellMap n K w x :=
  rfl

theorem upperBruhatCellMap_cellEquiv_symm (g : UpperBruhatCell n K w) :
    upperBruhatCellMap n K w ((cellEquiv w).symm g) = g :=
  (cellEquiv w).apply_symm_apply g

/-- The conjugated inverse of the `U_w⁻` coordinate is lower unipotent. -/
theorem recover_mem_lowerUnipotent (v : permutationUnipotentMinus n K w) :
    permutation n K w * v.val⁻¹ * (permutation n K w)⁻¹ ∈ lowerUnipotent n K :=
  ((mem_permutationUnipotentMinus_iff n K w _).mp (inv_mem v.property)).2

/-- Right multiplication of `g * p⁻¹` by the conjugated inverse recovers `b`. -/
theorem recover_mul (x : upperTriangularSubgroup n K × permutationUnipotentMinus n K w) :
    ((upperBruhatCellMap n K w x).val * (permutation n K w)⁻¹).val *
        (permutation n K w * x.2.val⁻¹ * (permutation n K w)⁻¹).val = x.1.val.val := by
  rw [← Units.val_mul, upperBruhatCellMap_val]
  congr 1
  group

/-- The lower right principal blocks of `g * p⁻¹` are invertible on the cell. -/
theorem det_toBlock_recover_ne_zero
    (x : upperTriangularSubgroup n K × permutationUnipotentMinus n K w) (c : Fin n) :
    (((upperBruhatCellMap n K w x).val * (permutation n K w)⁻¹).val.toBlock
      (fun k => c < k) (fun k => c < k)).det ≠ 0 := by
  have hL := (mem_lowerUnipotent_iff n K _).mp (recover_mem_lowerUnipotent w x.2)
  have hblock := toBlock_mul_of_support (fun k => c < k)
    ((upperBruhatCellMap n K w x).val * (permutation n K w)⁻¹).val
    (permutation n K w * x.2.val⁻¹ * (permutation n K w)⁻¹).val
    (fun k t hk ht => hL.1 k t (lt_of_le_of_lt (not_lt.mp hk) ht))
  rw [recover_mul] at hblock
  have hb : x.1.val.val.IsUpperTriangular := x.1.property
  have hdet := det_toBlock_ne_zero_of_upper x.1.val.val hb (diag_ne_zero_of_upper x.1.val hb)
    (fun k => c < k)
  rw [hblock, Matrix.det_mul] at hdet
  exact left_ne_zero_of_mul hdet

/-- The conjugated inverse of the `U_w⁻` coordinate is the lower column solve of `g * p⁻¹`. -/
theorem recover_eq (x : upperTriangularSubgroup n K × permutationUnipotentMinus n K w) :
    (permutation n K w * x.2.val⁻¹ * (permutation n K w)⁻¹).val =
      columnSolve (fun c k => c < k)
        ((upperBruhatCellMap n K w x).val * (permutation n K w)⁻¹).val := by
  have hL := (mem_lowerUnipotent_iff n K _).mp (recover_mem_lowerUnipotent w x.2)
  have hb : x.1.val.val.IsUpperTriangular := x.1.property
  refine eq_columnSolve (fun c k => c < k) _ _ (fun c => lt_irrefl c)
    (det_toBlock_recover_ne_zero w x) (fun k c hk => ?_) (fun r c hr => ?_)
  · rcases eq_or_ne k c with rfl | hne
    · rw [hL.2 k]
      simp
    · rw [hL.1 k c (lt_of_le_of_ne (not_lt.mp hk) hne)]
      simp [hne]
  · rw [recover_mul]
    exact hb hr

section Topology

variable [TopologicalSpace K] [IsTopologicalDivisionRing K]

/-- The inverse of the coordinate equivalence is continuous. -/
theorem continuous_cellEquiv_symm : Continuous (cellEquiv w (K := K)).symm := by
  have hM : Continuous fun g : UpperBruhatCell n K w => (g.val * (permutation n K w)⁻¹).val :=
    Units.continuous_val.comp (continuous_subtype_val.mul continuous_const)
  have hdet : ∀ (g : UpperBruhatCell n K w) (c : Fin n),
      ((g.val * (permutation n K w)⁻¹).val.toBlock (fun k => c < k) (fun k => c < k)).det ≠ 0 := by
    intro g c
    have h := det_toBlock_recover_ne_zero w ((cellEquiv w).symm g) c
    rwa [upperBruhatCellMap_cellEquiv_symm] at h
  have hS := continuous_columnSolve (fun c k => c < k) hM hdet
  have hvinv : Continuous fun g => (((cellEquiv w).symm g).2.val⁻¹ :
      Langlands.GeneralLinear n K) := by
    apply continuous_generalLinear_of_val
    have h : (fun g => ((((cellEquiv w).symm g).2.val⁻¹ : Langlands.GeneralLinear n K)).val) =
        fun g : UpperBruhatCell n K w => ((permutation n K w)⁻¹).val *
          columnSolve (fun c k => c < k) (g.val * (permutation n K w)⁻¹).val *
            (permutation n K w).val := by
      funext g
      have hr := recover_eq w ((cellEquiv w).symm g)
      rw [upperBruhatCellMap_cellEquiv_symm] at hr
      rw [← hr, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [h]
    exact (continuous_const.mul hS).mul continuous_const
  have hv' : Continuous fun g => ((cellEquiv w (K := K)).symm g).2.val := by
    simpa only [Function.comp_def, inv_inv] using continuous_inv.comp hvinv
  have hv : Continuous fun g => ((cellEquiv w).symm g).2 :=
    Topology.IsInducing.subtypeVal.continuous_iff.mpr hv'
  have hb : Continuous fun g => ((cellEquiv w (K := K)).symm g).1 := by
    have h : (fun g => ((cellEquiv w (K := K)).symm g).1.val) =
        fun g : UpperBruhatCell n K w =>
          g.val * ((cellEquiv w).symm g).2.val⁻¹ * (permutation n K w)⁻¹ := by
      funext g
      have hg := congrArg Subtype.val (upperBruhatCellMap_cellEquiv_symm w g)
      rw [upperBruhatCellMap_val] at hg
      rw [← hg]
      group
    refine Topology.IsInducing.subtypeVal.continuous_iff.mpr ?_
    change Continuous fun g => ((cellEquiv w (K := K)).symm g).1.val
    rw [h]
    exact (continuous_subtype_val.mul hvinv).mul continuous_const
  exact hb.prodMk hv

/-- Shalika's first coordinate homeomorphism `B × U_w⁻ ≃ₜ C_w`. -/
noncomputable def cellHomeomorph :
    (upperTriangularSubgroup n K × permutationUnipotentMinus n K w) ≃ₜ UpperBruhatCell n K w where
  toEquiv := cellEquiv w
  continuous_toFun := continuous_upperBruhatCellMap n K w
  continuous_invFun := continuous_cellEquiv_symm w

theorem cellHomeomorph_apply (x : upperTriangularSubgroup n K × permutationUnipotentMinus n K w) :
    cellHomeomorph w x = upperBruhatCellMap n K w x :=
  rfl

end Topology

/-- The diagonal entry of an upper triangular invertible matrix, as a unit. -/
noncomputable def diagUnit (b : upperTriangularSubgroup n K) (i : Fin n) : Kˣ :=
  Units.mk0 (b.val i i) (diag_ne_zero_of_upper b.val b.property i)

/-- Recombine `U` and a torus parameter, placing the torus to the left of `p`. -/
def torusSplitFun (x : upperUnipotent n K × (Fin n → Kˣ)) : upperTriangularSubgroup n K :=
  ⟨x.1.val * Iwasawa.diagonalUnits (fun i => x.2 (w⁻¹ i)),
    mul_mem (upperUnipotent_le_upperTriangular n K x.1.property)
      (diagonalUnits_mem_upperTriangular n _)⟩

/-- Split an upper triangular matrix into its unipotent part and permuted diagonal. -/
noncomputable def torusSplitInv (b : upperTriangularSubgroup n K) :
    upperUnipotent n K × (Fin n → Kˣ) :=
  (⟨b.val * Iwasawa.diagonalUnits (fun i => (diagUnit b i)⁻¹),
    mul_mem b.property (diagonalUnits_mem_upperTriangular n _), fun i => by
      change (b.val.val * Matrix.diagonal fun i => (((diagUnit b i)⁻¹ : Kˣ) : K)) i i = 1
      rw [Matrix.mul_diagonal, Units.val_inv_eq_inv_val, diagUnit, Units.val_mk0]
      exact mul_inv_cancel₀ (diag_ne_zero_of_upper b.val b.property i)⟩,
    fun j => diagUnit b (w j))

theorem diagUnit_torusSplitFun (x : upperUnipotent n K × (Fin n → Kˣ)) (i : Fin n) :
    diagUnit (torusSplitFun w x) i = x.2 (w⁻¹ i) := by
  apply Units.ext
  change (x.1.val.val * Matrix.diagonal fun i => ((x.2 (w⁻¹ i) : Kˣ) : K)) i i = _
  rw [Matrix.mul_diagonal, x.1.property.2 i, one_mul]

/-- The split `U × T ≃ B` with the torus parameter permuted by `w`. -/
noncomputable def torusSplitEquiv :
    (upperUnipotent n K × (Fin n → Kˣ)) ≃ upperTriangularSubgroup n K where
  toFun := torusSplitFun w
  invFun := torusSplitInv w
  left_inv x := by
    refine Prod.ext (Subtype.ext ?_) (funext fun j => ?_)
    · change x.1.val * Iwasawa.diagonalUnits (fun i => x.2 (w⁻¹ i)) *
        Iwasawa.diagonalUnits (fun i => (diagUnit (torusSplitFun w x) i)⁻¹) = x.1.val
      simp only [diagUnit_torusSplitFun]
      rw [mul_assoc, ← map_mul]
      have h1 : ((fun i => x.2 (w⁻¹ i)) * fun i => (x.2 (w⁻¹ i))⁻¹) = 1 := by
        funext i
        simp
      rw [h1, map_one, mul_one]
    · change diagUnit (torusSplitFun w x) (w j) = x.2 j
      rw [diagUnit_torusSplitFun]
      simp
  right_inv b := by
    apply Subtype.ext
    change b.val * Iwasawa.diagonalUnits (fun i => (diagUnit b i)⁻¹) *
      Iwasawa.diagonalUnits (fun i => diagUnit b (w (w⁻¹ i))) = b.val
    simp only [Equiv.Perm.coe_inv, Equiv.apply_symm_apply]
    rw [mul_assoc, ← map_mul]
    have h1 : ((fun i => (diagUnit b i)⁻¹) * fun i => diagUnit b i) = 1 := by
      funext i
      simp
    rw [h1, map_one, mul_one]

section Topology

variable [TopologicalSpace K] [IsTopologicalDivisionRing K]

theorem continuous_diagUnit (i : Fin n) :
    Continuous fun b : upperTriangularSubgroup n K => diagUnit b i :=
  Units.isEmbedding_val₀.continuous_iff.mpr
    ((Units.continuous_val.comp continuous_subtype_val).matrix_elem i i)

/-- The split `U × T ≃ₜ B`. -/
noncomputable def torusSplit :
    (upperUnipotent n K × (Fin n → Kˣ)) ≃ₜ upperTriangularSubgroup n K where
  toEquiv := torusSplitEquiv w
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    exact (continuous_subtype_val.comp continuous_fst).mul ((continuous_diagonalUnits n).comp
      (continuous_pi fun i => (continuous_apply (w⁻¹ i)).comp continuous_snd))
  continuous_invFun := by
    refine Continuous.prodMk (Continuous.subtype_mk ?_ _)
      (continuous_pi fun j => continuous_diagUnit (w j))
    exact continuous_subtype_val.mul ((continuous_diagonalUnits n).comp
      (continuous_pi fun i => (continuous_diagUnit i).inv))

/-- Shalika's torus coordinate homeomorphism `U × T × U_w⁻ ≃ₜ C_w`. -/
noncomputable def torusHomeomorph :
    (upperUnipotent n K × (Fin n → Kˣ) × permutationUnipotentMinus n K w) ≃ₜ
      UpperBruhatCell n K w :=
  (Homeomorph.prodAssoc _ _ _).symm.trans
    (((torusSplit w).prodCongr (Homeomorph.refl _)).trans (cellHomeomorph w))

theorem torusHomeomorph_apply_val
    (x : upperUnipotent n K × (Fin n → Kˣ) × permutationUnipotentMinus n K w) :
    (torusHomeomorph w x).val =
      x.1.val * permutation n K w * Iwasawa.diagonalUnits x.2.1 * x.2.2.val := by
  change x.1.val * Iwasawa.diagonalUnits (fun i => x.2.1 (w⁻¹ i)) * permutation n K w *
    x.2.2.val = _
  rw [mul_assoc x.1.val (permutation n K w), permutation_mul_diagonalUnits]
  simp only [mul_assoc]

end Topology

end Cell

end UpperBruhatCoordinates

/-- Shalika's two coordinate homeomorphisms on the actual upper Bruhat cell, over every
Hausdorff topological field, in every rank and for every permutation. -/
theorem upperBruhatCoordinates : UpperBruhatCoordinatesStatement.{u} := by
  intro K _ _ _ _ n w
  exact ⟨⟨UpperBruhatCoordinates.cellHomeomorph w, fun _ => rfl⟩,
    ⟨UpperBruhatCoordinates.torusHomeomorph w, UpperBruhatCoordinates.torusHomeomorph_apply_val w⟩⟩

end Langlands.GeneralLinear

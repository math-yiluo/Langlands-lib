import Langlands.Group.GL.Blocks
import Langlands.Group.GL.RankMaps
import Langlands.Group.GL.BlockModulus

/-! # Ordered two-block shapes for Shahidi induction -/

namespace Langlands.Shahidi

open GeneralLinear

universe u

/-- The standard ordered pair of positive block sizes, with total rank `m+n`. -/
abbrev twoBlocks (m n : ℕ) (hm : 0 < m) (hn : 0 < n) : BlockShape (m + n) where
  length := 2
  size := ![m, n]
  positive := by
    intro i
    fin_cases i <;> assumption
  sum_eq := by simp

variable {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

@[simp] theorem twoBlocks_index_first (i : Fin m) :
    (twoBlocks m n hm hn).index 0 i = i.castAdd n := by
  apply Fin.ext
  change ((twoBlocks m n hm hn).indexEquiv ⟨0, i⟩).val = i.val
  rw [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  simp

@[simp] theorem twoBlocks_index_second (i : Fin n) :
    (twoBlocks m n hm hn).index 1 i = i.natAdd m := by
  apply Fin.ext
  change ((twoBlocks m n hm hn).indexEquiv ⟨1, i⟩).val = m + i.val
  rw [BlockShape.indexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast,
    finSigmaFinEquiv_apply]
  change (∑ k : Fin 1, ![m, n] (Fin.castLE (by decide : 1 ≤ 2) k)) + i.val = m + i.val
  rw [Fin.sum_univ_one]
  rfl

variable (R : Type u) [CommRing R]

/-- The ordered actual Levi product of the two-block shape. -/
def twoBlockLeviEquiv : (twoBlocks m n hm hn).Levi R ≃*
    (Langlands.GeneralLinear m R × Langlands.GeneralLinear n R) where
  toFun g := (g 0, g 1)
  invFun g := Fin.cons g.1 (Fin.cons g.2 finZeroElim)
  left_inv g := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem twoBlockLeviEquiv_apply (g : (twoBlocks m n hm hn).Levi R) :
    twoBlockLeviEquiv hm hn R g = (g 0, g 1) := rfl

@[simp] theorem twoBlockLeviEquiv_symm_first
    (g : Langlands.GeneralLinear m R × Langlands.GeneralLinear n R) :
    (twoBlockLeviEquiv hm hn R).symm g 0 = g.1 := rfl

@[simp] theorem twoBlockLeviEquiv_symm_second
    (g : Langlands.GeneralLinear m R × Langlands.GeneralLinear n R) :
    (twoBlockLeviEquiv hm hn R).symm g 1 = g.2 := rfl

/-- The standard parabolic consists precisely of matrices with zero lower-left block. -/
theorem twoBlocks_mem_parabolic_iff (g : Langlands.GeneralLinear (m + n) R) :
    g ∈ (twoBlocks m n hm hn).parabolic R ↔
      ∀ (i : Fin n) (j : Fin m), g (i.natAdd m) (j.castAdd n) = 0 := by
  rw [BlockShape.mem_parabolic_iff]
  constructor
  · intro h i j
    simpa only [twoBlocks_index_first hm hn, twoBlocks_index_second hm hn] using
      h 1 0 i j (by change (0 : Fin 2) < 1; decide)
  · intro h i j a b hji
    fin_cases i <;> fin_cases j
    · exact False.elim ((lt_irrefl _) hji)
    · exact False.elim (by simp at hji)
    · change g ((twoBlocks m n hm hn).index 1 a)
        ((twoBlocks m n hm hn).index 0 b) = 0
      exact (congrArg₂ (fun x y : Fin (m + n) => g x y)
        (twoBlocks_index_second hm hn a) (twoBlocks_index_first hm hn b)).trans (h a b)
    · exact False.elim ((lt_irrefl _) hji)

/-- The Library Levi embedding is exactly the standard two-matrix block sum. -/
theorem twoBlocks_leviEmbedding (g : (twoBlocks m n hm hn).Levi R) :
    (twoBlocks m n hm hn).leviEmbedding R g = GeneralLinear.blockSum (g 0, g 1) := by
  apply Units.ext
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rename_i a b
    apply Eq.trans ?_ (GeneralLinear.blockSum_apply_left (g 0) (g 1) a b).symm
    simpa only [twoBlocks_index_first hm hn] using
      (twoBlocks m n hm hn).leviEmbedding_apply_same R g 0 a b
  · rename_i a b
    apply Eq.trans ?_ (GeneralLinear.blockSum_apply_left_right (g 0) (g 1) a b).symm
    simpa only [twoBlocks_index_first hm hn, twoBlocks_index_second hm hn] using
      (twoBlocks m n hm hn).leviEmbedding_apply_ne R g (i := 0) (j := 1) a b
        (by change (0 : Fin 2) ≠ 1; decide)
  · rename_i a b
    apply Eq.trans ?_ (GeneralLinear.blockSum_apply_right_left (g 0) (g 1) a b).symm
    simpa only [twoBlocks_index_first hm hn, twoBlocks_index_second hm hn] using
      (twoBlocks m n hm hn).leviEmbedding_apply_ne R g (i := 1) (j := 0) a b
        (by change (1 : Fin 2) ≠ 0; decide)
  · rename_i a b
    apply Eq.trans ?_ (GeneralLinear.blockSum_apply_right (g 0) (g 1) a b).symm
    simpa only [twoBlocks_index_second hm hn] using
      (twoBlocks m n hm hn).leviEmbedding_apply_same R g 1 a b

/-- The two diagonal projections extract the first actual diagonal block. -/
@[simp] theorem twoBlocks_leviProjection_first
    (g : (twoBlocks m n hm hn).parabolic R) (i j : Fin m) :
    (twoBlocks m n hm hn).leviProjection R g 0 i j =
      g.val (i.castAdd n) (j.castAdd n) := by
  simpa only [twoBlocks_index_first hm hn] using
    (twoBlocks m n hm hn).leviProjection_apply R g 0 i j

/-- The second diagonal projection extracts the second actual diagonal block. -/
@[simp] theorem twoBlocks_leviProjection_second
    (g : (twoBlocks m n hm hn).parabolic R) (i j : Fin n) :
    (twoBlocks m n hm hn).leviProjection R g 1 i j =
      g.val (i.natAdd m) (j.natAdd m) := by
  simpa only [twoBlocks_index_second hm hn] using
    (twoBlocks m n hm hn).leviProjection_apply R g 1 i j

/-- The explicit Levi product equivalence preserves the actual product topologies. -/
def twoBlockLeviContinuousEquiv [TopologicalSpace R] :
    (twoBlocks m n hm hn).Levi R ≃ₜ*
      (Langlands.GeneralLinear m R × Langlands.GeneralLinear n R) where
  toMulEquiv := twoBlockLeviEquiv hm hn R
  continuous_toFun := (continuous_apply 0).prodMk (continuous_apply 1)
  continuous_invFun := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact continuous_fst
    · exact continuous_snd

end Langlands.Shahidi

namespace Langlands.PadicField.TopologicalData

open Langlands.Shahidi

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}
variable (T : F.TopologicalData) {m n : ℕ} (hm : 0 < m) (hn : 0 < n)

/-- The full block modulus has precisely the standard two determinant exponents. -/
theorem leviModulus_twoBlocks (g : (twoBlocks m n hm hn).Levi F.Carrier) :
    T.leviModulus (twoBlocks m n hm hn) g =
      T.determinantNorm m (g 0) ^ n / T.determinantNorm n (g 1) ^ m := by
  rw [T.leviModulus_apply]
  simp only [Fin.prod_univ_two, Finset.prod_filter]
  norm_num [twoBlocks]
  rfl

end Langlands.PadicField.TopologicalData

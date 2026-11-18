import Langlands.Representation.Archimedean.RealLeviGeometry

/-! # Diagonal blocks of real block orthogonal matrices -/

noncomputable section

open MeasureTheory Matrix
open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean.RealLeviTorus

open RealLeviChart GramFormula

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! ## Block orthogonal elements are block diagonal -/

section BlockDiag

variable {c : ℕ} {sz : Fin c → ℕ}

/-- The diagonal block `i` of a matrix. -/
def diagBlock (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) (i : Fin c) :
    Matrix (Fin (sz i)) (Fin (sz i)) ℝ :=
  Matrix.of fun a b => g (pos sz i a) (pos sz i b)

theorem blockDiagHom_diagBlock {g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hg : BlockZero sz g) : blockDiagHom sz (diagBlock g) = g := by
  ext p q
  obtain ⟨a, ha⟩ := pos_cls sz p
  obtain ⟨b, hb⟩ := pos_cls sz q
  rw [← ha, ← hb]
  by_cases hij : cls sz p = cls sz q
  · have : HEq a b ∨ True := Or.inr trivial
    revert a b
    rw [hij]
    intro a _ b _ _
    rw [blockDiagHom_pos_pos_self]
    rfl
  · rw [blockDiagHom_pos_pos_of_ne sz _ hij, hg]
    rwa [cls_pos, cls_pos]

theorem blockDiagHom_injective : Function.Injective (blockDiagHom sz) := by
  intro A B h
  funext i
  ext a b
  have := congrFun (congrFun h (pos sz i a)) (pos sz i b)
  rwa [blockDiagHom_pos_pos_self, blockDiagHom_pos_pos_self] at this

theorem diagBlock_mul_transpose {g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hg : BlockZero sz g) (hgg : g * gᵀ = 1) (i : Fin c) :
    diagBlock g i * (diagBlock g i)ᵀ = 1 := by
  have h : blockDiagHom sz (diagBlock g * fun i => (diagBlock g i)ᵀ) = blockDiagHom sz 1 := by
    rw [map_mul, ← blockDiagHom_transpose, blockDiagHom_diagBlock hg, hgg, map_one]
  exact congrFun (blockDiagHom_injective h) i

/-- The diagonal block `i` of a block orthogonal element, as an element of `O(sz_i)`. -/
def orthBlock {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz) (i : Fin c) :
    unitaryCompact ℝ (sz i) :=
  ⟨⟨diagBlock (g : Matrix _ _ ℝ) i, (diagBlock (g : Matrix _ _ ℝ) i)ᵀ,
      diagBlock_mul_transpose hg.2 hg.1 i,
      mul_eq_one_comm.mp (diagBlock_mul_transpose hg.2 hg.1 i)⟩, by
    rw [mem_unitaryCompact_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    exact mul_eq_one_comm.mp (diagBlock_mul_transpose hg.2 hg.1 i)⟩

theorem blockDiagGL_orthBlock {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    blockDiagGL sz (fun i => ((orthBlock hg i : unitaryCompact ℝ (sz i)) :
      Langlands.GeneralLinear (sz i) ℝ)) = g := by
  ext : 1
  rw [blockDiagGL_val]
  exact blockDiagHom_diagBlock hg.2

end BlockDiag

open Langlands.GeneralLinear

variable {N : ℕ}

theorem gram_zero_eq (M : Matrix (Fin N) (Fin N) ℝ) : gram 0 M = M.det ^ 2 := by
  have : paddedGram 0 M = M * Mᵀ := by
    ext p q
    simp [paddedGram]
  rw [GramFormula.gram, this, Matrix.det_mul, Matrix.det_transpose, sq]

end Langlands.Archimedean.RealLeviTorus

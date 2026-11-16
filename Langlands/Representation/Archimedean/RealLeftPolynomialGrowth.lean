import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.RealGenericLargeReduction
import Langlands.Algebra.UniversalEnvelopingFiltration

/-!
# Growth on functions that are polynomial along a lower root group

For `p + 1 < n` let `E = E_{p+1,p}` be the matrix unit of `𝔤𝔩_n(ℝ)` in row `p + 1` and column
`p` (`lowerRootMatrix`), and `e(t) = 1 + t E` the corresponding one-parameter subgroup of lower
unipotent elements of `GL_n(ℝ)` (`lowerRootElement`).

`RealLeftPolynomialGrowthStatement`: let `Y` be a subspace of the `O(n)`-finite functions of
a real standard module of `GL_n(ℝ)` such that for every `h ∈ Y` and `g ∈ GL_n(ℝ)` the function
`t ↦ h(e(t) g)` is a polynomial of degree `< k`. Then the operators `h ↦ u h` from `Y` to the
standard module, for `u` of degree at most `d` in `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))`, span a space of dimension
at most `C (d + 1)^(n (n - 1) - 1)` for a constant `C` independent of `d`.
-/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean Langlands.Algebra.UniversalEnveloping

/-- The matrix unit `E_{p+1,p}` of `𝔤𝔩_n(ℝ)`: entry `1` in row `p + 1` and column `p`, all
other entries `0`. -/
def lowerRootMatrix (n p : ℕ) (hp : p + 1 < n) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.single ⟨p + 1, hp⟩ ⟨p, Nat.lt_of_succ_lt hp⟩ 1

/-- `E_{p+1,p}² = 0`. -/
theorem lowerRootMatrix_mul_self (n p : ℕ) (hp : p + 1 < n) :
    lowerRootMatrix n p hp * lowerRootMatrix n p hp = 0 := by
  unfold lowerRootMatrix
  exact Matrix.single_mul_single_of_ne _ _ _ _ (by simp [Fin.ext_iff]) _

theorem smul_lowerRootMatrix_mul_self (n p : ℕ) (hp : p + 1 < n) (s t : ℝ) :
    (s • lowerRootMatrix n p hp) * (t • lowerRootMatrix n p hp) = 0 := by
  rw [smul_mul_smul_comm, lowerRootMatrix_mul_self, smul_zero]

private theorem one_add_mul_one_sub {R : Type*} [Ring R] (x : R) :
    (1 + x) * (1 - x) = 1 - x * x := by noncomm_ring

private theorem one_sub_mul_one_add {R : Type*} [Ring R] (x : R) :
    (1 - x) * (1 + x) = 1 - x * x := by noncomm_ring

private theorem one_add_mul_one_add {R : Type*} [Ring R] (x y : R) :
    (1 + x) * (1 + y) = 1 + (x + y) + x * y := by noncomm_ring

/-- The lower unipotent element `e(t) = 1 + t E_{p+1,p}` of `GL_n(ℝ)`, with inverse
`1 - t E_{p+1,p}`. -/
def lowerRootElement (n p : ℕ) (hp : p + 1 < n) (t : ℝ) : Langlands.GeneralLinear n ℝ where
  val := 1 + t • lowerRootMatrix n p hp
  inv := 1 - t • lowerRootMatrix n p hp
  val_inv := by
    rw [one_add_mul_one_sub, smul_lowerRootMatrix_mul_self, sub_zero]
  inv_val := by
    rw [one_sub_mul_one_add, smul_lowerRootMatrix_mul_self, sub_zero]

@[simp]
theorem lowerRootElement_val (n p : ℕ) (hp : p + 1 < n) (t : ℝ) :
    (lowerRootElement n p hp t : Matrix (Fin n) (Fin n) ℝ) = 1 + t • lowerRootMatrix n p hp :=
  rfl

/-- `e(s) e(t) = e(s + t)`. -/
theorem lowerRootElement_add (n p : ℕ) (hp : p + 1 < n) (s t : ℝ) :
    lowerRootElement n p hp s * lowerRootElement n p hp t = lowerRootElement n p hp (s + t) := by
  apply Units.ext
  rw [Units.val_mul, lowerRootElement_val, lowerRootElement_val, lowerRootElement_val,
    add_smul]
  rw [one_add_mul_one_add, smul_lowerRootMatrix_mul_self, add_zero]

/-- **Growth on functions polynomial along a lower root group.** Let `ds` be a list of real
blocks, `p + 1 < n`, `k : ℕ`, and `Y` a subspace of the `O(n)`-finite functions of the standard
module `realStandardModule n ds` such that for every `h ∈ Y` and every `g ∈ GL_n(ℝ)` there is a
complex polynomial `q` of degree `< k` with `h(e(t) g) = q(t)` for all real `t`, where
`e(t) = 1 + t E_{p+1,p}`. Then there is `C` such that for every `d` the operators
`h ↦ u · h` from `Y` to the `O(n)`-finite functions of the standard module, for `u` in the
degree-`≤ d` part of `U(ℂ ⊗_ℝ 𝔤𝔩_n(ℝ))` acting through `realStandardLie n ds`, span a space of
dimension at most `C (d + 1)^(n (n - 1) - 1)`. -/
def RealLeftPolynomialGrowthStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (p k : ℕ) (hp : p + 1 < n)
    (Y : Submodule ℂ (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n))),
    (∀ h ∈ Y, ∀ g : Langlands.GeneralLinear n ℝ, ∃ q : Polynomial ℂ, q.degree < k ∧
      ∀ t : ℝ, (h : Langlands.GeneralLinear n ℝ → ℂ) (lowerRootElement n p hp t * g) =
        q.eval (t : ℂ)) →
    ∃ C : ℝ, ∀ d : ℕ,
      (Module.finrank ℂ ((degreeFiltration ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) d).map
        (LinearMap.lcomp ℂ _ Y.subtype ∘ₗ
          (envelopingAction (realStandardLie n ds)).toLinearMap)) : ℝ) ≤
        C * ((d : ℝ) + 1) ^ (n * (n - 1) - 1)

end Langlands.Archimedean

import Langlands.CategoryTheory.RationalizationEquivariantDenominators
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Basis.Basic

/-! # Exact scaled integral lifts of rational ring actions -/

noncomputable section

open CategoryTheory Module

set_option autoImplicit false
set_option maxHeartbeats 800000

universe v u w z

namespace Langlands.Rationalization

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {O : Type w} [Ring O] {X : C}

/-- An integral linear lift of a rational action, with exact scaled ring laws.
This is not in general a unital integral ring homomorphism. -/
structure ScaledIntegralLift (α : O →+* End X) where
  denom : ℤ
  denom_ne_zero : denom ≠ 0
  map : O →ₗ[ℤ] CategoryTheory.End X
  ofEnd_map : ∀ x, ofEnd X (map x) = denom • α x
  map_one : map 1 = denom • 1
  map_mul : ∀ x y, map x * map y = denom • map (x * y)

/-- A rational action of a ring with a finite integer basis has an integral
linear lift whose scaled unit and multiplication laws hold integrally. -/
theorem nonempty_scaledIntegralLift {I : Type z} [Finite I] (b : Basis I ℤ O)
    (α : O →+* End X) : Nonempty (ScaledIntegralLift α) := by
  obtain ⟨a, ha, r, hr⟩ := exists_common_integral_multiple (fun i => α (b i))
  let g₀ : O →ₗ[ℤ] CategoryTheory.End X := b.constr ℤ r
  have h₀ : ∀ x, ofEnd X (g₀ x) = a • α x := by
    have hlin : ((ofEnd X).toAddMonoidHom.toIntLinearMap).comp g₀ =
        a • α.toAddMonoidHom.toIntLinearMap := by
      apply b.ext
      intro i
      change ofHom (g₀ (b i)) = a • α (b i)
      simpa only [g₀, Basis.constr_basis] using hr i
    exact fun x => DFunLike.congr_fun hlin x
  have hunit : ofHom (g₀ 1) = ofHom (a • (1 : CategoryTheory.End X)) := by
    change ofEnd X (g₀ 1) = ofEnd X (a • (1 : CategoryTheory.End X))
    simp only [h₀, map_zsmul, map_one]
  have hmul (x y : O) :
      ofHom (g₀ x * g₀ y) = ofHom (a • g₀ (x * y)) := by
    change ofEnd X (g₀ x * g₀ y) = ofEnd X (a • g₀ (x * y))
    simp only [map_mul, h₀, map_zsmul, smul_mul_assoc, mul_smul_comm]
  obtain ⟨k, hk, hku⟩ := (ofHom_eq_iff_exists_zsmul_eq _ _).mp hunit
  obtain ⟨l, hl, hlm⟩ := exists_common_zsmul_eq
    (fun ij : I × I => g₀ (b ij.1) * g₀ (b ij.2))
    (fun ij : I × I => a • g₀ (b ij.1 * b ij.2))
    (fun ij => hmul (b ij.1) (b ij.2))
  let t : ℤ := k * l
  let n : ℤ := t * a
  let g : O →ₗ[ℤ] CategoryTheory.End X := t • g₀
  have hunit' : t • g₀ 1 = t • (a • (1 : CategoryTheory.End X)) := by
    simpa only [t, smul_smul, mul_assoc, mul_comm k l] using congrArg (fun f => l • f) hku
  have hmul' (i j : I) :
      t • (g₀ (b i) * g₀ (b j)) = t • (a • g₀ (b i * b j)) := by
    simpa only [t, smul_smul, mul_assoc] using congrArg (fun f => k • f) (hlm (i, j))
  have hbasis (i j : I) : g (b i) * g (b j) = n • g (b i * b j) := by
    change (t • g₀ (b i)) * (t • g₀ (b j)) =
      (t * a) • (t • g₀ (b i * b j))
    rw [smul_mul_assoc, mul_smul_comm, hmul' i j]
    simp only [smul_smul, mul_comm, mul_left_comm]
  have hbilin :
      ((LinearMap.mul ℤ (CategoryTheory.End X)) ∘ₗ g).compl₂ g =
        (LinearMap.mul ℤ O).compr₂ (n • g) := by
    apply b.ext
    intro i
    apply b.ext
    intro j
    exact hbasis i j
  refine ⟨{
    denom := n
    denom_ne_zero := mul_ne_zero (mul_ne_zero hk hl) ha
    map := g
    ofEnd_map := ?_
    map_one := ?_
    map_mul := ?_ }⟩
  · intro x
    change ofEnd X (t • g₀ x) = (t * a) • α x
    rw [map_zsmul, h₀, smul_smul]
  · change t • g₀ 1 = (t * a) • (1 : CategoryTheory.End X)
    rw [hunit', smul_smul]
  · intro x y
    exact DFunLike.congr_fun (DFunLike.congr_fun hbilin x) y

/-- A choice of exact scaled integral lift, using the proved finite-basis
denominator and torsion clearance. -/
def scaledIntegralLift {I : Type z} [Finite I] (b : Basis I ℤ O)
    (α : O →+* End X) : ScaledIntegralLift α :=
  Classical.choice (nonempty_scaledIntegralLift b α)

end Langlands.Rationalization

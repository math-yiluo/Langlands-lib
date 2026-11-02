import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.LinearAlgebra.Reflection
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.Module

namespace Langlands.Group.RelativeWeylIndexing

open Classical
open scoped BigOperators

noncomputable section

private theorem pow_eigen {V : Type*} [AddCommGroup V] [Module ℂ V]
    (T : V ≃ₗ[ℂ] V) (x : V) (a : ℂ) (h : T x = a • x) (n : ℕ) :
    (T ^ n) x = a ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply, ih, map_smul, h, smul_smul, pow_succ]

/-- The two-dimensional eigenvectors give the Coxeter relation on an arbitrary module. -/
private theorem reflection_pair_relation {V : Type*} [AddCommGroup V] [Module ℂ V]
    {x y : V} {f g : Module.Dual ℂ V} (hf : f x = 2) (hg : g y = 2)
    (q : ℂ) (hq : q ≠ 0) (hqq : q ^ 2 ≠ 1) (n : ℕ) (hqn : q ^ (2 * n) = 1)
    (hfy : f y = -(q + q⁻¹)) (hgx : g x = -(q + q⁻¹)) :
    (Module.reflection hf * Module.reflection hg) ^ n = 1 := by
  let c := q + q⁻¹
  let T := Module.reflection hf * Module.reflection hg
  let u := q • x + y
  let v := q⁻¹ • x + y
  have hdiff : q - q⁻¹ ≠ 0 := by
    intro h
    have he := sub_eq_zero.mp h
    apply hqq
    calc
      q ^ 2 = q * q := by ring
      _ = q * q⁻¹ := congrArg (q * ·) he
      _ = 1 := mul_inv_cancel₀ hq
  have hD : 4 - c ^ 2 ≠ 0 := by
    have he : 4 - c ^ 2 = -(q - q⁻¹) ^ 2 := by
      dsimp [c]
      field_simp
      ring
    rw [he]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hdiff)
  have hu : T u = q ^ 2 • u := by
    dsimp [T, u]
    simp only [Module.reflection_apply, map_add, map_sub, map_smul,
      hf, hg, hfy, hgx]
    match_scalars <;> field_simp <;> ring
  have hv : T v = (q⁻¹) ^ 2 • v := by
    dsimp [T, v]
    simp only [Module.reflection_apply, map_add, map_sub, map_smul,
      hf, hg, hfy, hgx]
    match_scalars <;> field_simp <;> ring
  have hpu : (T ^ n) u = u := by
    rw [pow_eigen T u (q ^ 2) hu, ← pow_mul, hqn, one_smul]
  have hpv : (T ^ n) v = v := by
    rw [pow_eigen T v ((q⁻¹) ^ 2) hv, ← pow_mul, inv_pow, hqn, inv_one, one_smul]
  have hpx : (T ^ n) x = x := by
    have he : (T ^ n) (u - v) = u - v := by rw [map_sub, hpu, hpv]
    have huv : u - v = (q - q⁻¹) • x := by dsimp [u, v]; module
    rw [huv, map_smul] at he
    exact smul_right_injective V hdiff he
  have hpy : (T ^ n) y = y := by
    have he := hpu
    dsimp [u] at he
    rw [map_add, map_smul, hpx] at he
    exact add_left_cancel he
  ext z
  let a := (2 * f z + c * g z) / (4 - c ^ 2)
  let b := (c * f z + 2 * g z) / (4 - c ^ 2)
  let z₀ := z - a • x - b • y
  have hf0 : f z₀ = 0 := by
    dsimp [z₀]
    simp only [map_sub, map_smul, hf, hfy]
    change f z - a * 2 - b * (-c) = 0
    dsimp [a, b]
    field_simp
    ring
  have hg0 : g z₀ = 0 := by
    dsimp [z₀]
    simp only [map_sub, map_smul, hg, hgx]
    change g z - a * (-c) - b * 2 = 0
    dsimp [a, b]
    field_simp
    ring
  have hz0 : T z₀ = z₀ := by
    simp [T, LinearEquiv.mul_apply, Module.reflection_apply, hf0, hg0]
  have hp0 : (T ^ n) z₀ = z₀ := by simpa using pow_eigen T z₀ 1 (by simpa using hz0) n
  have hz : z = z₀ + a • x + b • y := by dsimp [z₀]; module
  change (T ^ n) z = z
  conv_lhs => rw [hz]
  rw [map_add, map_add, map_smul, map_smul, hp0, hpx, hpy]
  exact hz.symm

universe u v
variable {B : Type u} {W : Type v} [Group W] [Fintype B]
variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

private def coxeterPhase (n : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (2 * n : ℕ))

private def reflectionCoefficient (M : CoxeterMatrix B) (i j : B) : ℂ :=
  if i = j then 2 else -(coxeterPhase (M i j) + (coxeterPhase (M i j))⁻¹)

private def coordinateVector (i : B) : B → ℂ := Pi.single i 1

private def coordinateForm (M : CoxeterMatrix B) (i : B) : Module.Dual ℂ (B → ℂ) :=
  ∑ j : B, reflectionCoefficient M i j • LinearMap.proj j

private theorem coordinateForm_vector (i j : B) :
    coordinateForm M i (coordinateVector j) = reflectionCoefficient M i j := by
  simp [coordinateForm, coordinateVector, LinearMap.sum_apply, Pi.single_apply]

private theorem coordinateForm_self (i : B) :
    coordinateForm M i (coordinateVector i) = 2 := by
  rw [coordinateForm_vector]
  simp [reflectionCoefficient]

private def coordinateReflection (M : CoxeterMatrix B) (i : B) :
    (B → ℂ) ≃ₗ[ℂ] (B → ℂ) :=
  Module.reflection (coordinateForm_self (M := M) i)

private theorem coordinateReflection_liftable :
    M.IsLiftable (coordinateReflection M) := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [M.diagonal, pow_one]
    apply LinearEquiv.ext
    intro z
    exact Module.involutive_reflection (coordinateForm_self (M := M) i) z
  by_cases hzero : M i j = 0
  · simp [hzero]
  have hn : 2 ≤ M i j := by
    have := M.off_diagonal i j hij
    omega
  have hroot : IsPrimitiveRoot (coxeterPhase (M i j)) (2 * M i j) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  apply reflection_pair_relation
      (coordinateForm_self (M := M) i) (coordinateForm_self (M := M) j)
      (coxeterPhase (M i j)) (hroot.ne_zero (by omega))
      (hroot.pow_ne_one_of_pos_of_lt (by decide) (by omega))
      (M i j) hroot.pow_eq_one
  · rw [coordinateForm_vector]
    simp [reflectionCoefficient, hij]
  · rw [coordinateForm_vector]
    simp [reflectionCoefficient, Ne.symm hij, M.symmetric j i]

/-- A complex reflection representation of a finite-rank Coxeter presentation. -/
def simpleReflectionRepresentation : W →* ((B → ℂ) ≃ₗ[ℂ] (B → ℂ)) :=
  cs.lift ⟨coordinateReflection M, coordinateReflection_liftable (M := M)⟩

/-- The indices of the simple reflections of a finite-rank Coxeter system are distinct. -/
theorem simple_reflection_injective : Function.Injective cs.simple := by
  intro i j hij
  by_contra hne
  have he : coordinateReflection M i = coordinateReflection M j := by
    simpa [simpleReflectionRepresentation] using congrArg (simpleReflectionRepresentation cs) hij
  have hc := congrArg (fun T : (B → ℂ) ≃ₗ[ℂ] (B → ℂ) =>
    T (coordinateVector i) i) he
  have hleft : coordinateReflection M i (coordinateVector i) i = -1 := by
    simp [coordinateReflection, coordinateVector]
  have hright : coordinateReflection M j (coordinateVector i) i = 1 := by
    simp [coordinateReflection, Module.reflection_apply, coordinateVector,
      hne]
  rw [hleft, hright] at hc
  exact (by norm_num : (-1 : ℂ) ≠ 1) hc

end
end Langlands.Group.RelativeWeylIndexing

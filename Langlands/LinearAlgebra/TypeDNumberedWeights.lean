import Langlands.GroupScheme.Reductive.IntegralWeylVector
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic

/-! # Numbered vector weights in an integral type-D weight lattice -/

noncomputable section

set_option maxHeartbeats 1600000

namespace Langlands.TypeDNumberedWeights

/-- Pairing of a coordinate weight with a numbered type-D simple coroot. -/
def coefficient {n : ℕ} (i j : Fin n) : ℤ :=
  if j.val + 1 < n then
    (if i = j then 1 else 0) - (if i.val = j.val + 1 then 1 else 0)
  else
    (if i.val + 2 = n then 1 else 0) + (if i.val + 1 = n then 1 else 0)

theorem coefficient_chain {n : ℕ} (hn : 4 ≤ n) (i j : Fin n)
    (hi : i.val + 1 < n) :
    coefficient i j - coefficient ⟨i.val + 1, hi⟩ j = CartanMatrix.D n i j := by
  simp only [coefficient, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
    show ¬ n ≤ 2 by omega, ↓reduceIte]
  split_ifs <;> omega

theorem coefficient_last {n : ℕ} (hn : 4 ≤ n) (j : Fin n) :
    coefficient (⟨n - 2, by omega⟩ : Fin n) j +
        coefficient (⟨n - 1, by omega⟩ : Fin n) j =
      CartanMatrix.D n ⟨n - 1, by omega⟩ j := by
  simp only [coefficient, CartanMatrix.D, Matrix.of_apply, Fin.ext_iff,
    show ¬ n ≤ 2 by omega, ↓reduceIte]
  split_ifs <;> omega

theorem coefficient_zero {n : ℕ} (hn : 4 ≤ n) (j : Fin n) :
    coefficient (⟨0, by omega⟩ : Fin n) j = if j.val = 0 then 1 else 0 := by
  by_cases hj : j.val = 0
  · simp [coefficient, Fin.ext_iff, hj, show 1 < n by omega]
  · simp [coefficient, Fin.ext_iff, hj, Ne.symm hj,
      show (2 : ℕ) ≠ n by omega, show (1 : ℕ) ≠ n by omega]

section RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (b : P.Base) (hspan : P.corootSpan ℤ = ⊤)
    {n : ℕ} (e : b.support ≃ Fin n)

/-- The vector weights defined by their pairings with the integral simple-coroot basis. -/
def weight (i : Fin n) : X :=
  P.toLinearMap.toPerfPair.symm
    ((IntegralWeylVector.corootBasis P b hspan).constr ℤ
      (fun a => coefficient i (e a)))

@[simp] theorem pairing_weight (i : Fin n) (a : b.support) :
    P.toLinearMap (weight P b hspan e i) (P.coroot a.val) = coefficient i (e a) := by
  unfold weight
  rw [LinearMap.apply_symm_toPerfPair_self,
    ← IntegralWeylVector.corootBasis_apply P b hspan a, Module.Basis.constr_basis]

variable (hn : 4 ≤ n)
    (hcartan : ∀ a c : b.support, P.pairing a.val c.val = CartanMatrix.D n (e a) (e c))

include hcartan hn

/-- The root at each chain vertex is the difference of successive vector weights. -/
theorem root_chain (a : b.support) (ha : (e a).val + 1 < n) :
    P.root a.val = weight P b hspan e (e a) -
      weight P b hspan e ⟨(e a).val + 1, ha⟩ := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq P b hspan
  intro c
  rw [P.root_coroot_eq_pairing, hcartan, map_sub, LinearMap.sub_apply,
    pairing_weight, pairing_weight, coefficient_chain hn]

/-- The final simple root is the sum of the last two vector weights. -/
theorem root_last (a : b.support) (ha : (e a).val + 1 = n) :
    P.root a.val = weight P b hspan e ⟨n - 2, by omega⟩ +
      weight P b hspan e ⟨n - 1, by omega⟩ := by
  apply IntegralWeylVector.eq_of_pairing_simple_eq P b hspan
  intro c
  rw [P.root_coroot_eq_pairing, hcartan, map_add, LinearMap.add_apply,
    pairing_weight, pairing_weight, coefficient_last hn]
  congr 2
  apply Fin.ext
  change (e a).val = n - 1
  omega

omit hcartan in
/-- The first vector weight is the fundamental weight at the vertex numbered zero. -/
theorem pairing_weight_zero (a : b.support) :
    P.toLinearMap (weight P b hspan e ⟨0, by omega⟩) (P.coroot a.val) =
      if (e a).val = 0 then 1 else 0 := by
  rw [pairing_weight, coefficient_zero hn]

end RootDatum

end Langlands.TypeDNumberedWeights

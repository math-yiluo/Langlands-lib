import Langlands.LinearAlgebra.CartanE6RootCoordinates

/-! # A complementary A₂ face in E₆ -/

noncomputable section

open scoped BigOperators

namespace Langlands.CartanE6Root

open RootReflectionCoefficients

/-- The short-arm endpoint and the central vertex. Their complement is
the union of the two long-arm chains of length two. -/
def shortArmAndCenter : Finset (Fin 6) := {1, 3}

/-- The coefficients of a coroot combination in the two long-arm
chains that is dominant for the reflected complementary face. -/
def complementaryCoweightCoefficients : Fin 6 → ℤ := ![-1, 0, -3, 0, -3, -1]

theorem complementaryCoweightCoefficients_eq_zero {i : Fin 6}
    (hi : i ∈ shortArmAndCenter) : complementaryCoweightCoefficients i = 0 := by
  revert i
  decide

private def reflectionRootCoefficients : Fin 6 → ℤ := ![1, 1, 2, 2, 2, 1]

private def reflectionPairing : Fin 6 → ℤ := ![0, 0, 1, -1, 1, 0]

private def mixedPairing (i j : Fin 6) : ℤ :=
  CartanMatrix.E 6 i j - reflectionPairing i * reflectionPairing j

private theorem cartan_symm (i j : Fin 6) :
    CartanMatrix.E 6 i j = CartanMatrix.E 6 j i := by
  fin_cases i <;> fin_cases j <;> decide

section RootDatum

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) (a : Fin 6 → J)
  (hE : ∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 6 i j)

private def Realized (c : Fin 6 → ℤ) : Prop :=
  ∃ r : J, P.root r = combination P a c ∧ P.coroot r = combination P.flip a c

include hE

private theorem coroot'_combination (c : Fin 6 → ℤ) (i : Fin 6) :
    P.coroot' (a i) (combination P a c) = ∑ j, c j * CartanMatrix.E 6 j i := by
  change P.toLinearMap (∑ j, c j • P.root (a j)) (P.coroot (a i)) = _
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    P.root_coroot_eq_pairing, zsmul_eq_mul, Int.cast_id, hE]

private theorem root'_combination (c : Fin 6 → ℤ) (i : Fin 6) :
    P.root' (a i) (combination P.flip a c) = ∑ j, c j * CartanMatrix.E 6 i j := by
  change P.root' (a i) (∑ j, c j • P.coroot (a j)) = _
  simp only [map_sum, map_zsmul, P.root_coroot_eq_pairing, zsmul_eq_mul, Int.cast_id, hE]

private theorem Realized.reflect (c : Fin 6 → ℤ) (h : Realized P a c) (i : Fin 6) :
    Realized P a (reflect (CartanMatrix.E 6) i c) := by
  classical
  obtain ⟨r, hr, hc⟩ := h
  have hri : P.pairing r (a i) = ∑ j, c j * CartanMatrix.E 6 j i := by
    change P.coroot' (a i) (P.root r) = _
    rw [hr, coroot'_combination P a hE]
  have hir : P.pairing (a i) r = ∑ j, c j * CartanMatrix.E 6 j i := by
    change P.root' (a i) (P.coroot r) = _
    rw [hc, root'_combination P a hE]
    exact Finset.sum_congr rfl fun j _ => by rw [cartan_symm i j]
  refine ⟨P.reflectionPerm (a i) r, ?_, ?_⟩
  · rw [P.root_reflectionPerm, P.reflection_apply_root, hri, hr]
    simp [combination, RootReflectionCoefficients.reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
  · rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, hir, hc]
    simp [combination, RootReflectionCoefficients.reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]

private theorem realized_reflectionRoot : Realized P a reflectionRootCoefficients := by
  classical
  have h : Realized P a (Pi.single 0 1) := by
    refine ⟨a 0, ?_, ?_⟩ <;> simp [combination, Pi.single_apply, ite_smul]
  have h := Realized.reflect P a hE _ h 2
  have h := Realized.reflect P a hE _ h 3
  have h := Realized.reflect P a hE _ h 1
  have h := Realized.reflect P a hE _ h 4
  have h := Realized.reflect P a hE _ h 3
  have h := Realized.reflect P a hE _ h 2
  have h := Realized.reflect P a hE _ h 5
  have h := Realized.reflect P a hE _ h 4
  convert h using 1
  decide

/-- A single reflection makes the short-arm endpoint and the central vertex
an A₂ face orthogonal to the original two long-arm chains. The two displayed
coroot combinations have the original fundamental coweight pairings. -/
theorem exists_complementary_typeA2_reflection :
    ∃ w : P.Aut,
      (∀ i : Fin 6, P.root' (w.indexEquiv (a i))
        (combination P.flip a complementaryCoweightCoefficients) =
          if i ∈ shortArmAndCenter then 0 else 1) ∧
      (∀ i j : Fin 6, i ∈ shortArmAndCenter → j ∉ shortArmAndCenter →
        P.pairing (w.indexEquiv (a i)) (a j) = 0) ∧
      (∀ i : Fin 6,
        P.root' (a i) (P.coroot (w.indexEquiv (a 1)) + P.coroot (w.indexEquiv (a 3))) =
          if i = 1 then 1 else 0) ∧
      (∀ i : Fin 6,
        P.root' (a i) (P.coroot (w.indexEquiv (a 1)) + 2 • P.coroot (w.indexEquiv (a 3))) =
          if i = 3 then 1 else 0) := by
  obtain ⟨r, hr, hc⟩ := realized_reflectionRoot P a hE
  let w := RootPairing.Equiv.reflection P r
  have hleft (i : Fin 6) : P.pairing r (a i) = reflectionPairing i := by
    change P.coroot' (a i) (P.root r) = _
    rw [hr, coroot'_combination P a hE]
    revert i
    decide
  have hright (i : Fin 6) : P.pairing (a i) r = reflectionPairing i := by
    change P.root' (a i) (P.coroot r) = _
    rw [hc, root'_combination P a hE]
    revert i
    decide
  have hw (i j : Fin 6) : P.pairing (w.indexEquiv (a i)) (a j) = mixedPairing i j := by
    change P.coroot' (a j) (P.root (P.reflectionPerm r (a i))) = _
    rw [P.root_reflectionPerm, P.reflection_apply_root, map_sub, map_zsmul]
    change P.pairing (a i) (a j) - P.pairing (a i) r * P.pairing r (a j) = _
    rw [hE, hright, hleft]
    rfl
  have hw' (i j : Fin 6) : P.pairing (a i) (w.indexEquiv (a j)) = mixedPairing i j := by
    change P.root' (a i) (P.coroot (P.reflectionPerm r (a j))) = _
    rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, map_sub, map_zsmul]
    change P.pairing (a i) (a j) - P.pairing r (a j) * P.pairing (a i) r = _
    rw [hE, hright, hleft, mul_comm]
    rfl
  refine ⟨w, fun i => ?_, fun i j hi hj => ?_, fun i => ?_, fun i => ?_⟩
  · change P.root' (w.indexEquiv (a i))
      (∑ j, complementaryCoweightCoefficients j • P.coroot (a j)) = _
    simp only [map_sum, map_zsmul, P.root_coroot_eq_pairing, zsmul_eq_mul, hw]
    revert i
    decide
  · rw [hw]
    fin_cases i <;> fin_cases j <;> revert hi hj <;> decide
  · rw [map_add]
    change P.pairing (a i) (w.indexEquiv (a 1)) +
      P.pairing (a i) (w.indexEquiv (a 3)) = _
    rw [hw', hw']
    revert i
    decide
  · rw [map_add, two_nsmul, map_add]
    change P.pairing (a i) (w.indexEquiv (a 1)) +
      (P.pairing (a i) (w.indexEquiv (a 3)) + P.pairing (a i) (w.indexEquiv (a 3))) = _
    rw [hw', hw']
    revert i
    decide

end RootDatum

/-- A reflected E₆ base has an A₂ face orthogonal to the original long-arm
chains, with an explicit defining cocharacter and complementary coweights. -/
def CartanE6ComplementaryTypeA2Statement : Prop :=
  ∀ (J X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
    (P : RootDatum J X Y) (a : Fin 6 → J),
    (∀ i j, P.pairing (a i) (a j) = CartanMatrix.E 6 i j) →
    ∃ w : P.Aut,
      (∀ i : Fin 6, P.root' (w.indexEquiv (a i))
        (combination P.flip a complementaryCoweightCoefficients) =
          if i ∈ shortArmAndCenter then 0 else 1) ∧
      (∀ i j : Fin 6, i ∈ shortArmAndCenter → j ∉ shortArmAndCenter →
        P.pairing (w.indexEquiv (a i)) (a j) = 0) ∧
      (∀ i : Fin 6,
        P.root' (a i) (P.coroot (w.indexEquiv (a 1)) + P.coroot (w.indexEquiv (a 3))) =
          if i = 1 then 1 else 0) ∧
      (∀ i : Fin 6,
        P.root' (a i) (P.coroot (w.indexEquiv (a 1)) + 2 • P.coroot (w.indexEquiv (a 3))) =
          if i = 3 then 1 else 0)

theorem cartanE6ComplementaryTypeA2 : CartanE6ComplementaryTypeA2Statement := by
  intro J X Y _ _ P a hE
  exact exists_complementary_typeA2_reflection P a hE

end Langlands.CartanE6Root

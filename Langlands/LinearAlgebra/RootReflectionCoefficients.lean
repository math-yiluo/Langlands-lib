import Mathlib.LinearAlgebra.RootSystem.Basic
import Mathlib.LinearAlgebra.Matrix.Cartan.Basic
import Mathlib.Tactic

/-! # Integral coefficients of roots under simple reflections -/

noncomputable section

namespace Langlands.RootReflectionCoefficients

variable {J X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum J X Y) {n : ℕ} (a : Fin n → J)

/-- The integral combination of a specified finite family of actual roots. -/
def combination (c : Fin n → ℤ) : X :=
  ∑ j, c j • P.root (a j)

/-- An integral coefficient vector represents an actual root. -/
def IsRoot (c : Fin n → ℤ) : Prop :=
  ∃ r : J, P.root r = combination P a c

/-- Reflect an integral coefficient vector using its Cartan matrix. -/
def reflect (M : Matrix (Fin n) (Fin n) ℤ) (i : Fin n)
    (c : Fin n → ℤ) : Fin n → ℤ :=
  fun j => c j - if j = i then ∑ k, c k * M k i else 0

/-- Each coordinate vector represents its selected actual root. -/
theorem isRoot_single (i : Fin n) :
    IsRoot P a (Pi.single i 1) := by
  classical
  refine ⟨a i, ?_⟩
  simp [combination, Pi.single_apply, ite_smul]

/-- Cartan reflection of coefficients is realized by reflection of the
actual root, without requiring independence of the selected roots. -/
theorem IsRoot.reflect {c : Fin n → ℤ} (h : IsRoot P a c)
    (M : Matrix (Fin n) (Fin n) ℤ)
    (hM : ∀ i j, P.pairing (a i) (a j) = M i j) (i : Fin n) :
    IsRoot P a (reflect M i c) := by
  classical
  obtain ⟨r, hr⟩ := h
  refine ⟨P.reflectionPerm (a i) r, ?_⟩
  have hp : P.pairing r (a i) = ∑ k, c k * M k i := by
    change P.toLinearMap (P.root r) (P.coroot (a i)) = _
    rw [hr]
    simp only [combination, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, RootPairing.root_coroot_eq_pairing, hM, smul_eq_mul]
  rw [P.root_reflectionPerm, P.reflection_apply_root, hp, hr]
  simp [combination, RootReflectionCoefficients.reflect, sub_smul,
    Finset.sum_sub_distrib, ite_smul]

end Langlands.RootReflectionCoefficients

import Langlands.GroupScheme.Lie.RepresentationDerivationPower
import Langlands.GroupScheme.Lie.FiniteDimensional
import Langlands.GroupScheme.Lie.SemisimpleElement
import Mathlib.FieldTheory.Separable

/-! # Semisimple prime-power replacements of actual Lie elements -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj Matrix

namespace Langlands.LinearAlgebra

variable {k : Type u} [Field k]

/-- Shift a finite relation between prime powers to its first exponent. -/
def primePowerRelationPolynomial (s : Finset ℕ) (c : ℕ → k) (p m : ℕ) : k[X] :=
  ∑ i ∈ s, c i • X ^ (p ^ (i - m))

theorem derivative_X_primePower (p r : ℕ) [CharP k p] :
    derivative (X ^ (p ^ r) : k[X]) = if r = 0 then 1 else 0 := by
  cases r with
  | zero => simp
  | succ r =>
    simp [derivative_X_pow, pow_succ, Nat.cast_mul]

/-- The shifted relation has nonzero constant derivative at its first
nonzero coefficient. -/
theorem derivative_primePowerRelationPolynomial
    (s : Finset ℕ) (c : ℕ → k) (p m : ℕ) [CharP k p]
    (hm : m ∈ s) (hle : ∀ i ∈ s, m ≤ i) :
    derivative (primePowerRelationPolynomial s c p m) = C (c m) := by
  classical
  rw [primePowerRelationPolynomial, derivative_sum]
  rw [Finset.sum_eq_single m]
  · simp [smul_eq_C_mul]
  · intro i hi him
    have hsub : i - m ≠ 0 := by
      have := hle i hi
      omega
    simp [derivative_X_primePower, hsub]
  · exact fun h => (h hm).elim

theorem separable_primePowerRelationPolynomial
    (s : Finset ℕ) (c : ℕ → k) (p m : ℕ) [CharP k p]
    (hm : m ∈ s) (hle : ∀ i ∈ s, m ≤ i) (hc : c m ≠ 0) :
    (primePowerRelationPolynomial s c p m).Separable := by
  rw [separable_def', derivative_primePowerRelationPolynomial s c p m hm hle]
  refine ⟨0, C (c m)⁻¹, ?_⟩
  simp [← C_mul, hc]

variable {A : Type v} [Ring A] [Algebra k A]

/-- Substitution of the first prime power restores the original exponents. -/
theorem aeval_primePowerRelationPolynomial (s : Finset ℕ) (c : ℕ → k)
    (p m : ℕ) (z : A) (hle : ∀ i ∈ s, m ≤ i) :
    aeval (z ^ (p ^ m)) (primePowerRelationPolynomial s c p m) =
      ∑ i ∈ s, c i • z ^ (p ^ i) := by
  classical
  simp only [primePowerRelationPolynomial, map_sum, map_smul, map_pow, aeval_X]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← pow_mul, ← pow_add, Nat.add_sub_of_le (hle i hi)]

end Langlands.LinearAlgebra

namespace Langlands.GroupScheme.Lie

open Langlands.LinearAlgebra

variable {k : Type u} [Field k]

/-- A separable ground-field annihilator gives geometric semisimplicity. -/
theorem isGeometricallySemisimpleMatrix_of_separable_aeval_eq_zero
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n k)
    {q : k[X]} (hq : q.Separable) (hM : aeval M q = 0) :
    IsGeometricallySemisimpleMatrix M := by
  let K := AlgebraicClosure k
  have hK : aeval (M.map (algebraMap k K)) q = 0 := by
    change aeval ((Algebra.ofId k K).mapMatrix M) q = 0
    rw [aeval_algHom_apply, hM, map_zero]
  have hK' : aeval (M.map (algebraMap k K)) (q.map (algebraMap k K)) = 0 := by
    rw [← aeval_eq_aeval_map (IsScalarTower.algebraMap_eq k K (Matrix n n K)).symm]
    exact hK
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hq.map.squarefree
    (p := q.map (algebraMap k K))
  change aeval (Matrix.toLinAlgEquiv' (M.map (algebraMap k K)))
    (q.map (algebraMap k K)) = 0
  rw [aeval_algHom_apply, hK', map_zero]

/-- A finite prime-power relation with a first nonzero coefficient makes
that first prime power geometrically semisimple. -/
theorem isGeometricallySemisimpleMatrix_primePower_of_relation
    {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n k)
    (s : Finset ℕ) (c : ℕ → k) (p m : ℕ) [CharP k p]
    (hm : m ∈ s) (hle : ∀ i ∈ s, m ≤ i) (hc : c m ≠ 0)
    (hrel : ∑ i ∈ s, c i • M ^ (p ^ i) = 0) :
    IsGeometricallySemisimpleMatrix (M ^ (p ^ m)) := by
  apply isGeometricallySemisimpleMatrix_of_separable_aeval_eq_zero _
    (separable_primePowerRelationPolynomial s c p m hm hle hc)
  rw [aeval_primePowerRelationPolynomial s c p m M hle]
  exact hrel

variable (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]

local instance semisimplePrimePowerKernelCommGroup : CommGroup (lieKernel G k) :=
  lieKernelCommGroup G

local instance semisimplePrimePowerKernelModule : Module k (Additive (lieKernel G k)) :=
  lieKernelModule G

/-- A single actual prime-power Lie element is semisimple in every actual
finite matrix representation simultaneously. -/
theorem exists_isSemisimpleElement_primePowerKernel
    (X : lieKernel G k) (p : ℕ) [Fact p.Prime] [CharP k p] :
    ∃ m : ℕ, IsSemisimpleElement G (primePowerKernel G X p m) := by
  classical
  have hdep := Module.Finite.not_linearIndependent_of_infinite (R := k)
    (fun r : ℕ => Additive.ofMul (primePowerKernel G X p r))
  obtain ⟨c, hrel, hc⟩ := not_linearIndependent_iff_finsupp.mp hdep
  have hs : c.support.Nonempty := Finsupp.support_nonempty_iff.mpr hc
  let m := c.support.min' hs
  have hm : m ∈ c.support := Finset.min'_mem c.support hs
  have hle : ∀ i ∈ c.support, m ≤ i := fun i hi => Finset.min'_le _ _ hi
  refine ⟨m, ?_⟩
  intro n ρ
  rw [MatrixRepresentation.tangentMatrix_primePowerKernel]
  apply isGeometricallySemisimpleMatrix_primePower_of_relation
    (ρ.tangentMatrix k X) c.support c p m hm hle (Finsupp.mem_support_iff.mp hm)
  have hρ := congrArg (ρ.kernelDifferential k) hrel
  have hpow (r : ℕ) : ρ.tangentMatrix k (primePowerKernel G X p r) =
      ρ.tangentMatrix k X ^ (p ^ r) :=
    ρ.tangentMatrix_primePowerKernel X p r
  simpa only [Finsupp.sum, map_sum, map_smul, map_zero,
    MatrixRepresentation.kernelDifferential_apply, toMul_ofMul,
    hpow] using hρ

end Langlands.GroupScheme.Lie

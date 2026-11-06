import Langlands.GroupScheme.MatrixRepresentation.AdditiveFixedVectors
import Langlands.GroupScheme.MatrixRepresentation.StableSubrepresentation
import Mathlib.Algebra.Polynomial.Degree.Support

/-! # Invariant subspaces of actual additive-group representations -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveInvariantSubspaces

open AdditiveDividedPowers AdditiveRestrictedOperators AdditiveFixedVectors

variable {k : Type u} [Field k] {n : Type} [Fintype n] [DecidableEq n]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)

/-- The actual action at an arbitrary scalar point evaluates the universal orbit. -/
theorem affineAction_eq_aeval_polynomialOrbit (v : n → k)
    (A : CommAlgCat.{u} k) (t : A) :
    ρ.affineAction A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t))
        (fun i => algebraMap k A (v i)) =
      fun i => Polynomial.aeval t (polynomialOrbit ρ v i) := by
  rw [affineAction_apply, ← univariateMatrix_aeval]
  funext i
  simp only [polynomialOrbit, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.map_apply, Polynomial.aeval_C]

/-- Every coordinate of the universal orbit has a common finite expansion. -/
theorem polynomialOrbit_eq_sum (v : n → k) :
    ∃ N : ℕ, ∀ i : n,
      polynomialOrbit ρ v i =
        ∑ m ∈ Finset.range N, Polynomial.C (dividedPower ρ m v i) * Polynomial.X ^ m := by
  let N := (Finset.univ.sup fun i : n => (polynomialOrbit ρ v i).natDegree) + 1
  refine ⟨N, fun i => ?_⟩
  have hi : (polynomialOrbit ρ v i).natDegree < N :=
    Nat.lt_succ_of_le (Finset.le_sup (f := fun j : n =>
      (polynomialOrbit ρ v j).natDegree) (Finset.mem_univ i))
  simpa only [polynomialOrbit_coeff] using
    (polynomialOrbit ρ v i).as_sum_range_C_mul_X_pow' hi

/-- Applying any coefficient functional to a translate gives a finite linear
combination of the actual divided-power translates of the original vector. -/
theorem linearFunctional_affineAction_eq_sum (v : n → k) :
    ∃ N : ℕ, ∀ (A : CommAlgCat.{u} k) (t : A) (ℓ : A →ₗ[k] k),
      (fun i => ℓ (ρ.affineAction A
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t))
        (fun j => algebraMap k A (v j)) i)) =
      ∑ m ∈ Finset.range N, ℓ (t ^ m) • dividedPower ρ m v := by
  obtain ⟨N, hN⟩ := polynomialOrbit_eq_sum ρ v
  refine ⟨N, fun A t ℓ => ?_⟩
  rw [affineAction_eq_aeval_polynomialOrbit]
  funext i
  change ℓ (Polynomial.aeval t (polynomialOrbit ρ v i)) = _
  rw [hN i]
  have hs (c : k) (a : A) : ℓ (algebraMap k A c * a) = c * ℓ a := by
    rw [← Algebra.smul_def, map_smul, smul_eq_mul]
  simp only [map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X,
    hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m _
  exact mul_comm _ _

/-- Stability over all test algebras is equivalent to invariance under all actual
coefficient operators, over finite as well as infinite fields. -/
theorem isStableSubspace_iff_invariant_dividedPower (W : Submodule k (n → k)) :
    IsStableSubspace ρ W ↔
      ∀ m : ℕ, ∀ v ∈ W, dividedPower ρ m v ∈ W := by
  constructor
  · intro h m v hv
    have hX := h (CommAlgCat.of k k[X])
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
        (CommAlgCat.of k k[X]) (fun _ => Polynomial.X))
      v hv (Polynomial.lcoeff k m)
    change (fun i => (Polynomial.lcoeff k m)
      (ρ.affineAction (CommAlgCat.of k k[X])
        (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1)
          (CommAlgCat.of k k[X]) (fun _ => Polynomial.X))
        (fun j => algebraMap k k[X] (v j)) i)) ∈ W at hX
    rw [affineAction_eq_aeval_polynomialOrbit] at hX
    simpa only [Polynomial.aeval_X_left_apply, Polynomial.lcoeff_apply,
      polynomialOrbit_coeff] using hX
  · intro h A x v hv ℓ
    obtain ⟨t, rfl⟩ := VectorGroup.affinePoint_surjective
      (R := CommRingCat.of k) (d := 1) A x
    have ht : t = fun _ : Fin 1 => t 0 := funext fun i =>
      congrArg t (Subsingleton.elim i 0)
    rw [ht]
    change (fun i => ℓ (ρ.affineAction A
      (VectorGroup.affinePoint (R := CommRingCat.of k) (d := 1) A (fun _ => t 0))
      (fun j => algebraMap k A (v j)) i)) ∈ W
    obtain ⟨N, hN⟩ := linearFunctional_affineAction_eq_sum ρ v
    rw [hN]
    exact W.sum_mem fun m _ => W.smul_mem _ (h m v hv)

/-- The coefficient orbit span of a vector in an actual additive-group representation. -/
def orbitSubmodule (v : n → k) : Submodule k (n → k) :=
  Submodule.span k (Set.range fun m : ℕ => dividedPower ρ m v)

/-- Every coefficient translate lies in the coefficient orbit span. -/
theorem dividedPower_mem_orbitSubmodule (v : n → k) (m : ℕ) :
    dividedPower ρ m v ∈ orbitSubmodule ρ v :=
  Submodule.subset_span ⟨m, rfl⟩

/-- The constant coefficient ensures that the orbit span contains its original vector. -/
theorem mem_orbitSubmodule (v : n → k) : v ∈ orbitSubmodule ρ v := by
  simpa only [dividedPower_zero, Module.End.one_apply] using
    dividedPower_mem_orbitSubmodule ρ v 0

/-- The coefficient orbit span is stable on every affine test algebra. -/
theorem isStableSubspace_orbitSubmodule (v : n → k) :
    IsStableSubspace ρ (orbitSubmodule ρ v) := by
  apply (isStableSubspace_iff_invariant_dividedPower ρ _).mpr
  intro m w hw
  have hs : orbitSubmodule ρ v ≤ (orbitSubmodule ρ v).comap (dividedPower ρ m) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change dividedPower ρ m (dividedPower ρ a v) ∈ orbitSubmodule ρ v
    rw [← Module.End.mul_apply, dividedPower_mul, LinearMap.smul_apply]
    exact (orbitSubmodule ρ v).smul_mem _ (dividedPower_mem_orbitSubmodule ρ v (m + a))
  exact hs hw

/-- Among stable subspaces, the coefficient orbit span is the least one containing
the original vector. -/
theorem orbitSubmodule_le_iff (v : n → k) (W : Submodule k (n → k))
    (hW : IsStableSubspace ρ W) :
    orbitSubmodule ρ v ≤ W ↔ v ∈ W := by
  constructor
  · intro h
    exact h (mem_orbitSubmodule ρ v)
  · intro hv
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    exact (isStableSubspace_iff_invariant_dividedPower ρ W).mp hW m v hv

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- In prime characteristic, the p-power coefficients detect stability over all
test algebras without an infinitude assumption. -/
theorem isStableSubspace_iff_invariant_pPowerOperator (W : Submodule k (n → k)) :
    IsStableSubspace ρ W ↔
      ∀ r : ℕ, ∀ v ∈ W, pPowerOperator ρ p r v ∈ W := by
  rw [isStableSubspace_iff_invariant_dividedPower,
    invariant_dividedPower_iff_invariant_pPowerOperator]

omit [Fact p.Prime] [CharP k p] in
/-- The coefficient fixed space is exactly the canonical fixed space on every
relative scheme test. -/
theorem mem_fixedSubmodule_iff_isFixedVector (v : n → k) :
    v ∈ AdditiveFixedVectors.fixedSubmodule ρ ↔ ρ.IsFixedVector v := by
  constructor
  · intro hv
    let A := VectorGroup.coordinateAlgebra (CommRingCat.of k) 1
    let j : (algSpec (CommRingCat.of k)).obj (op A) ≅
        (VectorGroup.groupScheme (CommRingCat.of k) 1).X := Iso.refl _
    apply (isFixedVector_iff_affine_model ρ j v).mpr
    exact affineAction_eq_of_mem_fixedSubmodule ρ hv A j.hom
  · intro hv
    apply (mem_fixedSubmodule_iff_affineAction ρ v).mpr
    exact fun A x => hv.affine A x

omit [Fact p.Prime] [CharP k p] in
/-- Equality with the existing canonical all-scheme fixed submodule. -/
theorem fixedSubmodule_eq :
    AdditiveFixedVectors.fixedSubmodule ρ = MatrixRepresentation.fixedSubmodule ρ := by
  ext v
  exact mem_fixedSubmodule_iff_isFixedVector ρ v

/-- The canonical all-scheme fixed vectors are exactly the common p-power kernels. -/
theorem isFixedVector_iff_pPowerOperator (v : n → k) :
    ρ.IsFixedVector v ↔ ∀ r : ℕ, pPowerOperator ρ p r v = 0 := by
  rw [← mem_fixedSubmodule_iff_isFixedVector, mem_fixedSubmodule_iff_pPowerOperator]

include p in
/-- The coefficient common-kernel construction gives a nonzero vector fixed on
every relative scheme test. -/
theorem exists_nonzero_isFixedVector [Nonempty n] :
    ∃ v : n → k, v ≠ 0 ∧ ρ.IsFixedVector v := by
  obtain ⟨v, hv, h⟩ := exists_nonzero_mem_fixedSubmodule ρ p
  exact ⟨v, hv, (mem_fixedSubmodule_iff_isFixedVector ρ v).mp h⟩

end Langlands.GroupScheme.MatrixRepresentation.AdditiveInvariantSubspaces

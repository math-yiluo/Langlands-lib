import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicStatement
import Mathlib.LinearAlgebra.Dimension.Finrank

/-! # Proofs of basic identities for actual Euler characteristics -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules.DerivedSections

variable {K : Type u} [Field K] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of K))

/-- Any actual cohomological vanishing bound is a finite summation cutoff. -/
theorem eulerCharacteristic_eq_sum_range (M : X.Modules)
    (hM : HasFiniteCohomology f M) (N : ℕ)
    (hN : ∀ n : ℕ, N ≤ n → IsZero ((relativeCohomology f n).obj M)) :
    eulerCharacteristic f M hM = ∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank K ((relativeCohomology f n).obj M) : ℤ) := by
  classical
  apply finsum_eq_sum_of_support_subset
  intro n hn
  simp only [Finset.mem_coe, Finset.mem_range]
  by_contra hlt
  let : Subsingleton ((relativeCohomology f n).obj M) :=
    ModuleCat.subsingleton_of_isZero (hN n (by omega))
  exact hn (by simp [Module.finrank_zero_of_subsingleton])

/-- An actual sheaf isomorphism transports the finite-cohomology condition. -/
theorem hasFiniteCohomology_of_iso {M N : X.Modules} (e : M ≅ N)
    (hM : HasFiniteCohomology f M) : HasFiniteCohomology f N := by
  constructor
  · intro n
    let : Module.Finite K ((relativeCohomology f n).obj M) := hM.1 n
    exact Module.Finite.equiv ((relativeCohomology f n).mapIso e).toLinearEquiv
  · obtain ⟨b, hb⟩ := hM.2
    exact ⟨b, fun n hn => IsZero.of_iso (hb n hn)
      ((relativeCohomology f n).mapIso e).symm⟩

/-- Actual sheaf isomorphisms preserve the Euler invariant. -/
theorem eulerCharacteristic_eq_of_iso {M N : X.Modules}
    (hM : HasFiniteCohomology f M) (hN : HasFiniteCohomology f N) (e : M ≅ N) :
    eulerCharacteristic f M hM = eulerCharacteristic f N hN := by
  unfold eulerCharacteristic
  apply finsum_congr
  intro n
  rw [((relativeCohomology f n).mapIso e).toLinearEquiv.finrank_eq]

/-- The five elementary identities hold for the actual Euler invariant. -/
theorem eulerCharacteristicBasic : EulerCharacteristicBasicStatement.{u} := by
  intro K _ X f
  refine ⟨eulerCharacteristic_eq_sum_range f, ?_, ?_, ?_, ?_⟩
  · intro M N e
    exact ⟨hasFiniteCohomology_of_iso f e, hasFiniteCohomology_of_iso f e.symm⟩
  · intro M N hM hN e
    exact eulerCharacteristic_eq_of_iso f hM hN e
  · intro M hM hzero
    simpa using eulerCharacteristic_eq_sum_range f M hM 0 (fun n _ => hzero n)
  · intro M hM hpos
    simpa using eulerCharacteristic_eq_sum_range f M hM 1
      (fun n hn => hpos n (by omega))

end Langlands.AlgebraicGeometry.Modules.DerivedSections

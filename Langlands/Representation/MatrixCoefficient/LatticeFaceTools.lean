import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Int.Interval
import Mathlib.Data.Pi.Interval
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-! # Finite representatives and coordinates for lattice faces -/

namespace Langlands.LatticeFaceTools

/-- Bounded values of finitely many integral linear forms have finitely many
representatives modulo their common kernel. -/
theorem exists_finite_representatives {L I : Type*} [AddCommGroup L] [Fintype I]
    (f : L →+ (I → ℤ)) (T : ℤ) :
    ∃ M : Set L, M.Finite ∧
      ∀ y : L, (∀ i, 0 ≤ f y i ∧ f y i ≤ T) →
        ∃ m ∈ M, f (y - m) = 0 := by
  classical
  let s : Set L := {y | ∀ i, 0 ≤ f y i ∧ f y i ≤ T}
  have hu : (f '' s).Finite := by
    apply (Set.finite_Icc (0 : I → ℤ) (fun _ => T)).subset
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨fun i => (hy i).1, fun i => (hy i).2⟩
  obtain ⟨M, hMs, hM, heq⟩ := hu.exists_subset_finite_image_eq (Set.Subset.refl _)
  refine ⟨M, hM, fun y hy => ?_⟩
  have hyim : f y ∈ f '' M := heq.symm ▸ ⟨y, hy, rfl⟩
  obtain ⟨m, hm, hmy⟩ := hyim
  exact ⟨m, hm, by rw [map_sub, hmy, sub_self]⟩

/-- Smith normal form supplies a basis of any integral submodule whose
coordinates are bounded by ambient integral linear forms. -/
theorem exists_basis_coord_bound {L I : Type*} [AddCommGroup L]
    [Finite I] (b : Module.Basis I ℤ L) (K : Submodule ℤ L) :
    letI : Module ℤ K := K.module
    ∃ (d : ℕ) (bK : Module.Basis (Fin d) ℤ K) (ell : Fin d → L →ₗ[ℤ] ℤ),
      ∀ (x : K) (j : Fin d), |(bK.repr x j : ℝ)| ≤ |(ell j x : ℝ)| := by
  let : Module ℤ K := K.module
  obtain ⟨d, snf⟩ := K.smithNormalForm b
  refine ⟨d, snf.bN, fun j => snf.bM.coord (snf.f j), fun x j => ?_⟩
  have ha : snf.a j ≠ 0 := by
    intro ha
    apply snf.bN.ne_zero j
    apply Subtype.ext
    simpa only [ha, zero_smul, Submodule.coe_zero] using snf.snf j
  have hmul : snf.bM.repr (x : L) (snf.f j) = snf.a j * snf.bN.repr x j := by
    simpa only [map_smul, Finsupp.smul_apply, smul_eq_mul] using
      snf.repr_apply_embedding_eq_repr_smul x (i := j)
  change |(snf.bN.repr x j : ℝ)| ≤ |(snf.bM.repr (x : L) (snf.f j) : ℝ)|
  rw [hmul, Int.cast_mul, abs_mul]
  have hapos : 0 < |snf.a j| := abs_pos.mpr ha
  have hage : (1 : ℝ) ≤ |(snf.a j : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast hapos
  nlinarith [abs_nonneg (snf.bN.repr x j : ℝ)]

end Langlands.LatticeFaceTools

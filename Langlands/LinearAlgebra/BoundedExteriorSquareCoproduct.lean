import Langlands.LinearAlgebra.BoundedCreationContraction
import Langlands.LinearAlgebra.ExteriorSquareCoproduct

/-! # Exterior-square comparison from bounded creation and contraction -/

noncomputable section

open scoped TensorProduct

namespace Langlands.LinearAlgebra.BoundedExteriorSquareCoproduct

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  {M : ℕ → Type*} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (c : ∀ (_ : ι) (n : ℕ), M n →ₗ[R] M (n + 1))
  (d : ∀ (_ : ι) (n : ℕ), M (n + 1) →ₗ[R] M n)
  (hrel : ∀ i j n,
    (d i (n + 1)).comp (c j (n + 1)) + (c j n).comp (d i n) =
      if i = j then LinearMap.id else 0)
  (hbound : ∀ n, Fintype.card ι < n → Subsingleton (M n))
  (cup : (M 1) [⋀^Fin 2]→ₗ[R] M 2)
  (v : ι → M 1)
  (hcup : ∀ i x, c i 1 x = cup ![v i, x])

include hrel hbound hcup

/-- The exterior cup lift is surjective when its image contains the degree-one
creation images in a bounded creation-contraction family. The vectors `v`
need not be assumed to form a basis. -/
theorem cupLift_surjective :
    Function.Surjective (exteriorPower.alternatingMapLinearEquiv cup) := by
  apply LinearMap.range_eq_top.mp
  apply top_unique
  rw [← BoundedCreationContraction.iSup_range_degreeOne_eq_top c d hrel hbound]
  refine iSup_le fun i => ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨exteriorPower.ιMulti R 2 ![v i, x], ?_⟩
  rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact (hcup i x).symm

variable [Module.Free R (M 1)]

/-- The inverse exterior cup equivalence obtained from boundedness, the
creation-contraction relations, and a compatible antisymmetrization detector. -/
def cupEquiv
    (detect : M 2 →ₗ[R] ⨂[R]^2 (M 1))
    (hdetect : ∀ w, detect (cup w) =
      exteriorPower.toTensorPower R (M 1) 2 (exteriorPower.ιMulti R 2 w)) :
    M 2 ≃ₗ[R] ⋀[R]^2 (M 1) :=
  ExteriorSquareCoproduct.cupEquiv cup detect
    (cupLift_surjective c d hrel hbound cup v hcup) hdetect

@[simp]
theorem cupEquiv_cup
    (detect : M 2 →ₗ[R] ⨂[R]^2 (M 1))
    (hdetect : ∀ w, detect (cup w) =
      exteriorPower.toTensorPower R (M 1) 2 (exteriorPower.ιMulti R 2 w))
    (w : Fin 2 → M 1) :
    cupEquiv c d hrel hbound cup v hcup detect hdetect (cup w) =
      exteriorPower.ιMulti R 2 w :=
  ExteriorSquareCoproduct.cupEquiv_cup cup detect
    (cupLift_surjective c d hrel hbound cup v hcup) hdetect w

/-- The three coproduct formulas extend from cup monomials using bounded
creation-contraction generation, without a separate surjectivity premise. -/
theorem exists_comparison
    {P : Type*} [AddCommGroup P] [Module R P]
    (κ : P ≃ₗ[R] M 2 × (⨂[R]^2 (M 1)) × M 2)
    (p₁ p₂ m : M 2 →ₗ[R] P)
    (hp₁ : ∀ w, κ (p₁ (cup w)) = (cup w, 0, 0))
    (hp₂ : ∀ w, κ (p₂ (cup w)) = (0, 0, cup w))
    (hm : ∀ w, κ (m (cup w)) =
      (cup w, exteriorPower.toTensorPower R (M 1) 2
        (exteriorPower.ιMulti R 2 w), cup w)) :
    ∃ e : M 2 ≃ₗ[R] ⋀[R]^2 (M 1),
      (∀ x, κ (p₁ x) = (x, 0, 0)) ∧
      (∀ x, κ (p₂ x) = (0, 0, x)) ∧
      (∀ x, κ (m x) =
        (x, exteriorPower.toTensorPower R (M 1) 2 (e x), x)) :=
  ExteriorSquareCoproduct.exists_comparison_of_cup_generators cup
    (cupLift_surjective c d hrel hbound cup v hcup) κ p₁ p₂ m hp₁ hp₂ hm

end Langlands.LinearAlgebra.BoundedExteriorSquareCoproduct

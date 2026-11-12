import Langlands.GroupScheme.Quaternionic.RationalIsometry
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.Quaternionic.IsometryRowAction
import Langlands.GroupScheme.GaloisPointRational

/-!
# Rational points of the isometry group

The rational points of the isometry group scheme `O(q) = σ.isometryGroup q` are identified with
the subgroup `rationalIsometryGroup σ q` of `GL_n(D)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.Quaternionic

namespace FirstKindInvolution.Eichler

section Lid

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]

/-- Over `K` itself, base change of a subspace is transported to the subspace by `lid`. -/
theorem lid_mem_baseChange_iff (M : Submodule K A) (y : K ⊗[K] A) :
    y ∈ M.baseChange K ↔ Algebra.TensorProduct.lid K A y ∈ M := by
  constructor
  · intro hy
    unfold Submodule.baseChange at hy
    obtain ⟨z, rfl⟩ := hy
    induction z with
    | tmul k m => simpa using M.smul_mem k m.2
    | add x y hx hy => simpa using M.add_mem hx hy
  · intro hy
    have : y = (1 : K) ⊗ₜ[K] Algebra.TensorProduct.lid K A y := by
      rw [← Algebra.TensorProduct.lid_symm_apply, AlgEquiv.symm_apply_apply]
    rw [this]
    exact Submodule.tmul_mem_baseChange_of_mem _ hy

end Lid

section Points

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D] [FiniteDimensional K D]
  (σ : FirstKindInvolution K D) {n : Type} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n)

omit [FiniteDimensional K D] in
/-- A unit of `K ⊗[K] M_n(D)` satisfies the isometry condition of `O(q)` exactly when its image
under `lid` is a rational isometry. -/
theorem map_lid_mem_rationalIsometryGroup_iff (y : (K ⊗[K] Matrix n n D)ˣ) :
    Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).toMonoidHom y ∈
        rationalIsometryGroup σ q ↔
      IsometryCut.defect (σ.matrix n) (Quotient.out q) (y : K ⊗[K] Matrix n n D) ∈
        (σ.quadraticKernel n).baseChange K := by
  rw [lid_mem_baseChange_iff, IsometryCut.lid_defect]
  rfl

/-- The rational points of the isometry family of `O(q)` are the rational isometries. -/
def isometryFamilyEquiv :
    IsometryCut.isometryFamily (IsometryCut.isStable_alternatingSubspace (τ := σ.matrix n))
        (Quotient.out q) (CommAlgCat.of (CommRingCat.of K) K) ≃*
      rationalIsometryGroup σ q :=
  ((Units.mapEquiv (Algebra.TensorProduct.lid K (Matrix n n D)).toMulEquiv).subgroupMap
    _).trans (MulEquiv.subgroupCongr (by
      ext u
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact (map_lid_mem_rationalIsometryGroup_iff σ q y).2 hy
      · intro hu
        refine ⟨Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).symm.toMonoidHom u, ?_, ?_⟩
        · change IsometryCut.defect (σ.matrix n) (Quotient.out q)
            ((Units.map (Algebra.TensorProduct.lid K (Matrix n n D)).symm.toMulEquiv.toMonoidHom u :
              (K ⊗[K] Matrix n n D)ˣ) : K ⊗[K] Matrix n n D) ∈ (σ.quadraticKernel n).baseChange K
          rw [← map_lid_mem_rationalIsometryGroup_iff σ q]
          convert hu using 1
          ext
          simp
        · ext
          simp))

/-- **Rational points of `O(q)`.** The `K`-points of the isometry group scheme are the rational
isometries of `q`. -/
def isometryGroupRationalPointsEquiv :
    rationalPoints (σ.isometryGroup q) ≃* rationalIsometryGroup σ q :=
  (GaloisPointComparison.rationalCoeffEquiv K (σ.isometryGroup q)).trans
    ((Corepresented.affinePointsEquiv _ _ (CommAlgCat.of (CommRingCat.of K) K)).trans
      (isometryFamilyEquiv σ q))

end Points

end FirstKindInvolution.Eichler

end Langlands.GroupScheme.Quaternionic

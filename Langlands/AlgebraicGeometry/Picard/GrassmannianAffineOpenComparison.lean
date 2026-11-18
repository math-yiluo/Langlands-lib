import Langlands.AlgebraicGeometry.Picard.BaseChangeMaps
import Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminantKernelComparison

/-! # Grassmannian points over the actual affine open section algebra -/

noncomputable section

universe u

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

open Module.Grassmannian.ProjectiveEmbedding
open Scheme.TwoAffineOpenCover

variable {R : CommRingCat.{u}} {E : Type u} [AddCommGroup E] [Module R E] {k : ℕ}
  (D : Rep R E k) {X : Scheme.{u}} (f : X ⟶ D.Gr)
  (p : X ⟶ Spec R) (hf : f ≫ D.p = p) (U : X.affineOpens)

include hf

/-- The actual affine chart followed by a relative Grassmannian map is a point
over the coefficient algebra induced by the parameter scheme's structure map. -/
theorem affineOpenPoint_over :
    U.2.fromSpec ≫ f ≫ D.p =
      Spec.map (CommRingCat.ofHom (algebraOfHom p U).algebraMap) := by
  rw [hf]
  exact LinearSystemCechModule.affPt_comp p U

/-- The Grassmannian point of an affine open, with the actual coefficient algebra. -/
def affineOpenPoint :
    letI := algebraOfHom p U
    Module.Grassmannian Γ(X, U) (Γ(X, U) ⊗[R] E) k := by
  letI := algebraOfHom p U
  exact (D.pt Γ(X, U)).symm
    ⟨U.2.fromSpec ≫ f, (Category.assoc _ _ _).trans (affineOpenPoint_over D f p hf U)⟩

/-- Its representing scheme map is the composite of the actual chart and the
relative Grassmannian map. -/
theorem pt_affineOpenPoint :
    letI := algebraOfHom p U
    (D.pt Γ(X, U) (affineOpenPoint D f p hf U)).1 = U.2.fromSpec ≫ f := by
  let := algebraOfHom p U
  unfold affineOpenPoint
  rw [Equiv.apply_symm_apply]

private theorem algOfHom_eq :
    algOfHom D (U.2.fromSpec ≫ f) = algebraOfHom p U := by
  apply Algebra.algebra_ext
  intro r
  have h := (specMap_algebraMap_algOfHom D (U.2.fromSpec ≫ f)).trans
    ((Category.assoc _ _ _).trans (affineOpenPoint_over D f p hf U))
  exact ConcreteCategory.congr_hom (Spec.map_injective h) r

/-- A kernel comparison expressed in the actual coefficient algebra gives the
Grassmannian determinant's affine-point comparison. -/
theorem hasAffinePointComparison_of_affineOpenTensorKernels
    (N : X.Modules) (q : E → Γ(N, ⊤))
    (hT : ∀ U : X.affineOpens,
      letI := algebraOfHom p U
      ∃ T : Γ(X, U) ⊗[R] E →ₗ[Γ(X, U)] Γ(N, U),
        Function.Surjective T ∧ T.ker = (affineOpenPoint D f p hf U).toSubmodule ∧
          ∀ m : E, T ((1 : Γ(X, U)) ⊗ₜ[R] m) =
            N.presheaf.map (homOfLE (show (U : X.Opens) ≤ ⊤ from le_top)).op (q m)) :
    HasAffinePointComparison D f N q := by
  apply hasAffinePointComparison_of_tensor_kernels
  intro W hW
  let U : X.affineOpens := ⟨W, hW⟩
  let j := hW.fromSpec ≫ f
  have compare (A : Algebra R Γ(X, W))
      (hA : A = algebraOfHom p W)
      (hj : j ≫ D.p = Spec.map (CommRingCat.ofHom A.algebraMap)) :
      letI := A
      ∃ T : Γ(X, W) ⊗[R] E →ₗ[Γ(X, W)] Γ(N, W),
        Function.Surjective T ∧ T.ker = ((D.pt Γ(X, W)).symm ⟨j, hj⟩).toSubmodule ∧
          ∀ m : E, T ((1 : Γ(X, W)) ⊗ₜ[R] m) =
            N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q m) := by
    subst A
    exact hT U
  exact compare (algOfHom D j) (algOfHom_eq D f p hf U)
    (specMap_algebraMap_algOfHom D j).symm

end Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

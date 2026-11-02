import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLevi
import Langlands.GroupScheme.CorepresentedAffineComparison
import Langlands.GroupScheme.Lie.DualNumberKernel

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

set_option backward.isDefEq.respectTransparency false

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)
variable (R : Type u) [CommRing R] [Algebra F R]

/-- Matrix coordinates over the original affine test algebra. -/
def affineMatrixCoordinates : Lie.AffinePoints (groupScheme b c) R →*
    GL (Fin 2) (E ⊗[F] R) :=
  (Matrix.GeneralLinearGroup.map (tensorCoefficientMap
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) R)).toAlgHom).toRingHom).comp
    (matrixCoordinates b c ((algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of (CommRingCat.of F) R))))

/-- Affine matrix coordinates distinguish points. -/
theorem affineMatrixCoordinates_injective :
    Function.Injective (affineMatrixCoordinates b c R) := by
  intro x y h
  apply (pointsEquiv b c _).injective
  apply Subtype.ext
  apply Units.ext
  have h' := congrArg Units.val h
  ext i j
  apply (Algebra.TensorProduct.congr (AlgEquiv.refl : E ≃ₐ[F] E)
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) R))).injective
  exact congrFun (congrFun h' i) j

variable {R} {S : Type u} [CommRing S] [Algebra F S]

private theorem affineSections_naturality (f : R →ₐ[F] S) (z :
    ((algΓ (CommRingCat.of F)).obj ((algSpec (CommRingCat.of F)).obj
      (op (CommAlgCat.of (CommRingCat.of F) R)))).unop) :
    Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) S)
      (((algΓ (CommRingCat.of F)).map
        ((algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom f).op)).unop.hom z) =
      f (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) R) z) := by
  change (Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of F) S)).hom.hom.toRingHom
    (((algΓ (CommRingCat.of F)).map
      ((algSpec (CommRingCat.of F)).map (CommAlgCat.ofHom f).op)).unop.hom z) =
    f ((Corepresented.affineSectionsIso (CommAlgCat.of (CommRingCat.of F) R)).hom.hom.toRingHom z)
  rw [Corepresented.affineSectionsIso_hom_ringHom,
    Corepresented.affineSectionsIso_hom_ringHom]
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
    ((Spec.map (CommRingCat.ofHom f.toRingHom)).appTop z) =
      f ((Scheme.ΓSpecIso (CommRingCat.of R)).hom z)
  rw [← CommRingCat.comp_apply, Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply]
  rfl

/-- Affine coordinates change by applying the algebra map to the right tensor factor. -/
theorem affineMatrixCoordinates_naturality (f : R →ₐ[F] S)
    (x : Lie.AffinePoints (groupScheme b c) R) :
    affineMatrixCoordinates b c S (Lie.affineMap _ f x) =
      Matrix.GeneralLinearGroup.map (tensorCoefficientMap f).toRingHom
        (affineMatrixCoordinates b c R x) := by
  apply Units.ext
  change ((matrixCoordinates b c _ (Lie.affineMap _ f x)).val.map _) = _
  rw [Lie.affineMap_apply, matrixCoordinates_naturality]
  ext i j
  change tensorCoefficientMap _ (tensorCoefficientMap _ (matrixCoordinates b c _ x i j)) =
    tensorCoefficientMap f (tensorCoefficientMap _ (matrixCoordinates b c _ x i j))
  induction (matrixCoordinates b c _ x i j) using TensorProduct.inductionOn with
  | tmul e r =>
    simp only [tensorCoefficientMap_tmul]
    exact congrArg (fun r => e ⊗ₜ[F] r) (affineSections_naturality f r)
  | add z w hz hw => simp [hz, hw]

/-- Every affine coordinate matrix satisfies the unitary equation. -/
theorem affineMatrixCoordinates_mem (x : Lie.AffinePoints (groupScheme b c) R) :
    affineMatrixCoordinates b c R x ∈ matrixPoints R c := by
  rw [matrixPoints, Langlands.Shimura.AlgebraInvolution.mem_unitary_iff]
  have h := (Langlands.Shimura.AlgebraInvolution.mem_unitary_iff _ _).mp
    (pointsEquiv b c _ x).property
  have h' := congrArg (RingHom.mapMatrix (m := Fin 2) (tensorCoefficientMap
    (Corepresented.affineSectionsAlgEquiv (CommAlgCat.of (CommRingCat.of F) R)).toAlgHom).toRingHom) h
  rw [map_mul, map_one] at h'
  change (affineMatrixCoordinates b c R x).val * _ = 1 at h' ⊢
  convert h' using 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [matrixInvolution, adjoint, tensorCoefficientMap_scalarConjugation,
      affineMatrixCoordinates, matrixCoordinates]

/-- The inverse coordinate matrix is the conjugate adjoint. -/
theorem affineMatrixCoordinates_inv (x : Lie.AffinePoints (groupScheme b c) R) :
    (affineMatrixCoordinates b c R x⁻¹).val =
      adjoint (scalarConjugation R c) (affineMatrixCoordinates b c R x).val := by
  rw [map_inv]
  have h := (Langlands.Shimura.AlgebraInvolution.mem_unitary_iff _ _).mp
    (affineMatrixCoordinates_mem b c x)
  change (affineMatrixCoordinates b c R x).val *
    adjoint (scalarConjugation R c) (affineMatrixCoordinates b c R x).val = 1 at h
  calc
    _ = (affineMatrixCoordinates b c R x)⁻¹.val * 1 := (mul_one _).symm
    _ = _ := by rw [← h, ← mul_assoc, Units.inv_mul, one_mul]

end Langlands.GroupScheme.QuasiSplitUnitary

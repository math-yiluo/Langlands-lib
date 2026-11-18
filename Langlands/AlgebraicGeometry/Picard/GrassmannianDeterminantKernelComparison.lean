import Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminantFrames
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Actual quotient comparison from affine generator kernels -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

/-- A supplied equality with the actual kernel gives the actual quotient
linear equivalence determined by the original surjective linear map. -/
def quotientByKernelEquiv {A : Type u} [CommRing A]
    {P Q : Type u} [AddCommGroup P] [AddCommGroup Q] [Module A P] [Module A Q]
    (K : Submodule A P) (T : P →ₗ[A] Q) (hT : Function.Surjective T)
    (hK : T.ker = K) : (P ⧸ K) ≃ₗ[A] Q :=
  (Submodule.quotEquivOfEq K T.ker hK.symm) ≪≫ₗ T.quotKerEquivOfSurjective hT

@[simp]
theorem quotientByKernelEquiv_mkQ {A : Type u} [CommRing A]
    {P Q : Type u} [AddCommGroup P] [AddCommGroup Q] [Module A P] [Module A Q]
    (K : Submodule A P) (T : P →ₗ[A] Q) (hT : Function.Surjective T)
    (hK : T.ker = K) (x : P) :
    quotientByKernelEquiv K T hT hK (K.mkQ x) = T x := by
  simp [quotientByKernelEquiv, Submodule.mkQ_apply]

open Module.Grassmannian.ProjectiveEmbedding

variable {R E : Type u} [CommRing R] [AddCommGroup E] [Module R E] {k : ℕ}
    (D : Rep R E k) {X : Scheme.{u}} (f : X ⟶ D.Gr) (N : X.Modules)
    (q : E → Γ(N, ⊤))

/-- Surjective actual tensor generator maps with the classified kernels and
specified generator values supply the actual affine-point quotient comparison. -/
theorem hasAffinePointComparison_of_tensor_kernels
    (hT : ∀ (W : X.Opens) (hW : IsAffineOpen W),
      letI := algOfHom D (hW.fromSpec ≫ f)
      ∃ T : Γ(X, W) ⊗[R] E →ₗ[Γ(X, W)] Γ(N, W),
        Function.Surjective T ∧ T.ker = (ptOf D (hW.fromSpec ≫ f)).toSubmodule ∧
          ∀ m : E, T ((1 : Γ(X, W)) ⊗ₜ[R] m) =
            N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q m)) :
    HasAffinePointComparison D f N q := by
  intro W hW
  let := algOfHom D (hW.fromSpec ≫ f)
  obtain ⟨T, hsurj, hker, hgen⟩ := hT W hW
  refine ⟨quotientByKernelEquiv (ptOf D (hW.fromSpec ≫ f)).toSubmodule T hsurj hker,
    fun m => ?_⟩
  rw [quotientByKernelEquiv_mkQ]
  exact hgen m

/-- The actual classified tensor kernels give actual chosen determinant
ampleness, once their generator maps are supplied. -/
theorem finiteLocallyFreeDeterminant_isAmple_of_tensor_kernels
    [CompactSpace X] [IsAffineHom f] (hN : Langlands.Scheme.Modules.HasFiniteLocalBasis N)
    (hT : ∀ (W : X.Opens) (hW : IsAffineOpen W),
      letI := algOfHom D (hW.fromSpec ≫ f)
      ∃ T : Γ(X, W) ⊗[R] E →ₗ[Γ(X, W)] Γ(N, W),
        Function.Surjective T ∧ T.ker = (ptOf D (hW.fromSpec ≫ f)).toSubmodule ∧
          ∀ m : E, T ((1 : Γ(X, W)) ⊗ₜ[R] m) =
            N.presheaf.map (homOfLE (show W ≤ ⊤ from le_top)).op (q m)) :
    (finiteLocallyFreeDeterminant hN).IsAmple :=
  finiteLocallyFreeDeterminant_isAmple_of_affinePointComparison D f N q hN
    (hasAffinePointComparison_of_tensor_kernels D f N q hT)

end Langlands.AlgebraicGeometry.Picard.GrassmannianDeterminant

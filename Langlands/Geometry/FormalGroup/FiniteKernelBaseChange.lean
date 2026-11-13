import Langlands.Geometry.FormalGroup.CoefficientPoints
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Tensor base change of actual finite kernel representations -/

noncomputable section

universe u v

namespace Langlands.FormalGroup.ModuleLaw

open CategoryTheory
open scoped TensorProduct

variable {O : Type u} [CommRing O]
variable {R S : Type v} [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {M : ModuleLaw O R σ} {N : ModuleLaw O R τ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- The actual tensor algebra along the chosen coefficient homomorphism. -/
def coefficientTensorAlgebra (φ : R →ₐ[O] S) (C : CommAlgCat.{v} R) :
    CommAlgCat.{v} S :=
  letI : Algebra R S := φ.toRingHom.toAlgebra
  CommAlgCat.of S (S ⊗[R] C)

/-- The tensor algebra's universal property, with the restricted structural map. -/
def coefficientTensorHomEquiv (φ : R →ₐ[O] S) (C : CommAlgCat.{v} R)
    (A : CommAlgCat.{v} S) :
    (coefficientTensorAlgebra φ C ⟶ A) ≃ (C ⟶ restrictCoefficientAlgebra φ A) := by
  letI : Algebra R S := φ.toRingHom.toAlgebra
  letI : Algebra R A := Algebra.compHom A φ.toRingHom
  letI : IsScalarTower R S A := IsScalarTower.of_algebraMap_eq' rfl
  exact {
    toFun := fun g => { hom' := (AlgHom.liftEquiv R S C A).symm g.hom }
    invFun := fun g => { hom' := (AlgHom.liftEquiv R S C A) g.hom }
    left_inv := fun g => CommAlgCat.hom_ext
      ((AlgHom.liftEquiv R S C A).apply_symm_apply g.hom)
    right_inv := fun g => CommAlgCat.hom_ext
      ((AlgHom.liftEquiv R S C A).symm_apply_apply g.hom) }

/-- Postcomposition commutes with tensor restriction. -/
theorem coefficientTensorHomEquiv_comp (φ : R →ₐ[O] S) (C : CommAlgCat.{v} R)
    {A B : CommAlgCat.{v} S} (g : coefficientTensorAlgebra φ C ⟶ A) (ψ : A ⟶ B) :
    coefficientTensorHomEquiv φ C B (g ≫ ψ) =
      coefficientTensorHomEquiv φ C A g ≫ restrictCoefficientMap φ ψ := rfl

namespace Hom.FiniteKernelModel

variable {f : Hom M N}

/-- Tensoring the actual kernel coordinate algebra corepresents the new kernel. -/
def baseChange (K : FiniteKernelModel f) (φ : R →ₐ[O] S) :
    FiniteKernelModel (f.map φ) := by
  letI : Algebra R S := φ.toRingHom.toAlgebra
  refine {
    coordinateAlgebra := coefficientTensorAlgebra φ K.coordinateAlgebra
    finite := by
      change Module.Finite S (S ⊗[R] K.coordinateAlgebra)
      infer_instance
    projective := by
      change Module.Projective S (S ⊗[R] K.coordinateAlgebra)
      infer_instance
    represents := ?_ }
  apply Functor.CorepresentableBy.ofIso
    (F := restrictCoefficientFunctor φ ⋙ f.kernelSetFunctor)
    (e' := (f.coefficientKernelIso φ).symm)
  exact {
    homEquiv := fun {A} =>
      (coefficientTensorHomEquiv φ K.coordinateAlgebra A).trans K.represents.homEquiv
    homEquiv_comp := fun ψ g => by
      change K.represents.homEquiv
        (coefficientTensorHomEquiv φ K.coordinateAlgebra _ (g ≫ ψ)) = _
      rw [coefficientTensorHomEquiv_comp, K.represents.homEquiv_comp]
      rfl }

/-- Kernel rank after tensor base change is the original rank at the image prime. -/
theorem rank_baseChange (K : FiniteKernelModel f) (φ : R →ₐ[O] S)
    (p : PrimeSpectrum S) :
    (K.baseChange φ).rank p = K.rank (p.comap φ.toRingHom) := by
  let : Algebra R S := φ.toRingHom.toAlgebra
  exact Module.rankAtStalk_baseChange (M := K.coordinateAlgebra) p

end Hom.FiniteKernelModel

namespace Hom

/-- A finite locally free actual kernel remains such after coefficient extension. -/
theorem HasFiniteLocallyFreeKernel.map {f : Hom M N}
    (hf : f.HasFiniteLocallyFreeKernel) (φ : R →ₐ[O] S) :
    (f.map φ).HasFiniteLocallyFreeKernel := by
  obtain ⟨K⟩ := hf
  exact ⟨K.baseChange φ⟩

/-- Constant actual kernel ranks are preserved by arbitrary coefficient extension. -/
theorem HasKernelRank.map {f : Hom M N} {n : ℕ}
    (hf : f.HasKernelRank n) (φ : R →ₐ[O] S) : (f.map φ).HasKernelRank n := by
  obtain ⟨K, hK⟩ := hf
  exact ⟨K.baseChange φ, fun p => (K.rank_baseChange φ p).trans (hK _)⟩

end Hom

end Langlands.FormalGroup.ModuleLaw

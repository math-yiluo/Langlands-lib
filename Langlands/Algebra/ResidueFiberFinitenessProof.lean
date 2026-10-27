import Langlands.Algebra.ResidueFiberFinitenessStatement
import Langlands.Algebra.EssFinitePresentationBaseChangeProof

/-! # Finiteness of the actual residue-fibre arrow and module: proof -/

universe u v w z

open scoped TensorProduct
open IsLocalRing

namespace Langlands.Algebra

section Comparison

variable (R S K T : Type*) [CommRing R] [CommRing S] [CommRing K] [CommRing T]
  [Algebra R S] [Algebra R K] [Algebra R T] [Algebra S T] [IsScalarTower R S T]

/-- The canonical comparison `(S ⊗[R] K) ⊗[S] T ≃ T ⊗[R] K`, as a ring isomorphism. -/
noncomputable def upperFiberBaseChangeRingEquiv : (S ⊗[R] K) ⊗[S] T ≃+* T ⊗[R] K :=
  ((_root_.Algebra.TensorProduct.comm S (S ⊗[R] K) T).trans
    (_root_.Algebra.TensorProduct.cancelBaseChange R S S T K)).toRingEquiv

@[simp] theorem upperFiberBaseChangeRingEquiv_tmul (s : S) (a : K) (t : T) :
    upperFiberBaseChangeRingEquiv R S K T ((s ⊗ₜ[R] a) ⊗ₜ[S] t) =
      (algebraMap S T s * t) ⊗ₜ[R] a := by
  simp [upperFiberBaseChangeRingEquiv, Algebra.smul_def]

@[simp] theorem upperFiberBaseChangeRingEquiv_symm_tmul (t : T) (a : K) :
    (upperFiberBaseChangeRingEquiv R S K T).symm (t ⊗ₜ[R] a) =
      (1 ⊗ₜ[R] a) ⊗ₜ[S] t := rfl

/-- The comparison `(S ⊗[R] K) ⊗[S] T ≃ₐ[S ⊗[R] K] T ⊗[R] K`, where the source has its
left-factor algebra structure and the target is an algebra through the actual arrow
`ResidueFiberTensor.upperMap R S K T`. -/
noncomputable def upperFiberBaseChangeEquiv :
    letI := ResidueFiberTensor.upperAlgebra R S K T
    (S ⊗[R] K) ⊗[S] T ≃ₐ[S ⊗[R] K] T ⊗[R] K :=
  letI := ResidueFiberTensor.upperAlgebra R S K T
  AlgEquiv.ofRingEquiv (f := upperFiberBaseChangeRingEquiv R S K T) fun x => by
    change upperFiberBaseChangeRingEquiv R S K T (x ⊗ₜ[S] 1) =
      ResidueFiberTensor.upperMap R S K T x
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp [TensorProduct.add_tmul, hx, hy]

@[simp] theorem upperFiberBaseChangeEquiv_tmul (s : S) (a : K) (t : T) :
    upperFiberBaseChangeEquiv R S K T ((s ⊗ₜ[R] a) ⊗ₜ[S] t) =
      (algebraMap S T s * t) ⊗ₜ[R] a :=
  upperFiberBaseChangeRingEquiv_tmul R S K T s a t

@[simp] theorem upperFiberBaseChangeEquiv_symm_tmul (t : T) (a : K) :
    letI := ResidueFiberTensor.upperAlgebra R S K T
    (upperFiberBaseChangeEquiv R S K T).symm (t ⊗ₜ[R] a) = (1 ⊗ₜ[R] a) ⊗ₜ[S] t := rfl

end Comparison

/-- The exact published finiteness proposition for the actual residue-fibre arrow and
module. -/
theorem residueFiberFiniteness : ResidueFiberFinitenessStatement.{u, v, w, z} := by
  intro R S T M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hT hM
  let := ResidueFiberTensor.upperAlgebra R S (ResidueField R) T
  let := ResidueFiberTensor.rawModule R T (ResidueField R) M
  refine ⟨?_, ?_⟩
  · exact essFinitePresentation_of_algEquiv
      (upperFiberBaseChangeEquiv R S (ResidueField R) T)
      (essFinitePresentation_baseChange (S ⊗[R] ResidueField R) hT)
  · exact Module.FinitePresentation.of_equiv
      (ResidueFiberTensor.linearComparison R T (ResidueField R) M)

example : ResidueFiberFinitenessStatement.{u, v, w, z} :=
  @residueFiberFiniteness.{u, v, w, z}

end Langlands.Algebra

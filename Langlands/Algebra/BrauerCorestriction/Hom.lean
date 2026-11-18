import Langlands.Algebra.BrauerCorestriction.Identity
import Langlands.Algebra.BrauerGroup

/-!
# Corestriction as a homomorphism of Brauer groups

With the abelian group law on the actual Brauer quotient (neutral class the ground field, sum
represented by the tensor product), the corestriction map of `BrauerClass` is an additive group
homomorphism, represented on actual central simple algebras by the tensor descent.
-/

universe u

open TensorProduct Langlands.Brauer

namespace Langlands.BrauerCorestriction

variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [Algebra.IsSeparable K L]

/-- Class computation: the corestriction of the class of `A` is the class of its tensor
descent. -/
theorem cor_classOf (A : CSA.{u, u} L) : cor K L (classOf A) = classOf (corCSA K L A) := rfl

/-- The tensor descent of a tensor product is isomorphic to the tensor product of the
descents, as actual central simple `K`-algebras. -/
noncomputable def corCSATensorEquiv (A B : CSA.{u, u} L) :
    corCSA K L (tensor A B) ≃ₐ[K] tensor (corCSA K L A) (corCSA K L B) := by
  let N := canonicalClosure K L
  let e₀ : (tensor A B : Type u) ≃ₐ[L] ((A : Type u) ⊗[L] (B : Type u)) := AlgEquiv.refl
  let eS : (corCSA K L (tensor A B) : Type u) ≃ₐ[K] corAlg K L N (tensor A B) := AlgEquiv.refl
  let e₁ : corAlg K L N (tensor A B) ≃ₐ[K] corAlg K L N ((A : Type u) ⊗[L] (B : Type u)) :=
    corEquiv K L N e₀
  let e₂ := (corMulEquiv K L N A B).symm
  let eA : corAlg K L N A ≃ₐ[K] (corCSA K L A : Type u) := AlgEquiv.refl
  let eB : corAlg K L N B ≃ₐ[K] (corCSA K L B : Type u) := AlgEquiv.refl
  let e₃ := Algebra.TensorProduct.congr eA eB
  let eT : ((corCSA K L A : Type u) ⊗[K] (corCSA K L B : Type u)) ≃ₐ[K]
      (tensor (corCSA K L A) (corCSA K L B) : Type u) := AlgEquiv.refl
  exact eS.trans (e₁.trans (e₂.trans (e₃.trans eT)))

/-- Corestriction as an additive homomorphism `BrauerGroup L →+ BrauerGroup K`. -/
noncomputable def corHom : BrauerGroup.{u, u} L →+ BrauerGroup.{u, u} K where
  toFun := cor K L
  map_zero' := cor_groundField K L
  map_add' a b := by
    induction a using Quotient.inductionOn with | _ A =>
    induction b using Quotient.inductionOn with | _ B =>
    exact classOf_eq_of_algEquiv (corCSATensorEquiv K L A B)

@[simp]
theorem corHom_apply (x : BrauerGroup.{u, u} L) : corHom K L x = cor K L x := rfl

@[simp]
theorem corHom_classOf (A : CSA.{u, u} L) :
    corHom K L (classOf A) = classOf (corCSA K L A) := rfl

/-- Split classes go to split classes. -/
theorem corHom_zero : corHom K L 0 = 0 := map_zero _

variable (F : Type u) [Field F]

/-- Corestriction along the identity extension is the identity homomorphism. -/
theorem corHom_self : corHom F F = AddMonoidHom.id (BrauerGroup.{u, u} F) :=
  AddMonoidHom.ext fun x => congrFun (cor_self F) x

end Langlands.BrauerCorestriction

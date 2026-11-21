import Langlands.Geometry.FormalGroup.DeligneNilpAction
import Langlands.Geometry.FormalGroup.DrinfeldActionExponent
import Langlands.Galois.Local.SeparableUnramifiedCompletionFrobenius

/-! # Deligne points with the actual completed unramified base map -/

noncomputable section

universe u

namespace Langlands.DeligneFormalSpace

open CategoryTheory ValuativeRel CentralSimple _root_.Langlands.FormalGroup
open Langlands.LocalGalois.Separable.UnramifiedCompletion
open scoped MatrixGroups

variable {K : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable {π : 𝒪[K]} {d : ℕ} [NeZero d]

/-- Points of the completed-base Deligne functor retain the original Deligne
class and the actual map from the completed base to the test algebra. -/
def nilpDeligneCompletedFunctor (hπ : Irreducible π) : Nilp.{u, u} 𝒪[K] π ⥤ Type (u + 1) where
  obj B := (nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)).obj B ×
    (Integers K →ₐ[𝒪[K]] B.obj)
  map f := ↾(fun x => ((nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)).map f x.1,
    f.hom.hom.comp x.2))
  map_id B := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom
        ((nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)).map_id B) x.1
    · rfl
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · exact ConcreteCategory.congr_hom
        ((nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)).map_comp f g) x.1
    · rfl

private def completedPrecompEquiv (σ : Integers K ≃ₐ[𝒪[K]] Integers K)
    (B : Nilp.{u, u} 𝒪[K] π) :
    (Integers K →ₐ[𝒪[K]] B.obj) ≃ (Integers K →ₐ[𝒪[K]] B.obj) where
  toFun f := f.comp σ.symm.toAlgHom
  invFun f := f.comp σ.toAlgHom
  left_inv f := AlgHom.ext fun x => congrArg f (σ.symm_apply_apply x)
  right_inv f := AlgHom.ext fun x => congrArg f (σ.apply_symm_apply x)

private def nilpDeligneCompletedAut (hπ : Irreducible π)
    (e : Aut (nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)))
    (σ : Integers K ≃ₐ[𝒪[K]] Integers K) : Aut (nilpDeligneCompletedFunctor (d := d) hπ) :=
  NatIso.ofComponents (fun B => ((e.app B).toEquiv.prodCongr (completedPrecompEquiv σ B)).toIso)
    (fun f => by
      apply ConcreteCategory.hom_ext
      intro x
      apply Prod.ext
      · exact ConcreteCategory.congr_hom (e.hom.naturality f) x.1
      · rfl)

/-- Act on the Deligne class and by inverse precomposition on the actual base map. -/
def nilpDeligneCompletedAutHom (hπ : Irreducible π) :
    Aut (nilpSheafClassFunctor d π K (coefficientUniformizer_ne_zero hπ)) ×
      (Integers K ≃ₐ[𝒪[K]] Integers K) →*
      Aut (nilpDeligneCompletedFunctor (d := d) hπ) where
  toFun x := nilpDeligneCompletedAut hπ x.1 x.2
  map_one' := by
    apply Aut.ext
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · change x.2.comp (AlgHom.id 𝒪[K] (Integers K)) = x.2
      exact AlgHom.comp_id _
  map_mul' e f := by
    apply Aut.ext
    apply NatTrans.ext
    funext B
    apply ConcreteCategory.hom_ext
    intro x
    apply Prod.ext
    · rfl
    · rfl

variable (K) in
private def completedFrobeniusPowers : Multiplicative ℤ →* (Integers K ≃ₐ[𝒪[K]] Integers K) where
  toFun n := arithmeticFrobenius K ^ n.toAdd
  map_one' := zpow_zero _
  map_mul' m n := zpow_add _ m.toAdd n.toAdd

variable {D : Type u} [DivisionRing D] [Algebra K D]
variable [FiniteDimensional K D] [Algebra.IsCentral K D]

local instance : NeZero (reducedDegree K D) := ⟨(reducedDegree_pos K D).ne'⟩

/-- Drinfeld's Deligne-side action uses the projective matrix action and the
signed Frobenius action on the actual completed base. -/
def nilpDeligneCompletedDivisionAction (hπ : Irreducible π) :
    GL (Fin (reducedDegree K D)) K × Dˣ →*
      Aut (nilpDeligneCompletedFunctor (d := reducedDegree K D) hπ) :=
  (nilpDeligneCompletedAutHom (d := reducedDegree K D) hπ).comp
    ((((nilpSheafProjectiveLeftHom hπ).comp Matrix.ProjGenLinGroup.mk).comp
      (MonoidHom.fst (GL (Fin (reducedDegree K D)) K) Dˣ)).prod
      ((completedFrobeniusPowers K).comp (LocalDivision.DrinfeldAction.exponentHom K D)))

variable (hπ : Irreducible π) (g : GL (Fin (reducedDegree K D)) K × Dˣ)
variable {B : Nilp.{u, u} 𝒪[K] π}
variable (x : (nilpDeligneCompletedFunctor (d := reducedDegree K D) hπ).obj B)

/-- The first component is the actual projective matrix action. -/
theorem nilpDeligneCompletedDivisionAction_deligne :
    ((nilpDeligneCompletedDivisionAction hπ g).hom.app B x).1 =
      (nilpSheafProjectiveLeftHom hπ (Matrix.ProjGenLinGroup.mk g.1)).hom.app B x.1 := rfl

/-- The completed base coordinate precomposes with the negative order power of arithmetic Frobenius. -/
theorem nilpDeligneCompletedDivisionAction_base :
    ((nilpDeligneCompletedDivisionAction hπ g).hom.app B x).2 =
      x.2.comp ((arithmeticFrobenius K ^ (-LocalDivision.DrinfeldAction.exponent K D g)).toAlgHom) := by
  change x.2.comp ((arithmeticFrobenius K ^ LocalDivision.DrinfeldAction.exponent K D g).symm.toAlgHom) = _
  rw [zpow_neg]
  rfl

end Langlands.DeligneFormalSpace

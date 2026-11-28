import Langlands.Representation.CuspidalSupport.BernsteinSupercuspidalHomBound
import Langlands.Representation.Induction.BinaryProduct
import Langlands.Representation.Smooth.RenardTensorHomAdjunctionProof
import Mathlib.RepresentationTheory.FiniteIndex

/-! # Transfer of tensor-type intertwiners through finite-index coinduction -/

noncomputable section

open CategoryTheory Representation
open Langlands.CuspidalSupport.HomBound (intertwiningMapLinearCongr)

namespace Langlands.BushnellKutzko.SplitTypeJacquet

universe uG uW uV uX uA uH

variable {G : Type uG} [Group G]
variable {W : Type uW} {V : Type uV} {X : Type uX} {A : Type uA}
  [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup A] [Module ℂ A]

/-- Coinduction transports an equivalence by postcomposing the equivariant functions. -/
private def coindEquiv {H : Type uH} [Group H] (i : H →* G)
    {κ : Representation ℂ H W} {σ : Representation ℂ H X} (e : κ.Equiv σ) :
    (coind i κ).Equiv (coind i σ) where
  toLinearEquiv :=
    { toFun := coindMap i e.toIntertwiningMap
      invFun := coindMap i e.symm.toIntertwiningMap
      left_inv := fun f => Subtype.ext <| funext fun g => e.symm_apply_apply (f.val g)
      right_inv := fun f => Subtype.ext <| funext fun g => e.apply_symm_apply (f.val g)
      map_add' := (coindMap i e.toIntertwiningMap).map_add
      map_smul' := (coindMap i e.toIntertwiningMap).map_smul }
  isIntertwining' := (coindMap i e.toIntertwiningMap).isIntertwining'

/-- Frobenius reciprocity for coinduction from a finite-index subgroup, with independent
universes for the group and the two representation carriers. -/
def finiteIndexCoindHomEquiv (H : Subgroup G) [H.FiniteIndex]
    (κ : Representation ℂ H W) (π : Representation ℂ G V) :
    (coind H.subtype κ).IntertwiningMap π ≃ₗ[ℂ] IntertwiningMap κ (π.comp H.subtype) := by
  classical
  let eκ := BinaryTensor.liftEquiv.{uG, uW, max uG uV} κ
  let eπ := BinaryTensor.liftEquiv.{uG, uV, max uG uW} π
  let B : Rep.{max uG uV uW} ℂ G := Rep.of (BinaryTensor.lift.{uG, uV, max uG uW} π)
  let C : Rep.{max uG uV uW} ℂ H := Rep.of (BinaryTensor.lift.{uG, uW, max uG uV} κ)
  let iso := Rep.indCoindIso C
  let precomp : (Rep.coind H.subtype C ⟶ B) ≃ₗ[ℂ] (Rep.ind H.subtype C ⟶ B) :=
    { toFun := fun f => iso.hom ≫ f
      invFun := fun f => iso.inv ≫ f
      left_inv := by intro f; simp
      right_inv := by intro f; simp
      map_add' := fun f g => Rep.comp_add iso.hom f g
      map_smul' := fun a f => by simp }
  let liftHom := intertwiningMapLinearCongr (coindEquiv H.subtype eκ) eπ
  let unliftHom := (intertwiningMapLinearCongr eκ (BinaryTensor.compEquiv eπ H.subtype)).symm
  let adj := (Rep.homLinearEquiv (Rep.coind H.subtype C) B).symm.trans
    (precomp.trans ((Rep.indResHomEquiv.{max uV uW, 0, uG, uG} H.subtype C B).trans
      (Rep.homLinearEquiv C (Rep.res H.subtype B))))
  exact liftHom.trans (adj.trans unliftHom)

/-- Equivalent coinductions transfer the tensor-type Hom space after twisting each source by
the restriction of the same ambient representation `ξ`. -/
def coinducedTensorHomEquiv (H K : Subgroup G) [H.FiniteIndex] [K.FiniteIndex]
    (κ : Representation ℂ H W) (σ : Representation ℂ K X)
    (e : (coind H.subtype κ).Equiv (coind K.subtype σ))
    (ξ : Representation ℂ G A) (π : Representation ℂ G V) :
    IntertwiningMap (tprod κ (ξ.comp H.subtype)) (π.comp H.subtype) ≃ₗ[ℂ]
      IntertwiningMap (tprod σ (ξ.comp K.subtype)) (π.comp K.subtype) := by
  let τ := Representation.linHom ξ π
  let cH := Langlands.Renard.Smooth.TensorHom.intertwinerCurry κ (ξ.comp H.subtype)
    (π.comp H.subtype)
  let cK := Langlands.Renard.Smooth.TensorHom.intertwinerCurry σ (ξ.comp K.subtype)
    (π.comp K.subtype)
  let fH := finiteIndexCoindHomEquiv H κ τ
  let fK := finiteIndexCoindHomEquiv K σ τ
  let trans := intertwiningMapLinearCongr e (Representation.Equiv.refl τ)
  exact cH.trans (fH.symm.trans (trans.trans (fK.trans cK.symm)))

end Langlands.BushnellKutzko.SplitTypeJacquet

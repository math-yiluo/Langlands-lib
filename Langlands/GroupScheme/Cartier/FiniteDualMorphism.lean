import Langlands.GroupScheme.Cartier.FiniteDualAlgebra

/-! # Morphisms of the convolution dual of a finite projective Hopf algebra -/

noncomputable section

open Module TensorProduct WithConv Coalgebra
open scoped TensorProduct

namespace Langlands.GroupScheme.Cartier.FiniteDual

variable {R A B : Type*} [CommRing R] [CommRing A] [Bialgebra R A] [CommRing B] [Bialgebra R B]

/-- The linear transpose of a map of coordinate algebras, with convolution on the duals. -/
def dualLinearMap (φ : A →ₐc[R] B) : Dual R B →ₗ[R] Dual R A :=
  (WithConv.linearEquiv R _).symm.toLinearMap.comp
    (φ.toLinearMap.dualMap.comp (WithConv.linearEquiv R _).toLinearMap)

@[simp]
theorem dualLinearMap_apply (φ : A →ₐc[R] B) (f : Dual R B) (a : A) :
    dualLinearMap φ f a = f (φ a) := rfl

variable [Module.Finite R A] [Module.Projective R A] [Module.Finite R B] [Module.Projective R B]

private theorem tensorDual_map_dualLinearMap (φ : A →ₐc[R] B)
    (t : Dual R B ⊗[R] Dual R B) (a b : A) :
    tensorDual (TensorProduct.map (dualLinearMap φ) (dualLinearMap φ) t) (a ⊗ₜ[R] b) =
      tensorDual t (φ a ⊗ₜ[R] φ b) := by
  induction t using TensorProduct.inductionOn with
  | tmul f g => simp
  | add t s ht hs => simp [ht, hs]

private def dualAlgHom (φ : A →ₐc[R] B) : Dual R B →ₐ[R] Dual R A :=
  AlgHom.ofLinearMap (dualLinearMap φ) (by
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    change (1 : Dual R B) (φ a) = (1 : Dual R A) a
    simp) (fun f g => by
    apply WithConv.ext
    apply LinearMap.ext
    intro a
    change (f * g) (φ a) = (dualLinearMap φ f * dualLinearMap φ g) a
    rw [LinearMap.convMul_apply, LinearMap.convMul_apply, ← CoalgHomClass.map_comp_comul_apply φ a]
    exact congrArg (LinearMap.mul' R R) (LinearMap.congr_fun (TensorProduct.map_comp
      f.ofConv g.ofConv φ.toLinearMap φ.toLinearMap).symm (comul a)))

/-- Actual morphism of the finite convolution-dual bialgebras, contravariant in
the input map. Its two structural identities are transposes of the input identities. -/
def dualBialgHom (φ : A →ₐc[R] B) : Dual R B →ₐc[R] Dual R A := by
  refine BialgHom.ofAlgHom (dualAlgHom φ) (AlgHom.ext fun f => ?_) (AlgHom.ext fun f => ?_)
  · change dualLinearMap φ f 1 = f 1
    rw [dualLinearMap_apply, map_one]
  · apply tensorDual_ext
    intro a b
    change tensorDual (TensorProduct.map (dualLinearMap φ) (dualLinearMap φ) (comul f)) (a ⊗ₜ[R] b) =
      tensorDual (comul (R := R) (dualLinearMap φ f)) (a ⊗ₜ[R] b)
    rw [tensorDual_map_dualLinearMap, tensorDual_comul, tensorDual_comul, dualLinearMap_apply, map_mul φ]

@[simp]
theorem dualBialgHom_apply (φ : A →ₐc[R] B) (f : Dual R B) (a : A) :
    dualBialgHom φ f a = f (φ a) := rfl

@[simp]
theorem dualBialgHom_id : dualBialgHom (BialgHom.id R A) = BialgHom.id R (Dual R A) := by
  apply BialgHom.ext
  intro f
  apply WithConv.ext
  apply LinearMap.ext
  intro a
  rfl

variable {C : Type*} [CommRing C] [Bialgebra R C]
  [Module.Finite R C] [Module.Projective R C]

@[simp]
theorem dualBialgHom_comp (φ : A →ₐc[R] B) (ψ : B →ₐc[R] C) :
    dualBialgHom (ψ.comp φ) = (dualBialgHom φ).comp (dualBialgHom ψ) := by
  apply BialgHom.ext
  intro f
  apply WithConv.ext
  apply LinearMap.ext
  intro a
  rfl

variable [Coalgebra.IsCocomm R A] [Coalgebra.IsCocomm R B]

/-- Evaluation into the double dual intertwines the actual bialgebra map. -/
theorem dualBialgHom_bidual (φ : A →ₐc[R] B) (a : A) :
    dualBialgHom (dualBialgHom φ) (bidualEquiv R A a) = bidualEquiv R B (φ a) := by
  apply WithConv.ext
  apply LinearMap.ext
  intro f
  rfl

end Langlands.GroupScheme.Cartier.FiniteDual

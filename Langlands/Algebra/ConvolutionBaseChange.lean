import Langlands.Algebra.GroupLikeDomainRigidity
import Mathlib.RingTheory.Bialgebra.Convolution

/-! # Convolution algebra points under scalar extension -/

noncomputable section

universe u v w z

open TensorProduct WithConv
open scoped TensorProduct

namespace Langlands.ConvolutionFamily

variable {k : Type u} [Field k] {R : Type v} [CommRing R] [Algebra k R]
    {C : Type w} [CommRing C] [Bialgebra k C]
    {A : Type z} [CommRing A] [Algebra k A] [Algebra R A] [IsScalarTower k R A]

/-- Restriction from the scalar-extended algebra preserves convolution when
group-like elements span the original coalgebra. -/
theorem restrict_conv_mul
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (f g : WithConv (R ⊗[k] C →ₐ[R] A)) :
    (AlgHom.liftEquiv k R C A).symm (f * g).ofConv =
      (toConv ((AlgHom.liftEquiv k R C A).symm f.ofConv) *
        toConv ((AlgHom.liftEquiv k R C A).symm g.ofConv)).ofConv := by
  apply AlgHom.toLinearMap_injective
  apply (GroupLike.basisOfSpan hspan).ext
  intro b
  simp only [GroupLike.basisOfSpan_apply]
  change (f * g) (1 ⊗ₜ[k] (b : C)) =
    (toConv ((AlgHom.liftEquiv k R C A).symm f.ofConv) *
      toConv ((AlgHom.liftEquiv k R C A).symm g.ofConv)) (b : C)
  rw [AlgHom.convMul_apply, AlgHom.convMul_apply,
    (GroupLike.isGroupLikeElem_one_tmul_domain
      b.isGroupLikeElem_val).comul_eq_tmul_self,
    b.isGroupLikeElem_val.comul_eq_tmul_self]
  simp

/-- Algebra points of scalar extension and of the original bialgebra have
canonically equivalent convolution monoids. -/
def baseChangeMulEquiv
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤) :
    WithConv (R ⊗[k] C →ₐ[R] A) ≃* WithConv (C →ₐ[k] A) where
  toFun f := toConv ((AlgHom.liftEquiv k R C A).symm f.ofConv)
  invFun f := toConv ((AlgHom.liftEquiv k R C A) f.ofConv)
  left_inv f := by
    apply WithConv.ofConv_injective
    exact (AlgHom.liftEquiv k R C A).apply_symm_apply f.ofConv
  right_inv f := by
    apply WithConv.ofConv_injective
    exact (AlgHom.liftEquiv k R C A).symm_apply_apply f.ofConv
  map_mul' f g := by
    apply WithConv.ofConv_injective
    exact restrict_conv_mul hspan f g

@[simp]
theorem baseChangeMulEquiv_apply
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (f : WithConv (R ⊗[k] C →ₐ[R] A)) (c : C) :
    baseChangeMulEquiv hspan f c = f (1 ⊗ₜ[k] c) := rfl

@[simp]
theorem baseChangeMulEquiv_symm_tmul
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    (f : WithConv (C →ₐ[k] A)) (r : R) (c : C) :
    (baseChangeMulEquiv (R := R) hspan).symm f (r ⊗ₜ[k] c) = r • f c := rfl

/-- Restriction of algebra points commutes with every coefficient-algebra map. -/
theorem baseChangeMulEquiv_naturality
    (hspan : Submodule.span k {c : C | IsGroupLikeElem k c} = ⊤)
    {B : Type z} [CommRing B] [Algebra k B] [Algebra R B] [IsScalarTower k R B]
    (φ : A →ₐ[R] B) (f : WithConv (R ⊗[k] C →ₐ[R] A)) :
    (baseChangeMulEquiv hspan (toConv (φ.comp f.ofConv))).ofConv =
      (φ.restrictScalars k).comp (baseChangeMulEquiv hspan f).ofConv := rfl

end Langlands.ConvolutionFamily

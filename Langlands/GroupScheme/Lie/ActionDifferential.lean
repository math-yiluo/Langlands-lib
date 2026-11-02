import Langlands.GroupScheme.Lie.Adjoint
import Langlands.GroupScheme.AutomorphicAction

/-! # Differentiating actual automorphic group-scheme actions -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {R : CommRingCat.{u}} {H U : GroupScheme (Spec R)}
    (a : AutomorphicAction H U)
variable {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B]

/-- Change of test algebra commutes with the given action morphism. -/
theorem affineAct_naturality (f : A →ₐ[R] B)
    (h : Lie.AffinePoints H A) (x : Lie.AffinePoints U A) :
    Lie.affineMap U f (a.act h x) =
      a.act (Lie.affineMap H f h) (Lie.affineMap U f x) :=
  a.naturality _ h x

/-- The action by a constant point preserves the actual dual-number identity kernel. -/
def kernelAction (h : Lie.AffinePoints H A) : lieKernel U A →* lieKernel U A where
  toFun x := ⟨a.act (Lie.constant H h) x.val, by
    change Lie.reduction U (a.act _ _) = 1
    rw [Lie.reduction, a.affineAct_naturality]
    change a.act (Lie.reduction H (Lie.constant H h)) (Lie.reduction U x.val) = 1
    rw [Lie.reduction_constant, x.property, a.act_one]⟩
  map_one' := Subtype.ext (a.act_one _)
  map_mul' x y := Subtype.ext (a.act_mul_right _ x.val y.val)

@[simp] theorem kernelAction_val (h : Lie.AffinePoints H A) (x : lieKernel U A) :
    (a.kernelAction h x).val = a.act (Lie.constant H h) x.val := rfl

/-- The differential is natural under every homomorphism of test algebras. -/
theorem kernelAction_naturality (f : A →ₐ[R] B)
    (h : Lie.AffinePoints H A) (x : lieKernel U A) :
    lieKernelMap U f (a.kernelAction h x) =
      a.kernelAction (Lie.affineMap H f h) (lieKernelMap U f x) := by
  apply Subtype.ext
  have hc : Lie.affineMap H (GeneralLinear.DualNumber.coefficientAlgMap f)
      (Lie.constant H h) = Lie.constant H (Lie.affineMap H f h) := by
    simp only [Lie.constant, ← Lie.affineMap_comp]
    have he : (GeneralLinear.DualNumber.coefficientAlgMap f).comp
        (TrivSqZeroExt.inlAlgHom R A A) =
        (TrivSqZeroExt.inlAlgHom R B B).comp f := by
      apply AlgHom.ext
      intro c
      apply TrivSqZeroExt.ext
      · rfl
      · exact map_zero f
    rw [he]
  simp only [lieKernelMap_val, kernelAction_val, a.affineAct_naturality]
  rw [hc]

/-- Naturality for epsilon scaling gives linearity, including nonunit scalars. -/
theorem kernelAction_scale (c : A) (h : Lie.AffinePoints H A) (x : lieKernel U A) :
    lieKernelScale U c (a.kernelAction h x) =
      a.kernelAction h (lieKernelScale U c x) := by
  apply Subtype.ext
  simp only [lieKernelScale_val, kernelAction_val, a.affineAct_naturality]
  congr 1
  simp only [Lie.constant, ← Lie.affineMap_comp]
  have e : (GeneralLinear.DualNumber.epsilonScaleAlg (R := R) c).comp
      (TrivSqZeroExt.inlAlgHom R A A) = TrivSqZeroExt.inlAlgHom R A A := by
    ext z <;> simp [GeneralLinear.DualNumber.epsilonScaleAlg]
  rw [e]

variable [IsAffineHom U.X.hom]

/-- The differential of an actual action is a linear automorphism of the actual Lie kernel. -/
def differential (h : Lie.AffinePoints H A) :
    Additive (lieKernel U A) ≃ₗ[A] Additive (lieKernel U A) where
  toFun x := Additive.ofMul (a.kernelAction h x.toMul)
  invFun x := Additive.ofMul (a.kernelAction h⁻¹ x.toMul)
  left_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.act (Lie.constant H h⁻¹) (a.act (Lie.constant H h) x.toMul.val) = _
    rw [map_inv, a.act_inv_act]
  right_inv x := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.act (Lie.constant H h) (a.act (Lie.constant H h⁻¹) x.toMul.val) = _
    rw [map_inv, a.act_act_inv]
  map_add' x y := congrArg Additive.ofMul ((a.kernelAction h).map_mul x.toMul y.toMul)
  map_smul' c x := congrArg Additive.ofMul (a.kernelAction_scale c h x.toMul).symm

@[simp] theorem differential_val (h : Lie.AffinePoints H A)
    (x : Additive (lieKernel U A)) :
    (a.differential h x).toMul.val = a.act (Lie.constant H h) x.toMul.val := rfl

/-- The resulting linear representation is constructed from the original action. -/
def differentialRepresentation (A : Type u) [CommRing A] [Algebra R A] :
    Lie.AffinePoints H A →*
      (Additive (lieKernel U A) ≃ₗ[A] Additive (lieKernel U A)) where
  toFun := a.differential
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.act (Lie.constant H 1) x.toMul.val = _
    rw [map_one, a.act_one_left]
    rfl
  map_mul' h h' := by
    apply LinearEquiv.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    change a.act (Lie.constant H (h * h')) x.toMul.val =
      a.act (Lie.constant H h) (a.act (Lie.constant H h') x.toMul.val)
    rw [map_mul, a.act_mul_left]

/-- Linear coefficient change intertwines the constructed differentials. -/
theorem differential_naturality (f : A →ₐ[R] B)
    (h : Lie.AffinePoints H A) (x : Additive (lieKernel U A)) :
    lieKernelMapLinear U f (a.differential h x) =
      a.differential (Lie.affineMap H f h) (lieKernelMapLinear U f x) :=
  congrArg Additive.ofMul (a.kernelAction_naturality f h x.toMul)

/-- Restricting the original action restricts its differential on the same Lie module. -/
theorem differential_restrict {M : GroupScheme (Spec R)} (j : M ⟶ H)
    (m : Lie.AffinePoints M A) :
    (a.restrict j).differential m = a.differential (m ≫ j.hom.hom) := by
  apply LinearEquiv.ext
  intro x
  apply Additive.toMul.injective
  apply Subtype.ext
  change (a.restrict j).act (Lie.constant M m) x.toMul.val = _
  rw [restrict_act]
  rfl

/-- For ambient conjugation this differential is precisely the published adjoint action. -/
theorem differential_conjugation (i : H ⟶ U) (h : Lie.AffinePoints H A)
    (x : Additive (lieKernel U A)) :
    (conjugation i).differential h x = adjoint U A (h ≫ i.hom.hom) x := by
  apply Additive.toMul.injective
  apply Subtype.ext
  rw [differential_val, conjugation_act, adjoint_val]
  rfl

end Langlands.GroupScheme.AutomorphicAction

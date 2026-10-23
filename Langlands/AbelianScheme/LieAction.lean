import Langlands.AbelianScheme.LieAdditivityProof
import Langlands.AbelianScheme.Rational
import Langlands.AlgebraicGeometry.ModuleLinear
import Langlands.CategoryTheory.RationalizationLift

/-! # Endomorphism actions on the relative Lie module of an abelian scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme

variable {S : AlgebraicGeometry.Scheme.{u}}

/-- The actual integral endomorphism ring acts on the relative Lie module. -/
def lieEndAction (A : AbelianScheme S) : End A →+* CategoryTheory.End A.Lie where
  toFun := (lieFunctor S).map
  map_zero' := (lieFunctor S).map_zero A A
  map_one' := (lieFunctor S).map_id A
  map_add' := fun _ _ => (lieFunctor S).map_add
  map_mul' := fun f g => (lieFunctor S).map_comp g f

@[simp]
lemma lieEndAction_apply (A : AbelianScheme S) (f : End A) :
    lieEndAction A f = lieMap f := rfl

/-- Over an actual rational algebra base, rational endomorphisms act on Lie. -/
def lieEnd0Action {R : CommRingCat.{u}} [Algebra ℚ R] (p : S ⟶ Spec R)
    (A : AbelianScheme S) :
    letI := Langlands.Scheme.Modules.rationalLinearOverBase p
    End0 A →ₐ[ℚ] CategoryTheory.End A.Lie := by
  letI := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.liftEnd (lieFunctor S) A

@[simp]
lemma lieEnd0Action_ofEnd {R : CommRingCat.{u}} [Algebra ℚ R] (p : S ⟶ Spec R)
    (A : AbelianScheme S) (f : End A) :
    lieEnd0Action p A (endToEnd0 A f) = lieEndAction A f := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  exact Langlands.Rationalization.liftEnd_ofEnd (lieFunctor S) A f

@[simp]
lemma lieEnd0Action_tmul {R : CommRingCat.{u}} [Algebra ℚ R] (p : S ⟶ Spec R)
    (A : AbelianScheme S) (q : ℚ) (f : End A) :
    letI := Langlands.Scheme.Modules.rationalLinearOverBase p
    lieEnd0Action p A (q ⊗ₜ[ℤ] f) = q • lieMap f := by
  let := Langlands.Scheme.Modules.rationalLinearOverBase p
  rfl

end Langlands.AbelianScheme

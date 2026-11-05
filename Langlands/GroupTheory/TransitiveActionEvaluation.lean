import Mathlib.GroupTheory.GroupAction.Transitive
import Mathlib.GroupTheory.GroupAction.Hom

/-! # Evaluation of equivariant maps from a transitive action -/

noncomputable section

set_option autoImplicit false

universe u v w

namespace Langlands.GroupTheory

variable {G : Type u} [Group G]
  {X : Type v} [MulAction G X]
  {Y : Type w} [MulAction G Y]

/-- Stabilizer-fixed values give the same answer for any two transporters. -/
theorem smul_eq_of_stabilizer_fixed (x : X) (y : Y)
    (hy : ∀ g : G, g • x = x → g • y = y)
    {g h : G} (he : g • x = h • x) : g • y = h • y := by
  have hs : (h⁻¹ * g) • x = x := by
    rw [mul_smul, he, inv_smul_smul]
  have hv := congrArg (fun z : Y => h • z) (hy (h⁻¹ * g) hs)
  simpa only [mul_smul, smul_inv_smul] using hv

variable [MulAction.IsPretransitive G X]

/-- Extend a stabilizer-fixed value to the whole transitive source action. -/
def equivariantMapOfStabilizerFixed (x : X)
    (y : {y : Y // ∀ g : G, g • x = x → g • y = y}) : X →[G] Y where
  toFun z := (Classical.choose (MulAction.IsPretransitive.exists_smul_eq x z) : G) • y.val
  map_smul' g z := by
    let a : G := Classical.choose (MulAction.IsPretransitive.exists_smul_eq x (g • z))
    let b : G := Classical.choose (MulAction.IsPretransitive.exists_smul_eq x z)
    have ha : a • x = g • z :=
      Classical.choose_spec (MulAction.IsPretransitive.exists_smul_eq x (g • z))
    have hb : b • x = z :=
      Classical.choose_spec (MulAction.IsPretransitive.exists_smul_eq x z)
    change a • y.val = g • b • y.val
    rw [← mul_smul]
    exact smul_eq_of_stabilizer_fixed x y.val y.property (by rw [ha, mul_smul, hb])

/-- The extension has the prescribed value after every actual transporter. -/
theorem equivariantMapOfStabilizerFixed_apply (x : X)
    (y : {y : Y // ∀ g : G, g • x = x → g • y = y})
    (g : G) (z : X) (he : g • x = z) :
    equivariantMapOfStabilizerFixed x y z = g • y.val := by
  apply smul_eq_of_stabilizer_fixed x y.val y.property
  exact (Classical.choose_spec (MulAction.IsPretransitive.exists_smul_eq x z)).trans he.symm

/-- Evaluation at a source point identifies equivariant maps with values fixed
by its full stabilizer. -/
def transitiveActionEvaluationEquiv (x : X) :
    (X →[G] Y) ≃ {y : Y // ∀ g : G, g • x = x → g • y = y} where
  toFun f := ⟨f x, fun g hg => by rw [← f.map_smul, hg]⟩
  invFun := equivariantMapOfStabilizerFixed x
  left_inv f := by
    apply MulActionHom.ext
    intro z
    obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq (M := G) x z
    rw [equivariantMapOfStabilizerFixed_apply x _ g z hg, ← f.map_smul, hg]
  right_inv y := by
    apply Subtype.ext
    change equivariantMapOfStabilizerFixed x y x = y.val
    simpa only [one_smul] using
      equivariantMapOfStabilizerFixed_apply x y (1 : G) x (one_smul G x)

/-- The evaluation equivalence uses literal evaluation. -/
theorem transitiveActionEvaluationEquiv_apply_val (x : X) (f : X →[G] Y) :
    (transitiveActionEvaluationEquiv x f).val = f x := rfl

/-- An equivariant map on a transitive source is determined by one value. -/
theorem equivariantMap_evaluation_injective (x : X) :
    Function.Injective (fun f : X →[G] Y => f x) := by
  intro f k h
  apply (transitiveActionEvaluationEquiv x).injective
  exact Subtype.ext h

end Langlands.GroupTheory

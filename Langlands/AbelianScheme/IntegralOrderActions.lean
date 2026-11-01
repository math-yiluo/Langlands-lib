import Langlands.AbelianScheme.LieOrderBaseChange
import Langlands.Algebra.FiniteFreeRingHom

/-! # Finite equations for actual integral actions on abelian schemes -/

noncomputable section

open CategoryTheory AlgebraicGeometry Module

universe u uI uO

namespace Langlands.AbelianScheme

variable {S S' : Scheme.{u}}
variable {I : Type uI} [Fintype I]
variable {O : Type uO} [Ring O]

/-- Finite tuples of actual endomorphisms satisfying the order's structure constants. -/
abbrev IntegralActionSolutions (b : Basis I ℤ O) (B : AbelianScheme S) :=
  FiniteFreeRingHom.Solutions b (CategoryTheory.End B)

/-- Actual integral actions are exactly the solutions of the finite equations. -/
def integralActionEquiv (b : Basis I ℤ O) (B : AbelianScheme S) :
    (O →+* CategoryTheory.End B) ≃ IntegralActionSolutions b B :=
  FiniteFreeRingHom.equiv b

@[simp] theorem integralActionEquiv_apply (b : Basis I ℤ O) (B : AbelianScheme S)
    (a : O →+* CategoryTheory.End B) (i : I) :
    (integralActionEquiv b B a).val i = a (b i) := rfl

@[simp] theorem integralActionEquiv_symm_apply (b : Basis I ℤ O) (B : AbelianScheme S)
    (r : IntegralActionSolutions b B) (x : O) :
    (integralActionEquiv b B).symm r x = ∑ i, b.repr x i • r.val i :=
  FiniteFreeRingHom.ofRelations_apply b r.val r.property x

@[simp] theorem integralActionEquiv_symm_apply_basis (b : Basis I ℤ O)
    (B : AbelianScheme S) (r : IntegralActionSolutions b B) (i : I) :
    (integralActionEquiv b B).symm r (b i) = r.val i :=
  FiniteFreeRingHom.equiv_symm_apply_basis b r i

/-- Pull back every actual endomorphism in the solution tuple. -/
def integralActionSolutionsBaseChange (b : Basis I ℤ O) (c : S' ⟶ S)
    (B : AbelianScheme S) (r : IntegralActionSolutions b B) :
    IntegralActionSolutions b ((baseChange c).obj B) :=
  FiniteFreeRingHom.map b (baseChangeEnd c B) r

@[simp] theorem integralActionSolutionsBaseChange_apply (b : Basis I ℤ O)
    (c : S' ⟶ S) (B : AbelianScheme S) (r : IntegralActionSolutions b B) (i : I) :
    (integralActionSolutionsBaseChange b c B r).val i = (baseChange c).map (r.val i) := rfl

theorem integralActionEquiv_baseChange (b : Basis I ℤ O) (c : S' ⟶ S)
    (B : AbelianScheme S) (a : O →+* CategoryTheory.End B) :
    integralActionEquiv b ((baseChange c).obj B) (baseChangeOrderAction c B a) =
      integralActionSolutionsBaseChange b c B (integralActionEquiv b B a) :=
  FiniteFreeRingHom.equiv_natural b a (baseChangeEnd c B)

/-- Reconstructing an integral action commutes with every actual scheme base change. -/
theorem integralActionEquiv_symm_baseChange (b : Basis I ℤ O) (c : S' ⟶ S)
    (B : AbelianScheme S) (r : IntegralActionSolutions b B) :
    (integralActionEquiv b ((baseChange c).obj B)).symm
        (integralActionSolutionsBaseChange b c B r) =
      baseChangeOrderAction c B ((integralActionEquiv b B).symm r) :=
  FiniteFreeRingHom.equiv_symm_natural b r (baseChangeEnd c B)

end Langlands.AbelianScheme

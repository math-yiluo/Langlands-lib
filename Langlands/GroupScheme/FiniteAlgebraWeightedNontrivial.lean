import Langlands.GroupScheme.FiniteAlgebraWeightedDynamic
import Langlands.GroupScheme.CorepresentedAffineComparison

/-! # Detecting a nontrivial weighted cocharacter -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme.FiniteAlgebraUnits.WeightedRoot

variable (k D : Type u) [Field k] [Infinite k] [Ring D] [Nontrivial D] [Algebra k D]
  {n : Type} [Fintype n] [DecidableEq n] {d : ℕ}
  (b : Module.Basis (Fin d) k (Matrix n n D))

/-- A weight equal to one detects a nonconstant actual cocharacter. -/
theorem cocharacter_ne_zero_of_weight_eq_one (w : n → ℤ) (a : n) (ha : w a = 1) :
    cocharacter k D b w ≠ 0 := by
  classical
  intro hz
  obtain ⟨c, hc⟩ := ({0, 1} : Finset k).exists_notMem
  have hc' : c ≠ 0 ∧ c ≠ 1 := by simpa using hc
  let S : CommAlgCat (CommRingCat.of k) := CommAlgCat.of (CommRingCat.of k) k
  let T := (algSpec (CommRingCat.of k)).obj (op S)
  let R := ((algΓ (CommRingCat.of k)).obj T).unop
  let e : R ≃ₐ[k] k := Corepresented.affineSectionsAlgEquiv S
  let E : R ⊗[k] D ≃ₐ[k] D :=
    (Algebra.TensorProduct.congr e (AlgEquiv.refl : D ≃ₐ[k] D)).trans
      (Algebra.TensorProduct.lid k D)
  let : Nontrivial (R ⊗[k] D) := E.symm.injective.nontrivial
  let t : Rˣ := Units.map (algebraMap k R).toMonoidHom (Units.mk0 c hc'.1)
  let x := (Gm.pointsEquiv (base k) T).symm t
  have hx : x ≫ (cocharacter k D b w).hom.hom = 1 := by
    rw [hz]
    exact MonObj.comp_one x
  have hm := tensorMatrixEquiv_cocharacter k D b w x
  rw [hx, map_one] at hm
  dsimp only [x] at hm
  erw [MulEquiv.apply_symm_apply] at hm
  have he := congrArg (fun M : Matrix.GeneralLinearGroup n (R ⊗[k] D) =>
    (M : Matrix n n (R ⊗[k] D)) a a) hm
  have he' : algebraMap k (R ⊗[k] D) c = 1 := by
    simpa [weightMatrixHom_apply, weightMatrix_val, Matrix.diagonal_apply_eq, ha, t,
      ← IsScalarTower.algebraMap_apply k R (R ⊗[k] D)] using he.symm
  exact hc'.2 ((algebraMap k (R ⊗[k] D)).injective (he'.trans (map_one _).symm))

/-- The actual weighted cocharacter together with its nonzeroness certificate,
when one of its weights is one. -/
def nontrivialCocharacterOfWeightOne (w : n → ℤ) (a : n) (ha : w a = 1) :
    {χ : (Gm (base k)).toGrp ⟶ groupScheme b // χ ≠ 0} :=
  ⟨cocharacter k D b w, cocharacter_ne_zero_of_weight_eq_one k D b w a ha⟩

end Langlands.GroupScheme.FiniteAlgebraUnits.WeightedRoot


import Langlands.Algebra.GaloisAlgebraDescent
import Langlands.GroupScheme.SpecialLinearInnerForm.GaloisDescent
import Langlands.GroupScheme.SpecialLinearInnerForm.NormOneChart
import Langlands.GroupScheme.CentralSimpleNormOneSplitting

/-! # The matrix descent algebra of an actual reduced-norm-one group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open scoped TensorProduct

namespace Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

open Langlands.CentralSimple Langlands.GaloisAlgebraDescent

variable {k L A : Type u} [Field k] [Field L] [Algebra k L]
    [Ring A] [Algebra k A]
    {I : Type} [Fintype I] [DecidableEq I]
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)

private theorem coefficientConjugate_one (x : L ⊗[k] A) :
    coefficientConjugate k L A 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem coefficientConjugate_mul (σ τ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    coefficientConjugate k L A (σ * τ) x =
      coefficientConjugate k L A σ (coefficientConjugate k L A τ x) := by
  induction x using TensorProduct.inductionOn with
  | tmul l a => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The matrix action transported from the actual coefficient action of `A_L`.
It is determined by the algebra chart, with no supplied descent-effectivity premise. -/
def matrixAction : SemilinearGaloisAction k L (Matrix I I L) where
  act σ := e.toRingEquiv.toRingHom.comp
    ((coefficientConjugate k L A σ).toRingHom.comp e.symm.toRingEquiv.toRingHom)
  act_algebraMap σ l := by
    change e (coefficientConjugate k L A σ
      (e.symm (algebraMap L (Matrix I I L) l))) =
        algebraMap L (Matrix I I L) (σ l)
    rw [e.symm.commutes, Algebra.algebraMap_eq_smul_one,
      coefficientConjugate_smul, map_one, map_smul, map_one]
    exact (Algebra.algebraMap_eq_smul_one (σ l)).symm
  act_one X := by
    change e (coefficientConjugate k L A 1 (e.symm X)) = X
    rw [coefficientConjugate_one, e.apply_symm_apply]
  act_mul σ τ X := by
    change e (coefficientConjugate k L A (σ * τ) (e.symm X)) =
      e (coefficientConjugate k L A σ
        (e.symm (e (coefficientConjugate k L A τ (e.symm X)))))
    rw [e.symm_apply_apply, coefficientConjugate_mul]

@[simp] theorem matrixAction_act (σ : L ≃ₐ[k] L) (X : Matrix I I L) :
    (matrixAction e).act σ X =
      e (coefficientConjugate k L A σ (e.symm X)) := rfl

/-- The prescribed chart is equivariant for the actual coefficient action. -/
@[simp] theorem matrixAction_chart (σ : L ≃ₐ[k] L) (x : L ⊗[k] A) :
    (matrixAction e).act σ (e x) = e (coefficientConjugate k L A σ x) := by
  rw [matrixAction_act, e.symm_apply_apply]

/-- The original algebra is mapped into the actual fixed matrix subalgebra. -/
def fixedHom : A →ₐ[k] (matrixAction e).fixed :=
  ((e.restrictScalars k).toAlgHom.comp
    (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A)).codRestrict
      (matrixAction e).fixed (by
        intro a σ
        change (matrixAction e).act σ (e (1 ⊗ₜ[k] a)) = e (1 ⊗ₜ[k] a)
        rw [matrixAction_chart, coefficientConjugate_tmul, map_one])

@[simp] theorem fixedHom_val (a : A) :
    (fixedHom e a : Matrix I I L) = e (1 ⊗ₜ[k] a) := rfl

theorem fixedHom_injective : Function.Injective (fixedHom e) := by
  intro a b h
  apply Algebra.TensorProduct.includeRight_injective (algebraMap k L).injective
  apply e.injective
  exact congrArg Subtype.val h

variable [FiniteDimensional k L] [IsGalois k L]

theorem fixedHom_surjective : Function.Surjective (fixedHom e) := by
  intro X
  have hx : ∀ σ : L ≃ₐ[k] L,
      coefficientConjugate k L A σ (e.symm (X : Matrix I I L)) =
        e.symm (X : Matrix I I L) := by
    intro σ
    apply e.injective
    rw [e.apply_symm_apply]
    exact X.property σ
  obtain ⟨a, ha⟩ := (mem_range_includeRight_iff k L A
    (e.symm (X : Matrix I I L))).mpr hx
  refine ⟨a, Subtype.ext ?_⟩
  change e ((Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) a) = _
  change (Algebra.TensorProduct.includeRight : A →ₐ[k] L ⊗[k] A) a =
    e.symm (X : Matrix I I L) at ha
  rw [ha, e.apply_symm_apply]

/-- Descent of the actual chart-induced matrix action recovers `A`, rather than
an arbitrary algebra having the desired Brauer class. -/
def fixedEquiv : A ≃ₐ[k] (matrixAction e).fixed :=
  AlgEquiv.ofBijective (fixedHom e) ⟨fixedHom_injective e, fixedHom_surjective e⟩

@[simp] theorem fixedEquiv_val (a : A) :
    (fixedEquiv e a : Matrix I I L) = e (1 ⊗ₜ[k] a) := rfl

/-- The effective-descent chart and the original chart agree after this equivalence. -/
theorem descentEquiv_fixedEquiv_tmul (l : L) (a : A) :
    (matrixAction e).descentEquiv (l ⊗ₜ[k] fixedEquiv e a) = e (l ⊗ₜ[k] a) := by
  rw [SemilinearGaloisAction.descentEquiv_tmul, fixedEquiv_val,
    Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul, ← map_smul,
    TensorProduct.smul_tmul', smul_eq_mul, mul_one]

variable {J : Type} [Fintype J] [DecidableEq J]
    (f : L ⊗[k] A ≃ₐ[L] Matrix J J L)

/-- Changing the actual algebra chart preserves the descended algebra, through `A`. -/
def changeChart : (matrixAction e).fixed ≃ₐ[k] (matrixAction f).fixed :=
  (fixedEquiv e).symm.trans (fixedEquiv f)

/-- Chart independence is implemented by the original algebra-chart transition. -/
theorem changeChart_val (X : (matrixAction e).fixed) :
    (changeChart e f X : Matrix J J L) = f (e.symm (X : Matrix I I L)) := by
  obtain ⟨a, rfl⟩ := (fixedEquiv e).surjective X
  simp [changeChart]

@[simp] theorem changeChart_fixedEquiv (a : A) :
    changeChart e f (fixedEquiv e a) = fixedEquiv f a := by
  simp [changeChart]

section Unconditional

variable (k A) [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]

/-- The actual CSA itself supplies a finite Galois chart for its matrix descent. -/
abbrev canonicalMatrixAction :=
  matrixAction (finiteGaloisSplittingChart k A)

/-- No splitting-field existence or descent-effectivity assumption is needed. -/
def canonicalFixedEquiv : A ≃ₐ[k] (canonicalMatrixAction k A).fixed :=
  fixedEquiv (finiteGaloisSplittingChart k A)

end Unconditional

end Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

import Langlands.GroupScheme.SimplyConnected.NormOneOppositeChart
import Langlands.GroupScheme.GeneralLinearContragredient
import Langlands.Algebra.BrauerGroup

/-! # Actual fixed-algebra Brauer representatives for the norm-one conventions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
    {I : Type} [Fintype I] [DecidableEq I]

section Dual

variable {A : Type u} [Ring A] [Algebra k A]
    (e : L ⊗[k] A ≃ₐ[L] Matrix I I L)

/-- The dual conjugator is the contragredient of the original conjugator. -/
theorem dualConjugator_eq_contragredient (σ : L ≃ₐ[k] L) :
    dualConjugator e σ = GeneralLinear.matrixContragredient I L (galoisConjugator e σ) :=
  Units.ext rfl

open SpecialLinearInnerForm in
/-- On every test, the inverse transpose intertwines the dual chart matrices. -/
theorem dualConjugator_normOneChartPoints [FiniteDimensional k A] [Algebra.IsCentral k A]
    [IsSimpleRing A] (σ : L ≃ₐ[k] L)
    {V : Over (Spec (CommRingCat.of k))} (s : V ⟶ ringTest k L)
    (g : V ⟶ (normOne k A).X) :
    Matrix.GeneralLinearGroup.map (pointScalars s) (dualConjugator e σ) *
        GeneralLinear.matrixContragredient I ((algΓ (CommRingCat.of k)).obj V).unop
          (Matrix.SpecialLinearGroup.toGL (normOneChartPoints e s g)) =
      GeneralLinear.matrixContragredient I ((algΓ (CommRingCat.of k)).obj V).unop
          (Matrix.SpecialLinearGroup.toGL (normOneChartPoints e
            (s ≫ ringTestMap k σ.toAlgHom) g)) *
        Matrix.GeneralLinearGroup.map (pointScalars s) (dualConjugator e σ) := by
  have h : Matrix.GeneralLinearGroup.map (pointScalars s) (galoisConjugator e σ) *
        Matrix.SpecialLinearGroup.toGL (normOneChartPoints e s g) =
      Matrix.SpecialLinearGroup.toGL (normOneChartPoints e (s ≫ ringTestMap k σ.toAlgHom) g) *
        Matrix.GeneralLinearGroup.map (pointScalars s) (galoisConjugator e σ) :=
    Units.ext (galoisConjugator_normOneChartPoints e σ s g)
  have hdual := congrArg (GeneralLinear.matrixContragredient I ((algΓ (CommRingCat.of k)).obj V).unop) h
  simpa only [map_mul, GeneralLinear.matrixContragredient_map,
    dualConjugator_eq_contragredient] using hdual

variable [IsGalois k L]

/-- Transpose preserves membership when passing to the opposite chart's fixed algebra. -/
theorem transpose_mem_oppositeFixed_iff (X : Matrix I I L) :
    Xᵀ ∈ (matrixAction (oppositeChart e)).fixed ↔ X ∈ (matrixAction e).fixed := by
  constructor
  · intro hx
    obtain ⟨Y, hY⟩ := (oppositeFixedEquiv e).surjective ⟨Xᵀ, hx⟩
    have ht : (Y.unop : Matrix I I L)ᵀ = Xᵀ :=
      (oppositeFixedEquiv_val e Y).symm.trans (congrArg Subtype.val hY)
    have he : (Y.unop : Matrix I I L) = X := Matrix.transpose_injective ht
    exact he ▸ Y.unop.property
  · intro hx
    have h := (oppositeFixedEquiv e (MulOpposite.op ⟨X, hx⟩)).property
    simpa only [oppositeFixedEquiv_val, MulOpposite.unop_op] using h

/-- The dual intertwining equations cut out the actual fixed algebra of the opposite chart. -/
theorem mem_oppositeFixed_iff_dualConjugator (X : Matrix I I L) :
    X ∈ (matrixAction (oppositeChart e)).fixed ↔
      ∀ σ : L ≃ₐ[k] L,
        (dualConjugator e σ : Matrix I I L) * X =
          X.map σ * (dualConjugator e σ : Matrix I I L) := by
  calc
    _ ↔ Xᵀ ∈ (matrixAction e).fixed := by
      simpa only [Matrix.transpose_transpose] using transpose_mem_oppositeFixed_iff e Xᵀ
    _ ↔ _ := (mem_fixed_iff_galoisConjugator e Xᵀ).trans (forall_congr' fun σ => by
      let D := dualConjugator e σ
      change _ ↔ (D : Matrix I I L) * X = X.map σ * (D : Matrix I I L)
      calc
        _ ↔ X * (↑D⁻¹ : Matrix I I L) = (↑D⁻¹ : Matrix I I L) * X.map σ := by
          rw [← Matrix.transpose_injective.eq_iff]
          simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_map]
          rfl
        _ ↔ X = (↑D⁻¹ : Matrix I I L) * X.map σ * (D : Matrix I I L) :=
          Units.mul_inv_eq_iff_eq_mul D
        _ ↔ _ := by
          rw [mul_assoc, eq_comm (a := X)]
          exact (Units.inv_mul_eq_iff_eq_mul D).trans eq_comm)

end Dual

section BrauerClasses

variable [IsGalois k L] (B : CSA.{u, u} k)
    (e : L ⊗[k] B ≃ₐ[L] Matrix I I L)

/-- The actual fixed matrix algebra of the chart, packaged as a central simple algebra. -/
def fixedCSA : CSA.{u, u} k where
  toAlgCat := AlgCat.of k (matrixAction e).fixed
  isCentral := Algebra.IsCentral.of_algEquiv k B _ (fixedEquivOfIsGalois e)
  isSimple := IsSimpleRing.of_ringEquiv (fixedEquivOfIsGalois e).toRingEquiv inferInstance
  fin_dim := FiniteDimensional.of_surjective (fixedEquivOfIsGalois e).toLinearMap
    (fixedEquivOfIsGalois e).surjective

/-- The column convention gives the class of the original algebra. -/
@[simp] theorem classOf_fixedCSA :
    Langlands.Brauer.classOf (fixedCSA B e) = Langlands.Brauer.classOf B :=
  Langlands.Brauer.classOf_eq_of_algEquiv (fixedEquivOfIsGalois e).symm

/-- The dual convention gives the additive inverse through the actual opposite algebra. -/
theorem classOf_oppositeFixedCSA :
    Langlands.Brauer.classOf (fixedCSA (Langlands.Brauer.opposite B) (oppositeChart e)) =
      -Langlands.Brauer.classOf B := by
  exact (classOf_fixedCSA (Langlands.Brauer.opposite B) (oppositeChart e)).trans
    (Langlands.Brauer.classOf_opposite B)

end BrauerClasses

end Langlands.GroupScheme.CentralSimpleUnits.TitsDescent

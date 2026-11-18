import Langlands.GroupScheme.SimplyConnected.NormOneMatrixRepresentation
import Langlands.GroupScheme.SimplyConnected.NormOneTitsFixedClass
import Langlands.GroupScheme.MatrixRepresentationDual
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Galois intertwiners of the actual norm-one matrix representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped TensorProduct Matrix

namespace Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

open Langlands.CentralSimple Langlands.ReducedNorm SpecialLinearInnerForm TitsDescent

attribute [local instance] Splitting.sectionsAlgebra Splitting.sectionsScalarTower

variable {k A : Type u} [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    {L : Type u} [Field L] [Algebra k L]
    (e : L ⊗[k] A ≃ₐ[L]
      Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) L)

local notation "ι" => Fin (reducedDegree k A)
local notation "b" => algebraBaseMap k L
local notation "G" => normOne k A
local notation "Gₗ" => Functor.obj (GroupScheme.baseChange b) G

/-- A test scheme over the splitting field remembers its map to that field over `k`. -/
def chartBasePoint (T : Over (Spec (CommRingCat.of L))) :
    (Over.map b).obj T ⟶ ringTest k L :=
  Over.homMk T.hom rfl

/-- The two chart descriptions give the same matrix on every relative test scheme. -/
private theorem representation_pointMatrix_eq_normOneChartPoints
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (Gₗ).X) :
    ((representation k A e).pointMatrix T x : Matrix ι ι Γ(T.left, ⊤)) =
      (normOneChartPoints e (chartBasePoint T) (baseChangePointsEquiv b G T x)).val := by
  rw [representation_pointMatrix_val, normOneChartPoints_val]
  change splittingMap e (Splitting.coefficients (K := k) T) _ =
    chartAlong e (pointScalars (chartBasePoint T)) (pointScalars_comp_algebraMap _) _
  rfl

/-- Changing the field structure on the test composes its chart point with `Spec σ`. -/
private theorem chartBasePoint_galois (σ : L ≃ₐ[k] L)
    (T : Over (Spec (CommRingCat.of L))) :
    chartBasePoint ((Over.map (galoisBaseMap k L σ)).obj T) =
      (descentTestIso b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) T).inv ≫
        (chartBasePoint T ≫ ringTestMap k σ.toAlgHom) := by
  apply Over.OverMorphism.ext
  change T.hom ≫ galoisBaseMap k L σ = 𝟙 _ ≫ (T.hom ≫ galoisBaseMap k L σ)
  exact (Category.id_comp _).symm

/-- The matrix of the transported point is the one read with the Galois-modified scalar map. -/
private theorem descentPoint_representation_pointMatrix (σ : L ≃ₐ[k] L)
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (Gₗ).X) :
    ((representation k A e).pointMatrix ((Over.map (galoisBaseMap k L σ)).obj T)
      (descentPoint b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G T x)).val =
      (normOneChartPoints e (chartBasePoint T ≫ ringTestMap k σ.toAlgHom)
        (baseChangePointsEquiv b G T x)).val := by
  rw [representation_pointMatrix_eq_normOneChartPoints, chartBasePoint_galois,
    baseChangePointsEquiv_descentPoint, normOneChartPoints_naturality]
  ext i j
  simp [descentTestIso]

/-- The original chart conjugator intertwines actual representation matrices under Galois transport. -/
theorem galoisConjugator_representation_pointMatrix (σ : L ≃ₐ[k] L)
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (Gₗ).X) :
    let transported : Matrix ι ι Γ(T.left, ⊤) :=
      ((representation k A e).pointMatrix ((Over.map (galoisBaseMap k L σ)).obj T)
        (descentPoint b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G T x)).val
    (galoisConjugator e σ : Matrix ι ι L).map (scalarMap T) *
        ((representation k A e).pointMatrix T x : Matrix ι ι Γ(T.left, ⊤)) =
      transported * (galoisConjugator e σ : Matrix ι ι L).map (scalarMap T) := by
  dsimp only
  rw [descentPoint_representation_pointMatrix, representation_pointMatrix_eq_normOneChartPoints]
  exact galoisConjugator_normOneChartPoints e σ (chartBasePoint T) (baseChangePointsEquiv b G T x)

/-- The same transport for the actual dual uses the inverse-transpose conjugator. -/
theorem dualConjugator_representation_pointMatrix (σ : L ≃ₐ[k] L)
    (T : Over (Spec (CommRingCat.of L))) (x : T ⟶ (Gₗ).X) :
    let transported : Matrix ι ι Γ(T.left, ⊤) :=
      (MatrixRepresentation.pointMatrix (MatrixRepresentation.dual (representation k A e))
        ((Over.map (galoisBaseMap k L σ)).obj T)
        (descentPoint b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G T x)).val
    (dualConjugator e σ : Matrix ι ι L).map (scalarMap T) *
        (MatrixRepresentation.pointMatrix (MatrixRepresentation.dual (representation k A e))
          T x : Matrix ι ι Γ(T.left, ⊤)) =
      transported * (dualConjugator e σ : Matrix ι ι L).map (scalarMap T) := by
  dsimp only
  let conjugator := Matrix.GeneralLinearGroup.map (scalarMap T) (galoisConjugator e σ)
  let transported : GL ι Γ(T.left, ⊤) :=
    (representation k A e).pointMatrix ((Over.map (galoisBaseMap k L σ)).obj T)
      (descentPoint b (galoisBaseMap k L σ) (galoisBaseMap_over k L σ) G T x)
  have h : conjugator * (representation k A e).pointMatrix T x = transported * conjugator :=
    Units.ext (galoisConjugator_representation_pointMatrix e σ T x)
  have hdual := congrArg (GeneralLinear.matrixContragredient ι Γ(T.left, ⊤)) h
  simp only [map_mul, conjugator, transported, GeneralLinear.matrixContragredient_map,
    ← dualConjugator_eq_contragredient] at hdual
  simp only [MatrixRepresentation.dual_pointMatrix]
  exact congrArg (fun M : GL ι Γ(T.left, ⊤) => (M : Matrix ι ι Γ(T.left, ⊤))) hdual

end Langlands.GroupScheme.CentralSimpleUnits.SplitRepresentation

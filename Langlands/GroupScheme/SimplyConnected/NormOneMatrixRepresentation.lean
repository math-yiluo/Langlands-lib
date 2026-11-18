import Langlands.GroupScheme.CentralSimpleNormOneSplitting
import Langlands.GroupScheme.MatrixRepresentation.IrreducibleRestriction

/-! # The actual irreducible matrix representation of a split norm-one group -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

open MatrixRepresentation

namespace SpecialLinear

variable {k : Type u} [Field k] {I : Type} [Fintype I] [DecidableEq I]

/-- The standard column representation has the prescribed matrix on every affine test. -/
theorem inclusion_affineMatrix (S : CommAlgCat.{u} (CommRingCat.of k))
    (x : (algSpec (CommRingCat.of k)).obj (op S) ⟶
      (groupScheme I (CommRingCat.of k)).X) :
    MatrixRepresentation.affineMatrix (inclusion I (CommRingCat.of k)) S x =
      Matrix.SpecialLinearGroup.toGL (affinePointsEquiv I (CommRingCat.of k) S x) := by
  exact Corepresented.groupSchemeMap_affinePoints
    (corepresentableBy I (CommRingCat.of k))
    (GeneralLinear.corepresentableBy I (CommRingCat.of k))
    (toGeneralLinear (n := I) (R := CommRingCat.of k)) x

/-- The actual standard column representation of `SL_I` is irreducible over every field. -/
theorem inclusion_isIrreducible [Nonempty I] :
    MatrixRepresentation.IsIrreducible (inclusion I (CommRingCat.of k)) := by
  refine ⟨inferInstance, ?_⟩
  intro V hV
  by_cases h0 : V = ⊥
  · exact Or.inl h0
  · refine Or.inr (eq_top_of_forall_SL_mulVec_mem V ?_ h0)
    intro g v hv
    let S := CommAlgCat.of (CommRingCat.of k) k
    let x := (affinePointsEquiv I (CommRingCat.of k) S).symm g
    have h := hV S x v hv (LinearMap.id : k →ₗ[k] k)
    change ((MatrixRepresentation.affineMatrix (inclusion I (CommRingCat.of k))
      S x : Matrix I I k) *ᵥ v) ∈ V at h
    rw [inclusion_affineMatrix] at h
    dsimp only [x] at h
    rw [MulEquiv.apply_symm_apply] at h
    exact h

end SpecialLinear

namespace CentralSimpleUnits.SplitRepresentation

open Langlands.CentralSimple Langlands.ReducedNorm

attribute [local instance] Splitting.sectionsAlgebra Splitting.sectionsScalarTower

variable (k A : Type u) [Field k] [Ring A] [Algebra k A]
    [FiniteDimensional k A] [Algebra.IsCentral k A] [IsSimpleRing A]
    {L : Type u} [Field L] [Algebra k L]
    (e : L ⊗[k] A ≃ₐ[L]
      Matrix (Fin (reducedDegree k A)) (Fin (reducedDegree k A)) L)

/-- The actual matrix representation given by the splitting chart and the standard SL inclusion. -/
def representation :
    MatrixRepresentation
      ((GroupScheme.baseChange (Splitting.baseMap (K := k) (L := L))).obj (normOne k A))
      (Fin (reducedDegree k A)) :=
  MatrixRepresentation.restrict
    (SpecialLinear.inclusion (Fin (reducedDegree k A)) (CommRingCat.of L))
    (Splitting.splittingIso k A e).hom

/-- On every relative test scheme this representation is exactly the chart matrix. -/
theorem representation_pointMatrix (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange (Splitting.baseMap (K := k) (L := L))).obj
      (normOne k A)).X) :
    (representation k A e).pointMatrix T x =
      Matrix.SpecialLinearGroup.toGL (Splitting.basePointsEquiv k A e T x) := by
  rw [representation, MatrixRepresentation.pointMatrix_restrict,
    MatrixRepresentation.pointMatrix_apply, SpecialLinear.pointsEquiv_inclusion,
    Splitting.splittingIso_hom_points]

/-- Its column-vector action is multiplication by the extended original algebra chart. -/
theorem representation_pointMatrix_val (T : Over (Spec (CommRingCat.of L)))
    (x : T ⟶ ((GroupScheme.baseChange (Splitting.baseMap (K := k) (L := L))).obj
      (normOne k A)).X) :
    ((representation k A e).pointMatrix T x : Matrix _ _ Γ(T.left, ⊤)) =
      splittingMap e (Splitting.coefficients (K := k) T)
        ((normOnePointsEquiv k A
          ((Over.map (Splitting.baseMap (K := k) (L := L))).obj T)
          (baseChangePointsEquiv (Splitting.baseMap (K := k) (L := L)) (normOne k A) T x)).val :
            Splitting.coefficients (K := k) T ⊗[k] A) := by
  rw [representation_pointMatrix]
  exact Splitting.basePointsEquiv_val k A e T x

/-- This representation is irreducible on all affine tests, not merely on rational points. -/
theorem representation_isIrreducible : (representation k A e).IsIrreducible :=
  SpecialLinear.inclusion_isIrreducible.restrict_iso (Splitting.splittingIso k A e)

/-- Every CSA supplies the chart for this actual irreducible representation. -/
abbrev canonicalRepresentation :=
  representation k A (finiteGaloisSplittingChart k A)

theorem canonicalRepresentation_isIrreducible :
    (canonicalRepresentation k A).IsIrreducible :=
  representation_isIrreducible k A (finiteGaloisSplittingChart k A)

end CentralSimpleUnits.SplitRepresentation

end Langlands.GroupScheme

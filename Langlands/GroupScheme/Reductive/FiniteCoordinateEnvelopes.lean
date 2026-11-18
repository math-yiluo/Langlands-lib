import Langlands.GroupScheme.Absolute.DenseRationalPointEnvelope
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.MatrixRepresentation.ComponentConstant
import Langlands.GroupScheme.ProductProperties
import Langlands.GroupScheme.Reductive.AbstractGroupTensorSemisimpleReduction

/-! # Simultaneous algebraic envelopes for finite coordinate actions -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AbstractGroupTensorReduction

/-- Rational points of the product of two general linear groups are pairs
of invertible matrices in the two coordinate dimensions. -/
def coordinateProductRationalEquiv (k : Type u) [Field k] (n m : ℕ) :
    RationalPoint k
      (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k) ⊗
        GeneralLinear.groupScheme (Fin m) (CommRingCat.of k)).X ≃*
      Matrix.GeneralLinearGroup (Fin n) k × Matrix.GeneralLinearGroup (Fin m) k :=
  (productPointsEquiv _ _ (Over.mk (𝟙 (Spec (CommRingCat.of k))))).trans
    (MatrixRepresentation.generalLinearRationalEquiv.prodCongr
      MatrixRepresentation.generalLinearRationalEquiv)

set_option maxHeartbeats 600000 in
/-- Two finite coordinate actions of an abstract group have a simultaneous
reduced affine envelope locally of finite type over the ground field. -/
theorem hasFiniteCoordinateEnvelopes (k : Type u) [Field k] (G : Type v) [Group G] :
    HasFiniteCoordinateEnvelopes k G := by
  intro n m r s
  let R := CommRingCat.of k
  let A := GeneralLinear.groupScheme (Fin n) R
  let B := GeneralLinear.groupScheme (Fin m) R
  let K : GroupScheme (Spec R) := A ⊗ B
  let : IsAffineHom K.X.hom := by
    let : IsAffine A.X.left := GeneralLinear.isAffine_groupScheme (Fin n) R
    let : IsAffineHom B.X.hom := GeneralLinear.isAffineHom_groupScheme (Fin m) R
    have : IsAffine K.X.left := by
      change IsAffine (Limits.pullback A.X.hom B.X.hom)
      infer_instance
    exact isAffineHom_of_isAffine K.X.hom
  let : Smooth A.X.hom := GeneralLinear.smoothStatement (Fin n) R
  let : Smooth B.X.hom := GeneralLinear.smoothStatement (Fin m) R
  let : LocallyOfFiniteType K.X.hom :=
    prop_tensor_hom (@LocallyOfFiniteType) A.X B.X inferInstance inferInstance
  let e : RationalPoint k K.X ≃*
      Matrix.GeneralLinearGroup (Fin n) k × Matrix.GeneralLinearGroup (Fin m) k :=
    coordinateProductRationalEquiv k n m
  let pair : G →* RationalPoint k K.X := e.symm.toMonoidHom.comp (r.prod s)
  obtain ⟨H, hred, haff, hfin, i, β, hβ, hfactor⟩ :=
    RationalPointClosure.exists_dense_envelope K pair.range
  let α := β.comp pair.rangeRestrict
  have hα : HasDenseRationalPointFamily α := by
    apply hβ.mono
    intro x hx
    obtain ⟨δ, z, hz⟩ := Set.mem_iUnion.mp hx
    obtain ⟨g, rfl⟩ := pair.rangeRestrict_surjective δ
    exact Set.mem_iUnion.mpr ⟨g, z, hz⟩
  have hmat (g : G) : e (α g ≫ i.hom.hom) = (r g, s g) := by
    rw [show α g ≫ i.hom.hom = pair g from hfactor (pair.rangeRestrict g)]
    exact e.apply_symm_apply _
  let p : MatrixRepresentation K (Fin n) := fst A B
  let q : MatrixRepresentation K (Fin m) := snd A B
  refine ⟨H, hred, haff, hfin, p.restrict i, q.restrict i, α, hα, ?_, ?_⟩
  · intro g
    rw [MatrixRepresentation.rationalMatrix_restrict,
      MatrixRepresentation.rationalMatrix_eq_generalLinearRationalEquiv]
    exact congrArg Prod.fst (hmat g)
  · intro g
    rw [MatrixRepresentation.rationalMatrix_restrict,
      MatrixRepresentation.rationalMatrix_eq_generalLinearRationalEquiv]
    exact congrArg Prod.snd (hmat g)

end Langlands.GroupScheme.AbstractGroupTensorReduction

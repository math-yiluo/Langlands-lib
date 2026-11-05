import Langlands.GroupScheme.Torus.GaloisNorm
import Langlands.GroupScheme.AffineWeilRestrictionTopology

/-! # Rational-point compatibility of the algebraic Galois norm -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj BigOperators

namespace Langlands.GroupScheme.GaloisNorm

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
  [FiniteDimensional k L] [IsGalois k L]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The tensor-unit coefficient map, with scalars restricted to `k`. -/
def tensorUnitMap : L ⊗[k] k →ₐ[k] L :=
  (Algebra.TensorProduct.rid k L L).toAlgHom.restrictScalars k

omit [FiniteDimensional k L] [IsGalois k L] [IsAffine T.X.left] in
/-- Tensor extension followed by tensor-unit is the existing coefficient extension. -/
theorem tensorUnitMap_extend (x : Lie.AffinePoints T.toGrp k) :
    Lie.affineMap T.toGrp (tensorUnitMap k L)
        (TensorGaloisPoint.extend k L k T.toGrp x) =
      GaloisPoint.extend k L T.toGrp x := by
  change Lie.affineMap T.toGrp (tensorUnitMap k L)
      (Lie.affineMap T.toGrp Algebra.TensorProduct.includeRight x) = _
  rw [← Lie.affineMap_comp]
  have h : (tensorUnitMap k L).comp
      (Algebra.TensorProduct.includeRight : k →ₐ[k] L ⊗[k] k) = Algebra.ofId k L := by
    ext
  rw [h]
  rfl

omit [FiniteDimensional k L] [IsGalois k L] [IsAffine T.X.left] in
/-- Tensor-unit intertwines tensor conjugation with the original field conjugation. -/
theorem tensorUnitMap_conjugate (σ : L ≃ₐ[k] L)
    (x : Lie.AffinePoints T.toGrp (L ⊗[k] k)) :
    Lie.affineMap T.toGrp (tensorUnitMap k L)
        (TensorGaloisPoint.conjugate k L k T.toGrp σ x) =
      GaloisPoint.conjugate k L T.toGrp σ
        (Lie.affineMap T.toGrp (tensorUnitMap k L) x) := by
  change Lie.affineMap T.toGrp (tensorUnitMap k L)
      (Lie.affineMap T.toGrp (TensorGaloisPoint.coefficientConjugate k L k σ) x) =
    Lie.affineMap T.toGrp σ.toAlgHom
      (Lie.affineMap T.toGrp (tensorUnitMap k L) x)
  rw [← Lie.affineMap_comp, ← Lie.affineMap_comp]
  have h : (tensorUnitMap k L).comp (TensorGaloisPoint.coefficientConjugate k L k σ) =
      σ.toAlgHom.comp (tensorUnitMap k L) := by
    ext; simp [tensorUnitMap, TensorGaloisPoint.coefficientConjugate]
  rw [h]

/-- At the base test algebra, the tensor norm is the existing coefficient norm. -/
theorem tensorNorm_eq (x : Lie.AffinePoints T.toGrp (L ⊗[k] k)) :
    TensorGaloisPoint.norm k L k T x =
      GaloisPoint.norm k L T (Lie.affineMap T.toGrp (tensorUnitMap k L) x) := by
  apply GaloisPoint.extend_injective k L T.toGrp
  rw [GaloisPoint.extend_norm]
  have h := congrArg (Lie.affineMap T.toGrp (tensorUnitMap k L))
    (TensorGaloisPoint.extend_norm k L k T x)
  rw [tensorUnitMap_extend, map_prod] at h
  exact h.trans (Finset.prod_congr rfl (fun σ _ => tensorUnitMap_conjugate k L T σ x))

local notation "T_L" => GaloisPointComparison.baseChanged k L T.toGrp

omit [FiniteDimensional k L] [IsGalois k L] [IsAffine T.X.left] in
/-- The affine pullback comparison agrees with the existing rational comparison. -/
theorem baseChange_rationalCoeff (x : rationalPoints T_L) :
    Lie.affineBaseChangeEquiv k L T.toGrp L
        (GaloisPointComparison.rationalCoeffEquiv L T_L x) =
      GaloisPointComparison.baseChangeCoeffEquiv k L T.toGrp x := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left,
    GaloisPointComparison.rationalCoeffEquiv_left,
    GaloisPointComparison.baseChangeCoeffEquiv_left]

variable
  [IsAffine (GaloisPointComparison.baseChanged k L T.toGrp).X.left]
  [LocallyOfFiniteType (GaloisPointComparison.baseChanged k L T.toGrp).X.hom]

/-- The prescribed identification from extension rational points to Weil rational points. -/
def rationalPointsEquiv :
    rationalPoints T_L ≃* rationalPoints (AffineWeil.groupScheme k L T_L) :=
  (GaloisPointComparison.rationalCoeffEquiv L T_L).trans
    ((AffineWeil.basePointsEquiv k L T_L).symm.trans
      (GaloisPointComparison.rationalCoeffEquiv k
        (AffineWeil.groupScheme k L T_L)).symm)

omit [IsGalois k L] [IsAffine T.X.left] in
/-- The rational-point equivalence has the prescribed coefficient formula. -/
theorem rationalPointsEquiv_coeff (x : rationalPoints T_L) :
    GaloisPointComparison.rationalCoeffEquiv k (AffineWeil.groupScheme k L T_L)
        (rationalPointsEquiv k L T x) =
      (AffineWeil.basePointsEquiv k L T_L).symm
        (GaloisPointComparison.rationalCoeffEquiv L T_L x) := by
  exact (GaloisPointComparison.rationalCoeffEquiv k
    (AffineWeil.groupScheme k L T_L)).apply_symm_apply _

/-- The algebraic norm realizes the existing rational norm under the canonical comparisons. -/
theorem norm_rationalPoints (x : rationalPoints T_L) :
    rationalPoints.map (norm k L T) (rationalPointsEquiv k L T x) =
      GaloisPointComparison.rationalNorm k L T x := by
  apply (GaloisPointComparison.rationalCoeffEquiv k T.toGrp).injective
  rw [GaloisPointComparison.rationalCoeffEquiv_map, affinePointsTarget_apply,
    rationalPointsEquiv_coeff,
    GaloisPointComparison.rationalCoeffEquiv_rationalNorm,
    norm_affinePoints, tensorNorm_eq]
  apply congrArg (GaloisPoint.norm k L T)
  dsimp only [tensorUnitMap]
  rw [← Lie.affineBaseChangeEquiv_naturality k L T.toGrp
    (Algebra.TensorProduct.rid k L L).toAlgHom]
  change Lie.affineBaseChangeEquiv k L T.toGrp L
      (AffineWeil.basePointsEquiv k L T_L
        ((AffineWeil.basePointsEquiv k L T_L).symm
          (GaloisPointComparison.rationalCoeffEquiv L T_L x))) = _
  rw [MulEquiv.apply_symm_apply]
  exact baseChange_rationalCoeff k L T x

end Langlands.GroupScheme.GaloisNorm

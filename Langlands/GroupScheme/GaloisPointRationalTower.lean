import Langlands.GroupScheme.GaloisPointTransitivity
import Langlands.GroupScheme.GaloisPointRational
import Langlands.AlgebraicGeometry.PointTopology.RingPointBaseChange

/-! # Relative norms and actual base changes in a field tower -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPointComparison

open GaloisPoint

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- Coefficient points of a base change are coefficient points of the original group. -/
def coefficientBaseChangeEquiv :
    (baseChanged k L G).affinePoints (CommAlgCat.of L M) ≃*
      G.affinePoints (CommAlgCat.of k M) :=
  (baseChangePointsEquiv (baseMap k L) G (ringTest L M)).trans
    (G.points.mapIso (ringTestRestrictScalarsIso k L M).symm.op).groupIsoToMulEquiv

@[simp] theorem coefficientBaseChangeEquiv_left
    (x : (baseChanged k L G).affinePoints (CommAlgCat.of L M)) :
    (coefficientBaseChangeEquiv k L M G x).left =
      x.left ≫ pullback.fst G.X.hom (baseMap k L) := by
  change 𝟙 _ ≫ (x.left ≫ pullback.fst G.X.hom (baseMap k L)) = _
  simp only [Category.id_comp]

@[simp] theorem coefficientBaseChangeEquiv_rationalCoeffEquiv
    (x : rationalPoints (baseChanged k L G)) :
    coefficientBaseChangeEquiv k L L G
        (rationalCoeffEquiv L (baseChanged k L G) x) =
      baseChangeCoeffEquiv k L G x := by
  apply Over.OverMorphism.ext
  simp only [coefficientBaseChangeEquiv_left, rationalCoeffEquiv_left,
    baseChangeCoeffEquiv_left]

theorem coefficientBaseChangeEquiv_extend
    (x : (baseChanged k L G).affinePoints (CommAlgCat.of L L)) :
    coefficientBaseChangeEquiv k L M G (extend L M (baseChanged k L G) x) =
      relativeExtend k L M G (coefficientBaseChangeEquiv k L L G x) := by
  apply Over.OverMorphism.ext
  rw [coefficientBaseChangeEquiv_left]
  change (baseMap L M ≫ x.left) ≫ pullback.fst G.X.hom (baseMap k L) =
    baseMap L M ≫ (coefficientBaseChangeEquiv k L L G x).left
  rw [coefficientBaseChangeEquiv_left, Category.assoc]

theorem coefficientBaseChangeEquiv_conjugate (σ : M ≃ₐ[L] M)
    (x : (baseChanged k L G).affinePoints (CommAlgCat.of L M)) :
    coefficientBaseChangeEquiv k L M G (conjugate L M (baseChanged k L G) σ x) =
      relativeConjugate k L M G σ (coefficientBaseChangeEquiv k L M G x) := by
  apply Over.OverMorphism.ext
  rw [coefficientBaseChangeEquiv_left]
  change (Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫ x.left) ≫
      pullback.fst G.X.hom (baseMap k L) =
    Spec.map (CommRingCat.ofHom σ.toRingEquiv.toRingHom) ≫
      (coefficientBaseChangeEquiv k L M G x).left
  rw [coefficientBaseChangeEquiv_left, Category.assoc]

variable [FiniteDimensional L M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

private instance commBaseChanged_isAffine :
    IsAffine ((CommGroupScheme.baseChange (baseMap k L)).obj T).X.left := by
  change IsAffine (pullback T.X.hom (baseMap k L))
  infer_instance

/-- The norm of the actual base change is the relative norm on original coefficients. -/
theorem coefficientBaseChangeEquiv_norm
    (x : affinePoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp
      (CommAlgCat.of L M)) :
    coefficientBaseChangeEquiv k L L T.toGrp
        (norm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) x) =
      relativeNorm k L M T (coefficientBaseChangeEquiv k L M T.toGrp x) := by
  apply relativeExtend_injective k L M T.toGrp
  rw [← coefficientBaseChangeEquiv_extend]
  change coefficientBaseChangeEquiv k L M T.toGrp
    (extend L M ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp
      (norm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) x)) = _
  rw [extend_norm, map_prod, relativeExtend_norm]
  exact Finset.prod_congr rfl (fun σ _ =>
    coefficientBaseChangeEquiv_conjugate k L M T.toGrp σ x)

/-- A norm between two direct base changes, retaining the original group over k. -/
def relativeRationalNorm :
    rationalPoints ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp →*
      rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp :=
  (baseChangeCoeffEquiv k L T.toGrp).symm.toMonoidHom.comp
    ((relativeNorm k L M T).comp (baseChangeCoeffEquiv k M T.toGrp).toMonoidHom)

@[simp] theorem baseChangeCoeffEquiv_relativeRationalNorm
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp) :
    baseChangeCoeffEquiv k L T.toGrp (relativeRationalNorm k L M T x) =
      relativeNorm k L M T (baseChangeCoeffEquiv k M T.toGrp x) := by
  exact (baseChangeCoeffEquiv k L T.toGrp).apply_symm_apply _

variable [FiniteDimensional k L] [FiniteDimensional k M]
  [IsGalois k L] [IsGalois k M]

/-- Norms compose on the existing rational-point carriers of the original group. -/
theorem rationalNorm_relativeRationalNorm
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k M)).obj T).toGrp) :
    rationalNorm k L T (relativeRationalNorm k L M T x) = rationalNorm k M T x := by
  apply (rationalCoeffEquiv k T.toGrp).injective
  simp only [rationalCoeffEquiv_rationalNorm, baseChangeCoeffEquiv_relativeRationalNorm,
    norm_relativeNorm]

end Langlands.GroupScheme.GaloisPointComparison

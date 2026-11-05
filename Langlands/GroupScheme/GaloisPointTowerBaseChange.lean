import Langlands.GroupScheme.GaloisPointRationalTower

/-! # Direct and iterated base changes in a field tower -/

noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.GaloisPointComparison

open GaloisPoint

private def baseChangeCompEqIso {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (d : S'' ⟶ S) (h : c ≫ b = d)
    (G : GroupScheme S) :
    (Over.pullback c).mapGrp.obj ((Over.pullback b).mapGrp.obj G) ≅
      (Over.pullback d).mapGrp.obj G :=
  (baseChangeCompIso b c G).symm ≪≫
    eqToIso (congrArg (fun e => (Over.pullback e).mapGrp.obj G) h)

private theorem baseChangeCompEqIso_hom_fst {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') (d : S'' ⟶ S) (h : c ≫ b = d)
    (G : GroupScheme S) :
    (baseChangeCompEqIso b c d h G).hom.hom.hom.left ≫ pullback.fst G.X.hom d =
      pullback.fst (pullback.snd G.X.hom b) c ≫ pullback.fst G.X.hom b := by
  subst d
  change ((baseChangeCompIso b c G).inv.hom.hom.left ≫ 𝟙 _) ≫ _ = _
  rw [Category.comp_id, baseChangeCompIso_inv_fst]

variable (k L M : Type u) [Field k] [Field L] [Field M]
  [Algebra k L] [Algebra k M] [Algebra L M] [IsScalarTower k L M]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The scheme base maps compose in the opposite direction to the field maps. -/
theorem baseMap_tower : baseMap L M ≫ baseMap k L = baseMap k M := by
  rw [baseMap, baseMap, baseMap, ← Spec.map_comp]
  congr 1
  exact congrArg CommRingCat.ofHom (IsScalarTower.algebraMap_eq k L M).symm

/-- The standard pullback comparison identifies iterated and direct base changes. -/
def towerBaseChangeIso :
    baseChanged L M (baseChanged k L G) ≅ baseChanged k M G :=
  baseChangeCompEqIso (baseMap k L) (baseMap L M) (baseMap k M) (baseMap_tower k L M) G

/-- The tower comparison preserves projection to the original group scheme. -/
theorem towerBaseChangeIso_hom_fst :
    (towerBaseChangeIso k L M G).hom.hom.hom.left ≫ pullback.fst G.X.hom (baseMap k M) =
      pullback.fst (pullback.snd G.X.hom (baseMap k L)) (baseMap L M) ≫
        pullback.fst G.X.hom (baseMap k L) :=
  baseChangeCompEqIso_hom_fst _ _ _ _ _

/-- The point map of the tower comparison is the successive coefficient projection. -/
theorem baseChangeCoeffEquiv_towerBaseChangeIso
    (x : rationalPoints (baseChanged L M (baseChanged k L G))) :
    baseChangeCoeffEquiv k M G (rationalPoints.map (towerBaseChangeIso k L M G).hom x) =
      coefficientBaseChangeEquiv k L M G
        (baseChangeCoeffEquiv L M (baseChanged k L G) x) := by
  apply Over.OverMorphism.ext
  rw [baseChangeCoeffEquiv_left, coefficientBaseChangeEquiv_left,
    baseChangeCoeffEquiv_left]
  change (x.left ≫ (towerBaseChangeIso k L M G).hom.hom.hom.left) ≫
      pullback.fst G.X.hom (baseMap k M) = _
  rw [Category.assoc, towerBaseChangeIso_hom_fst, Category.assoc]
  rfl

variable [FiniteDimensional L M] [IsGalois L M]
  (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

private instance commBaseChanged_isAffine :
    IsAffine ((CommGroupScheme.baseChange (baseMap k L)).obj T).X.left := by
  change IsAffine (pullback T.X.hom (baseMap k L))
  infer_instance

/-- Relative norms of direct base changes are the ordinary norms of the lower base change. -/
theorem relativeRationalNorm_towerBaseChangeIso
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap L M)).obj
      ((CommGroupScheme.baseChange (baseMap k L)).obj T)).toGrp) :
    relativeRationalNorm k L M T
        (rationalPoints.map (towerBaseChangeIso k L M T.toGrp).hom x) =
      rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) x := by
  apply (baseChangeCoeffEquiv k L T.toGrp).injective
  rw [baseChangeCoeffEquiv_relativeRationalNorm]
  rw [← coefficientBaseChangeEquiv_rationalCoeffEquiv k L T.toGrp]
  change _ = coefficientBaseChangeEquiv k L L T.toGrp
    (rationalCoeffEquiv L ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp
      (rationalNorm L M ((CommGroupScheme.baseChange (baseMap k L)).obj T) x))
  rw [rationalCoeffEquiv_rationalNorm, coefficientBaseChangeEquiv_norm]
  congr 1
  exact baseChangeCoeffEquiv_towerBaseChangeIso k L M T.toGrp x

end Langlands.GroupScheme.GaloisPointComparison

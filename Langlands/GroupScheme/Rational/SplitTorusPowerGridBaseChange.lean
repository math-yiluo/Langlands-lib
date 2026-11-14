import Langlands.GroupScheme.Rational.BoundedSplitTorusMaps
import Langlands.GroupScheme.Torus.RingRepresentationWeightsBaseChange

/-! # Base change of rational split-torus power grids -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.BoundedTorusOrbits

open GaloisPointComparison

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (I : Type u) [Fintype I] [DecidableEq I]

/-- The image of an integer-power tuple under a homomorphism from a split torus. -/
def powerGridPoint {G : GroupScheme (Spec (CommRingCat.of k))}
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (π : kˣ)
    (n : Multiplicative (I → ℤ)) : rationalPoints G :=
  rationalPoints.map j (tuplePoint I (powerTuple I π n))

/-- The identity-test unit coordinates of the tuple point are the specified tuple. -/
theorem affinePointsEquiv_tuplePoint (t : I → kˣ) :
    splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of k))) (tuplePoint I t) = t := by
  have h : ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).symm t).left =
      (tuplePoint I t).left := by
    simpa only [tuplePoint, MulEquiv.apply_symm_apply] using
      rationalCoeffEquiv_left k _ (tuplePoint I t)
  have hc : splitTorus.affinePointsEquiv I (𝟙 (Spec (CommRingCat.of k)))
      (tuplePoint I t) = splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k
        ((splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I k).symm t) := by
    funext i
    apply Units.ext
    change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        (Gm.pointsEquiv _ _ (tuplePoint I t ≫
          (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp) i).hom.hom)).val =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom
        (Gm.pointsEquiv _ _ ((splitTorus.algebraPointsEquiv
          (R := CommRingCat.of k) I k).symm t ≫
          (Limits.Pi.π (fun _ : I => (Gm (Spec (CommRingCat.of k))).toGrp) i).hom.hom)).val
    rw [Gm.pointsEquiv_val, Gm.pointsEquiv_val]
    simp only [Over.comp_left]
    rw [h]
    rfl
  exact hc.trans (MulEquiv.apply_symm_apply _ _)

/-- Rational extension commutes with a group-scheme homomorphism. -/
theorem rationalExtend_map {G H : GroupScheme (Spec (CommRingCat.of k))}
    (j : G ⟶ H) (x : rationalPoints G) :
    rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map j)
        (rationalExtend k L G x) =
      rationalExtend k L H (rationalPoints.map j x) := by
  apply (baseChangeCoeffEquiv k L H).injective
  rw [baseChangeCoeffEquiv_map, baseChangeCoeffEquiv_rationalExtend,
    baseChangeCoeffEquiv_rationalExtend, rationalCoeffEquiv_map]
  apply Over.OverMorphism.ext
  simp [GaloisPoint.extend, affinePointsTarget_apply, affinePointMap_apply,
    Category.assoc]

/-- A coordinate tuple after base change represents the extension of its original point. -/
theorem baseChangeIso_inv_tuplePoint (t : I → kˣ) :
    rationalPoints.map (splitTorus.baseChangeIso (baseMap k L) I).inv
        (tuplePoint I (fun i => Units.map (algebraMap k L).toMonoidHom (t i))) =
      rationalExtend k L (splitTorus (Spec (CommRingCat.of k)) I) (tuplePoint I t) := by
  apply (baseChangeCoeffEquiv k L _).injective
  rw [baseChangeCoeffEquiv_rationalExtend]
  apply (splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I L).injective
  change splitTorus.affinePointsEquiv I (baseMap k L)
      (GroupScheme.baseChangePointsEquiv (baseMap k L) _ (Over.mk (𝟙 _))
        (tuplePoint I (fun i => Units.map (algebraMap k L).toMonoidHom (t i)) ≫
          (splitTorus.baseChangeIso (baseMap k L) I).inv.hom.hom)) = _
  have hc := splitTorus.affinePointsEquiv_baseChangeIso_inv I (baseMap k L) (𝟙 _)
    (tuplePoint I (fun i => Units.map (algebraMap k L).toMonoidHom (t i)))
  erw [hc, affinePointsEquiv_tuplePoint]
  change _ = splitTorus.algebraPointsEquiv (R := CommRingCat.of k) I L
    (Lie.affineMap _ (Algebra.ofId k L) (rationalCoeffEquiv k _ (tuplePoint I t)))
  rw [splitTorus.algebraPointsEquiv_naturality]
  simp [tuplePoint]

/-- Base change of a split-torus homomorphism transports the full uniformizer-power grid. -/
theorem baseChangeHomAlong_powerTuple {G : GroupScheme (Spec (CommRingCat.of k))}
    (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G) (π : kˣ)
    (n : Multiplicative (I → ℤ)) :
    rationalPoints.map (splitTorus.baseChangeHomAlong I (baseMap k L) j)
        (tuplePoint I (powerTuple I (Units.map (algebraMap k L).toMonoidHom π) n)) =
      rationalExtend k L G (rationalPoints.map j (tuplePoint I (powerTuple I π n))) := by
  have ht : powerTuple I (Units.map (algebraMap k L).toMonoidHom π) n =
      fun i => Units.map (algebraMap k L).toMonoidHom (powerTuple I π n i) := by
    funext i
    simp [powerTuple]
  rw [ht]
  change rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map j)
      (rationalPoints.map (splitTorus.baseChangeIso (baseMap k L) I).inv
        (tuplePoint I (fun i => Units.map (algebraMap k L).toMonoidHom
          (powerTuple I π n i)))) = _
  rw [baseChangeIso_inv_tuplePoint, rationalExtend_map]

end Langlands.GroupScheme.BoundedTorusOrbits

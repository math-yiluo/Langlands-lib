import Langlands.Algebra.IntLatticeAlgebra
import Langlands.GroupScheme.Torus.UniversalPoint
import Langlands.GroupScheme.Lie.AffineCoordinates
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Pointed morphisms of split tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace splitTorus

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    (I J : Type u) [Fintype I] [DecidableEq I] [Finite J]
    (p : (splitTorus (Spec (CommRingCat.of k)) I).X ⟶
      (splitTorus (Spec (CommRingCat.of k)) J).X)
    (hp : η[(splitTorus (Spec (CommRingCat.of k)) I).X] ≫ p =
      η[(splitTorus (Spec (CommRingCat.of k)) J).X])

omit [DecidableEq I] in
include hp in
private theorem pointed_one {T : Over (Spec (CommRingCat.of k))} :
    (1 : T ⟶ (splitTorus (Spec (CommRingCat.of k)) I).X) ≫ p = 1 := by
  rw [Hom.one_def, Category.assoc, hp]
  rfl

omit [DecidableEq I] in
private theorem coordinate_naturality
    {A B : Type u} [CommRing A] [Algebra (CommRingCat.of k) A]
    [CommRing B] [Algebra (CommRingCat.of k) B]
    (f : A →ₐ[CommRingCat.of k] B)
    (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) (j : J) :
    algebraPointsEquiv J B (Lie.affineMap _ f x ≫ p) j =
      Units.map f.toMonoidHom (algebraPointsEquiv J A (x ≫ p) j) := by
  simpa only [Lie.affineMap_apply, Category.assoc] using
    congrFun (algebraPointsEquiv_naturality J f (x ≫ p)) j

include hp in
/-- Each coordinate of a pointed morphism of split tori is one monomial,
with no scalar factor. -/
theorem exists_pointed_coordinate_monomial (j : J) :
    ∃ m : I → ℤ,
      (algebraPointsEquiv J _ (universalPoint (R := CommRingCat.of k) I ≫ p) j :
        AddMonoidAlgebra k (I → ℤ)) = AddMonoidAlgebra.single m 1 := by
  let z := universalPoint (R := CommRingCat.of k) I
  let v := algebraPointsEquiv J _ (z ≫ p) j
  obtain ⟨m, c, hc⟩ :=
    Langlands.IntLatticeAlgebra.exists_eq_single_of_isUnit k I v.isUnit
  let ev := evaluateUnits (R := CommRingCat.of k) I (1 : I → kˣ)
  have he : Lie.affineMap _ ev z = 1 := by
    rw [universalPoint_evaluateUnits]
    exact map_one (algebraPointsEquiv I k).symm
  have h := coordinate_naturality I J p ev z j
  rw [he, pointed_one I J p hp, map_one, Pi.one_apply] at h
  have h' := congrArg Units.val h
  change (1 : k) = ev (v : AddMonoidAlgebra k (I → ℤ)) at h'
  rw [hc, evaluateUnits_single] at h'
  have hc1 : (c : k) = 1 := by
    simpa [exponentValue] using h'.symm
  exact ⟨m, by simpa only [v, z, hc1] using hc⟩

/-- A coordinate monomial at the universal point controls the value on every
affine algebra test. -/
theorem pointed_coordinate_formula
    {m : I → ℤ} {j : J}
    (hm : (algebraPointsEquiv J _
      (universalPoint (R := CommRingCat.of k) I ≫ p) j :
        AddMonoidAlgebra k (I → ℤ)) = AddMonoidAlgebra.single m 1)
    {A : Type u} [CommRing A] [Algebra (CommRingCat.of k) A]
    (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
    algebraPointsEquiv J A (x ≫ p) j =
      ∏ i, algebraPointsEquiv I A x i ^ m i := by
  have h := coordinate_naturality I J p
    (evaluateUnits (R := CommRingCat.of k) I (algebraPointsEquiv I A x))
    (universalPoint (R := CommRingCat.of k) I) j
  rw [universalPoint_evaluateUnits, MulEquiv.symm_apply_apply] at h
  apply Units.ext
  have h' := congrArg Units.val h
  change _ = evaluateUnits I (algebraPointsEquiv I A x) _ at h'
  rw [hm, evaluateUnits_single, map_one, one_mul] at h'
  exact h'

include hp in
/-- A scheme morphism between split tori carrying the identity to the identity
is the underlying morphism of an actual group-scheme homomorphism. -/
theorem exists_hom_of_pointed_morphism :
    ∃ f : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J, f.hom.hom = p := by
  classical
  let := isAffineHom_splitTorus_spec (CommRingCat.of k) I
  choose m hm using exists_pointed_coordinate_monomial I J p hp
  let f : splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J :=
    Pi.lift (fun j => CommGroupScheme.groupHom ((characterLatticeEquiv k I).symm (m j)))
  refine ⟨f, ?_⟩
  have hpoints {A : Type u} [CommRing A] [Algebra (CommRingCat.of k) A]
      (x : Lie.AffinePoints (splitTorus (Spec (CommRingCat.of k)) I) A) :
      x ≫ f.hom.hom = x ≫ p := by
    apply (algebraPointsEquiv J A).injective
    funext j
    have hf : (x ≫ f.hom.hom) ≫
        (Pi.π (fun _ : J => (Gm (Spec (CommRingCat.of k))).toGrp) j).hom.hom =
      x ≫ (CommGroupScheme.groupHom ((characterLatticeEquiv k I).symm (m j))).hom.hom := by
      rw [Category.assoc]
      change x ≫ (f ≫ Pi.π _ j).hom.hom = _
      dsimp only [f]
      rw [Pi.lift_comp_π]
    have hcoord := pointed_coordinate_formula I J p (hm j) x
    have hchar_aff :
        Gm.affinePointsEquiv (R := CommRingCat.of A)
          ((algSpec (CommRingCat.of k)).obj
            (Opposite.op (CommAlgCat.of (CommRingCat.of k) A))).hom
          (x ≫ (CommGroupScheme.groupHom
            ((characterLatticeEquiv k I).symm (m j))).hom.hom) =
          ∏ i, algebraPointsEquiv I A x i ^ m j i := by
      rw [characterLatticeEquiv_symm_eq]
      refine (congrArg
        (Gm.affinePointsEquiv (R := CommRingCat.of A)
          ((algSpec (CommRingCat.of k)).obj
            (Opposite.op (CommAlgCat.of (CommRingCat.of k) A))).hom)
        (comp_groupHom_sum (G := commGroupScheme (Spec (CommRingCat.of k)) I)
          x Finset.univ fun i => m j i • proj _ I i)).trans ?_
      rw [map_prod]
      refine Finset.prod_congr rfl fun i _ => ?_
      refine (congrArg
        (Gm.affinePointsEquiv (R := CommRingCat.of A)
          ((algSpec (CommRingCat.of k)).obj
            (Opposite.op (CommAlgCat.of (CommRingCat.of k) A))).hom)
        (comp_groupHom_zsmul (G := commGroupScheme (Spec (CommRingCat.of k)) I)
          x (m j i) (proj _ I i))).trans ?_
      rw [map_zpow]
      rfl
    exact (congrArg
      (Gm.affinePointsEquiv
        (R := CommRingCat.of A)
        ((algSpec (CommRingCat.of k)).obj
          (Opposite.op (CommAlgCat.of (CommRingCat.of k) A))).hom) hf).trans
        (hchar_aff.trans hcoord.symm)
  exact (cancel_epi (Lie.coordinateIso
    (splitTorus (Spec (CommRingCat.of k)) I)).hom).mp
    (hpoints (Lie.coordinateIso (splitTorus (Spec (CommRingCat.of k)) I)).hom)

/-- The group-scheme homomorphism underlying a supplied pointed morphism of
canonical split tori. -/
def homOfPointedMorphism :
    splitTorus (Spec (CommRingCat.of k)) I ⟶
      splitTorus (Spec (CommRingCat.of k)) J :=
  (exists_hom_of_pointed_morphism I J p hp).choose

@[simp] theorem homOfPointedMorphism_hom :
    (homOfPointedMorphism I J p hp).hom.hom = p :=
  (exists_hom_of_pointed_morphism I J p hp).choose_spec

end splitTorus

end Langlands.GroupScheme

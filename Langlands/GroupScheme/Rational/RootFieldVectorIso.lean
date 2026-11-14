import Langlands.GroupScheme.VectorLinearIso
import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.RootPointLieNaturality

/-! # Actual root-group isomorphisms realizing root-field coordinates -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u w

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]

section RationalCoordinates

variable {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}
    (c : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤)))
    (hc : IsNaturalVectorCoordinates c)

include hc in
/-- Passing from identity-test sections to base-field affine points preserves
the coefficient coordinates of any natural vector-coordinate system. -/
theorem vectorAffineCoordinates_rationalCoeffEquiv (g : rationalPoints V) :
    (vectorAffineCoordinates c k (GaloisPointComparison.rationalCoeffEquiv k V g)).toAdd =
      fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
        ((c (Over.mk (𝟙 _)) g).toAdd j) := by
  change (fun j => (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((c _ ((Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom ≫ g)).toAdd j)) = _
  rw [hc _ _ (Langlands.AlgebraicGeometry.PointTopology.ringTestSelfIso k).hom]
  funext j
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom
    ((𝟙 (Spec (CommRingCat.of k)) :
        Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)).appTop.hom
      ((c (Over.mk (𝟙 _)) g).toAdd j)) = _
  simp

/-- The scheme isomorphism from natural vector coordinates has those same
coordinates in the base-field affine-point convention. -/
theorem sectionCoordinates_vectorGroupIso_eq_affine (g : rationalPoints V) :
    (VectorGroup.sectionCoordinates (CommRingCat.of k) n
      (rationalPoints.map (vectorGroupIso c hc).hom g)).toAdd =
        (vectorAffineCoordinates c k (GaloisPointComparison.rationalCoeffEquiv k V g)).toAdd := by
  rw [vectorAffineCoordinates_rationalCoeffEquiv c hc]
  funext j
  rw [VectorGroup.sectionCoordinates_apply, rationalPoints.map_apply,
    coordinates_comp_vectorGroupIso_hom]

end RationalCoordinates

variable {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [IsAffineHom U.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    {E : Type w} [Field E] [Algebra k E] {m : ℕ}
    (W : E ≃ₗ[k] weightSpace i a) (b : Module.Basis (Fin m) k E)

/-- The linear correction from the chosen weight coordinates to a prescribed
field-to-weight-space equivalence and field basis. -/
def rootFieldVectorLinearEquiv :
    (Fin (weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj).1 → k) ≃ₗ[k]
      (Fin m → k) :=
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  (((vectorLieCoordinates c.2.val c.2.property.1 (CommAlgCat.of k k)).symm.trans
    (representedRootLieEquiv hS i ha hhigh hj)).trans W.symm).trans b.equivFun

/-- An actual all-test root-group isomorphism whose rational coordinates
realize the prescribed root-field comparison. -/
def rootFieldVectorIso : U ≅ VectorGroup.groupScheme (CommRingCat.of k) m :=
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  vectorGroupIso c.2.val c.2.property.1 ≪≫
    VectorGroup.linearIso (R := CommRingCat.of k)
      (rootFieldVectorLinearEquiv hS i ha hhigh hj W b)

/-- On actual rational sections, the scheme isomorphism gives precisely the
field coordinates defined by the intrinsic root-point Lie comparison. -/
theorem sectionCoordinates_rootFieldVectorIso (g : rationalPoints U) :
    (VectorGroup.sectionCoordinates (CommRingCat.of k) m
      (rationalPoints.map (rootFieldVectorIso hS i ha hhigh hj W b).hom g)).toAdd =
        b.equivFun (W.symm
          (rootPointLieEquiv hS i ha hhigh (Additive.ofMul (hj.pointsEquiv _ g)))) := by
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  change (VectorGroup.sectionCoordinates (CommRingCat.of k) m
    (rationalPoints.map
      (VectorGroup.linearIso (R := CommRingCat.of k)
        (rootFieldVectorLinearEquiv hS i ha hhigh hj W b)).hom
      (rationalPoints.map (vectorGroupIso c.2.val c.2.property.1).hom g))).toAdd = _
  rw [VectorGroup.sectionCoordinates_linearIso,
    sectionCoordinates_vectorGroupIso_eq_affine]
  rw [rootPointLieEquiv_eq_represented hS i ha hhigh hj]
  change b.equivFun (W.symm (representedRootLieEquiv hS i ha hhigh hj
      ((vectorLieCoordinates c.2.val c.2.property.1 (CommAlgCat.of k k)).symm
        (vectorAffineCoordinates c.2.val k
          (GaloisPointComparison.rationalCoeffEquiv k U g)).toAdd))) =
    b.equivFun (W.symm (representedRootLieEquiv hS i ha hhigh hj
      (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U
          ((hj.pointsEquiv _).symm (hj.pointsEquiv _ g)))))))
  rw [MulEquiv.symm_apply_apply]
  rfl

end Langlands.GroupScheme.RelativeRoot

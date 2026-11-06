import Langlands.GroupScheme.Rational.VectorPointLieEquiv
import Langlands.GroupScheme.Rational.RootSubgroupWeightCoordinates
import Langlands.GroupScheme.Rational.CyclicTailWeightSpan
import Langlands.GroupScheme.Lie.SubgroupCellDimension
import Langlands.GroupScheme.GaloisPointRational

/-! # Actual root points and their single Lie weight -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- In the absence of higher roots, the first positive cyclic Lie span is
exactly the original weight space. -/
theorem semigroupWeightSpan_eq_weightSpace_of_noHigherRoots
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a) :
    semigroupWeightSpan (AutomorphicAction.conjugation i) (cyclicTail a 1) =
      weightSpace i a := by
  rw [semigroupWeightSpan_cyclicTail]
  apply le_antisymm
  · refine iSup_le fun n => ?_
    rw [actionWeightSpace_conjugation]
    by_cases hn : n.val = 1
    · simp only [hn, one_smul, le_refl]
    · have hbot : weightSpace i (n.val • a) = ⊥ := by
        by_contra h
        exact hhigh n.val (by have := n.property; omega)
          ⟨hS.nsmul_ne_zero ha (Nat.ne_of_gt n.property.2), h⟩
      rw [hbot]
      exact bot_le
  · simpa only [actionWeightSpace_conjugation, one_smul] using
      (le_iSup (fun n : {n : ℕ // 1 ≤ n ∧ 0 < n} =>
        actionWeightSpace (AutomorphicAction.conjugation i) (n.val • a))
          ⟨1, by decide, by decide⟩)

variable [Smooth G.X.hom]

/-- The intrinsic tangent of a root functor without higher roots is its
actual adjoint weight space. -/
theorem tangentSubmodule_eq_weightSpace_of_noHigherRoots
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a) :
    tangentSubmodule (subgroup i a) = weightSpace i a := by
  rw [tangentSubmodule_subgroup i a hS ha,
    semigroupWeightSpan_eq_weightSpace_of_noHigherRoots hS i ha hhigh]

variable {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]

/-- The actual Lie module of any representative identifies with the exact
root weight space when higher roots are absent. -/
def representedRootLieEquiv
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) :
    Additive (lieKernel U k) ≃ₗ[k] weightSpace i a :=
  (representedTangentLinearEquiv (subgroup i a) j hj).trans
    (LinearEquiv.ofEq _ _
      (tangentSubmodule_eq_weightSpace_of_noHigherRoots hS i ha hhigh))

@[simp]
theorem representedRootLieEquiv_coe
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j)
    (X : Additive (lieKernel U k)) :
    (representedRootLieEquiv hS i ha hhigh hj X : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k X := rfl

/-- Natural coordinates of the original root weight identify the actual
root points with actual weight vectors, via any affine representative. -/
def representedRootPointLieEquiv
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) :
    Additive ((subgroup i a).carrier (Over.mk (𝟙 _))) ≃+ weightSpace i a :=
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  (((hj.pointsEquiv _).symm.trans
      (GaloisPointComparison.rationalCoeffEquiv k U)).toAdditive).trans
    ((vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)).trans
      (representedRootLieEquiv hS i ha hhigh hj).toAddEquiv)

/-- On represented points the comparison is the actual differential applied
to the vector group's point-to-kernel comparison. -/
theorem representedRootPointLieEquiv_apply
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a)
    {j : U ⟶ G} (hj : (subgroup i a).IsRepresentedBy j) (v : rationalPoints U) :
    let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
    (representedRootPointLieEquiv hS i ha hhigh hj
        (Additive.ofMul (hj.pointsEquiv _ v)) : Additive (lieKernel G k)) =
      Lie.targetMapLinear j k
        (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
          (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U v))) := by
  let c := weightVectorCoordinatesOfNoHigherRoots hS i ha hhigh hj
  change Lie.targetMapLinear j k
      (vectorPointLieEquiv c.2.val c.2.property.1 (CommAlgCat.of k k)
        (Additive.ofMul (GaloisPointComparison.rationalCoeffEquiv k U
          ((hj.pointsEquiv _).symm (hj.pointsEquiv _ v))))) = _
  rw [MulEquiv.symm_apply_apply]

omit [IsAffineHom U.X.hom] in
/-- Actual root points have additive coordinates in their intrinsic adjoint
weight space without supplied vector coordinates or a supplied representative. -/
def rootPointLieEquiv
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a) :
    Additive ((subgroup i a).carrier (Over.mk (𝟙 _))) ≃+ weightSpace i a := by
  let h := subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha
  let U := h.choose
  let j : U ⟶ G := h.choose_spec.choose
  have hj : (subgroup i a).IsRepresentedBy j := h.choose_spec.choose_spec.1
  let : IsAffineHom U.X.hom := h.choose_spec.choose_spec.2.1.isAffineHom
  exact representedRootPointLieEquiv hS i ha hhigh hj

omit [IsAffineHom U.X.hom] in
/-- The chosen comparison is realized by the point-to-differential comparison
of an actual affine representative. -/
theorem rootPointLieEquiv_exists_representative
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    {a : characterLattice S} (ha : a ≠ 0) (hhigh : HasNoHigherRoots i a) :
    ∃ (U : GroupScheme (Spec (CommRingCat.of k))) (_hU : IsAffineHom U.X.hom)
      (j : U ⟶ G) (hj : (subgroup i a).IsRepresentedBy j),
      rootPointLieEquiv hS i ha hhigh =
        representedRootPointLieEquiv hS i ha hhigh hj := by
  let h := subgroup_isSmoothConnectedClosed_of_ne_zero hS i a ha
  exact ⟨h.choose, h.choose_spec.choose_spec.2.1.isAffineHom,
    h.choose_spec.choose, h.choose_spec.choose_spec.1, rfl⟩

end Langlands.GroupScheme.RelativeRoot

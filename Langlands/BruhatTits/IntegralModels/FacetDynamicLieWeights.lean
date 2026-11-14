import Langlands.BruhatTits.IntegralModels.FacetLieWeights
import Langlands.GroupScheme.Rational.RootSignParabolicLie
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Actual Lie-image weights of represented dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.BruhatTits.IntegralModels

open GroupScheme GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {H : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom]

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

local instance (lambda : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    IsAffineHom (Dynamic.Affine.parabolicScheme lambda).X.hom := by
  have : IsClosedImmersion (Dynamic.Affine.parabolicHom lambda).hom.hom.left :=
    Dynamic.Affine.isClosedSubgroup_parabolicHom lambda
  rw [← Over.w (Dynamic.Affine.parabolicHom lambda).hom.hom]
  infer_instance

/-- The actual nonzero differential-image weights of the canonical closed
representative of the dynamic parabolic of a torus cocharacter. -/
def dynamicParabolicLieWeights (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Set (characterLattice S) :=
  nonzeroLieImageWeights i (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i))

/-- The existing differential-image support is the nonzero part of the
intrinsic conjugation-action support of any monomorphic representative. -/
theorem nonzeroLieImageWeights_eq_actionWeightSupport
    (i : S.toGrp ⟶ G) (j : H ⟶ G) {F : SubgroupFunctor G}
    (hj : F.IsRepresentedBy j) :
    nonzeroLieImageWeights i j =
      {χ | χ ≠ 0 ∧ χ ∈ actionWeightSupport (AutomorphicAction.conjugation i) F} := by
  have h := (hasLieImage_of_isRepresentedBy j hj).actionWeightSupport_eq
    (AutomorphicAction.conjugation i)
  ext χ
  simp only [nonzeroLieImageWeights, Set.mem_ofPred_eq, h,
    actionWeightSpace_conjugation]

/-- For an actual representative of a dynamic parabolic, the nonzero weights
of its differential image are exactly the actual roots with nonnegative pairing.
Smoothness and connectedness are unnecessary for this computation. -/
theorem nonzeroLieImageWeights_parabolic [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (j : H ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j) :
    nonzeroLieImageWeights i j =
      {χ | χ ∈ relativeRoots i ∧ 0 ≤ latticePairing S χ ν} := by
  have hLie := (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
    (tangentSubmodule_parabolic_eq_semigroupWeightSpan hS i ν)
  rw [nonzeroLieImageWeights_eq_actionWeightSupport i j hj]
  ext χ
  have hw := HasLieImage.mem_actionWeightSupport_iff
    (AutomorphicAction.conjugation i) hS (nonnegativeSemigroup ν) hLie χ
  rw [actionWeightSpace_conjugation] at hw
  simp only [Set.mem_ofPred_eq, hw, mem_relativeRoots]
  change (χ ≠ 0 ∧ (0 ≤ latticePairing S χ ν ∧ weightSpace i χ ≠ ⊥)) ↔
    (χ ≠ 0 ∧ weightSpace i χ ≠ ⊥) ∧ 0 ≤ latticePairing S χ ν
  exact ⟨fun h => ⟨⟨h.1, h.2.2⟩, h.2.1⟩,
    fun h => ⟨h.1.1, h.2, h.1.2⟩⟩

/-- The canonical actual differential-image support is computed by the
nonnegative pairings on actual relative roots. -/
theorem dynamicParabolicLieWeights_eq [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    dynamicParabolicLieWeights i ν =
      {χ | χ ∈ relativeRoots i ∧ 0 ≤ latticePairing S χ ν} :=
  nonzeroLieImageWeights_parabolic hS i ν _
    (Dynamic.Affine.isRepresentedBy_parabolicHom _)

/-- Every monomorphic representative computes the same canonical support. -/
theorem nonzeroLieImageWeights_eq_dynamicParabolicLieWeights
    [LocallyOfFiniteType G.X.hom]
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (ν : cocharacterLattice S) (j : H ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).IsRepresentedBy j) :
    nonzeroLieImageWeights i j = dynamicParabolicLieWeights i ν := by
  rw [nonzeroLieImageWeights_parabolic hS i ν j hj, dynamicParabolicLieWeights_eq hS]

section Order

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
  {H' : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H'.X.hom]

/-- In a smooth connected ambient group, inclusion of represented dynamic
parabolics is detected by the concrete nonzero differential-image supports. -/
theorem representedParabolic_le_iff_nonzeroLieImageWeights_subset
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) (j : H ⟶ G) (j' : H' ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j)
    (hj' : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j') :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range j' ↔
      nonzeroLieImageWeights i j ⊆ nonzeroLieImageWeights i j' := by
  rw [hj.2, hj'.2,
    parabolic_le_iff_nonnegative_rootSupport dynamicConnected hS i zeta eta,
    nonzeroLieImageWeights_parabolic hS i zeta j hj,
    nonzeroLieImageWeights_parabolic hS i eta j' hj']
  exact ⟨fun h χ hχ => ⟨hχ.1, h χ hχ.1 hχ.2⟩,
    fun h χ hχ hzeta => (h ⟨hχ, hzeta⟩).2⟩

/-- Equality of represented dynamic parabolics is detected by their actual
nonzero Lie-image weights for the fixed split torus. -/
theorem representedParabolic_eq_iff_nonzeroLieImageWeights_eq
    (hS : IsSplitTorus S.toGrp) (i : S.toGrp ⟶ G)
    (zeta eta : cocharacterLattice S) (j : H ⟶ G) (j' : H' ⟶ G)
    (hj : (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j)
    (hj' : (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).IsRepresentedBy j') :
    SubgroupFunctor.range j = SubgroupFunctor.range j' ↔
      nonzeroLieImageWeights i j = nonzeroLieImageWeights i j' := by
  rw [le_antisymm_iff,
    representedParabolic_le_iff_nonzeroLieImageWeights_subset hS i zeta eta j j' hj hj',
    representedParabolic_le_iff_nonzeroLieImageWeights_subset hS i eta zeta j' j hj' hj]
  exact ⟨fun h => Set.Subset.antisymm h.1 h.2,
    fun h => ⟨h.subset, h.symm.subset⟩⟩

end Order

end Langlands.BruhatTits.IntegralModels

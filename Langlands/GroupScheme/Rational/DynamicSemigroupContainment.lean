import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.CocharacterWeightSums
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

/-! # Containment in a Dynamic functor from its actual tangent image -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

local instance ambient_isAffine {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

set_option backward.isDefEq.respectTransparency false

/-- A smooth connected invariant closed subgroup with tangent image in the
positive pairing span lies in the actual unipotent Dynamic functor. -/
theorem le_dynamicUnipotent_of_tangentSubmodule_le
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν)) :
    F ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  obtain ⟨H, j, hj, hc, hs, hconn⟩ := hF
  have : IsClosedImmersion j.hom.hom.left := hc
  have : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  have : Smooth H.X.hom := hs
  have : ConnectedSpace H.X.left := hconn
  have : Mono j.hom.hom := hj.1
  let b := AutomorphicAction.conjugation i
  let d := b.onRepresentedSubgroup j hj hstable
  let a := d.restrict (CommGroupScheme.groupHom ν)
  let χ := CommGroupScheme.groupHom ν ≫ i
  have heq : a.IsEquivariant (AutomorphicAction.cocharacterAction χ) j := by
    intro T t x
    change (d.restrict (CommGroupScheme.groupHom ν)).act t x ≫ j.hom.hom = _
    rw [AutomorphicAction.restrict_act]
    rw [AutomorphicAction.onRepresentedSubgroup_act_comp]
    simp only [b, χ, AutomorphicAction.cocharacterAction_eq_conjugation,
      AutomorphicAction.conjugation_act, Grp.comp_hom_hom, Category.assoc]
  have hcomap : a.unipotent = (Dynamic.unipotent χ).comap j := by
    simpa only [AutomorphicAction.cocharacterAction_unipotent] using
      heq.unipotent_eq_comap_of_isClosedSubgroup hc
  let K := AutomorphicAction.Affine.unipotentScheme a
  let κ := AutomorphicAction.Affine.unipotentHom a
  have hκ := AutomorphicAction.Affine.isRepresentedBy_unipotentHom a
  have hκc := AutomorphicAction.Affine.isClosedSubgroup_unipotentHom a
  have : Mono κ.hom.hom := hκ.1
  have : Smooth K.X.hom := AutomorphicAction.Affine.smooth_unipotentScheme a
  have htop : SubgroupFunctor.range κ = ⊤ := by
    refine lieSubgroupEquality k H K κ hκc fun X => ?_
    have hXF : (Lie.targetMap j k X).val ∈ F.carrier _ := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    have hXW := hLie hXF
    rw [semigroupWeightSpan_conjugation_positive hS i ν] at hXW
    have hXU : (Lie.targetMap j k X).val ∈ (Dynamic.unipotent χ).carrier _ :=
      ((dynamicLie k G χ (Lie.targetMap j k X)).2.2).mpr hXW
    have hXa : X.val ∈ a.unipotent.carrier _ := by
      rw [hcomap, SubgroupFunctor.mem_comap]
      exact hXU
    rw [← hκ.2] at hXa
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hXa
    refine ⟨⟨y, mem_lieKernel_of_comp κ y ?_⟩, hy⟩
    rw [hy]
    exact X.property
  intro T g hg
  rw [← hj.2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ a.unipotent.carrier T := by
    rw [← hκ.2, htop]
    exact Subgroup.mem_top _
  rw [hcomap, SubgroupFunctor.mem_comap] at hx
  exact hx

/-- Every admissible positive semigroup generator lies in the Dynamic functor. -/
theorem positive_generator_le_dynamicUnipotent
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G}
    (hF : IsSemigroupGenerator (AutomorphicAction.conjugation i) (positiveSemigroup ν) F) :
    F ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) :=
  le_dynamicUnipotent_of_tangentSubmodule_le G S hS i ν hF.1 hF.2.1
    ((hF.1.actionWeightSupport_subset_iff_tangentSubmodule_le
      (AutomorphicAction.conjugation i) hS hF.2.1 (positiveSemigroup ν)).mp hF.2.2)

/-- The actual morphism to the affine Dynamic unipotent representative induced by
a positive tangent bound on a represented smooth connected stable subgroup. -/
def dynamicUnipotentFactorOfTangent
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    H ⟶ Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom ν ≫ i) :=
  hj.homOfLe (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (le_dynamicUnipotent_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

/-- The factorization preserves the original inclusion into the ambient group. -/
theorem dynamicUnipotentFactorOfTangent_comp
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    dynamicUnipotentFactorOfTangent G S hS i ν hF hstable hLie hj ≫
      Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom ν ≫ i) = j :=
  hj.homOfLe_comp (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    (le_dynamicUnipotent_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

end Langlands.GroupScheme.RelativeRoot

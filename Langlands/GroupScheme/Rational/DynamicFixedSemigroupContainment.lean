import Langlands.GroupScheme.Dynamic.ActionAffineRepresentability
import Langlands.GroupScheme.Dynamic.ActionConjugation
import Langlands.GroupScheme.Dynamic.ActionFunctoriality
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.CocharacterWeightSums
import Langlands.GroupScheme.Rational.SemigroupWeightSupport
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness
import Langlands.GroupScheme.Lie.SubgroupEqualityProof

import Langlands.GroupScheme.Dynamic.ActionLieContainment

/-! # Nonnegative and zero tangent containment in actual Dynamic functors -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

local instance dynamicFixedSemigroupAmbient_isAffine {k : Type u} [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom] :
    IsAffine G.X.left :=
  isAffine_of_isAffineHom G.X.hom

set_option backward.isDefEq.respectTransparency false

/-- A smooth connected invariant closed subgroup with tangent image in the
nonnegative pairing span lies in the actual parabolic Dynamic functor. -/
theorem le_dynamicParabolic_of_tangentSubmodule_le
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν)) :
    F ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) := by
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
  have hcomap : a.parabolic = (Dynamic.parabolic χ).comap j := by
    simpa only [AutomorphicAction.cocharacterAction_parabolic] using
      heq.parabolic_eq_comap_of_isClosedSubgroup hc
  have htop : a.parabolic = ⊤ := by
    apply a.parabolic_eq_top_of_lieKernel
    intro X
    have hXF : (Lie.targetMap j k X).val ∈ F.carrier _ := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    have hXW := hLie hXF
    rw [semigroupWeightSpan_conjugation_nonnegative hS i ν] at hXW
    have hXD : (Lie.targetMap j k X).val ∈ (Dynamic.parabolic χ).carrier _ :=
      ((dynamicLie k G χ (Lie.targetMap j k X)).2.1).mpr hXW
    rw [hcomap, SubgroupFunctor.mem_comap]
    exact hXD
  intro T g hg
  rw [← hj.2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ a.parabolic.carrier T := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hcomap, SubgroupFunctor.mem_comap] at hx
  exact hx

/-- Every admissible nonnegative semigroup generator lies in the Dynamic functor. -/
theorem nonnegative_generator_le_dynamicParabolic
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G}
    (hF : IsSemigroupGenerator (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν) F) :
    F ≤ Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) :=
  le_dynamicParabolic_of_tangentSubmodule_le G S hS i ν hF.1 hF.2.1
    ((hF.1.actionWeightSupport_subset_iff_tangentSubmodule_le
      (AutomorphicAction.conjugation i) hS hF.2.1 (nonnegativeSemigroup ν)).mp hF.2.2)

/-- The actual morphism to the affine Dynamic parabolic representative induced by
a nonnegative tangent bound on a represented smooth connected stable subgroup. -/
def dynamicParabolicFactorOfTangent
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    H ⟶ Dynamic.Affine.parabolicScheme (CommGroupScheme.groupHom ν ≫ i) :=
  hj.homOfLe (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (le_dynamicParabolic_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

/-- The factorization preserves the original inclusion into the ambient group. -/
theorem dynamicParabolicFactorOfTangent_comp
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    dynamicParabolicFactorOfTangent G S hS i ν hF hstable hLie hj ≫
      Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i) = j :=
  hj.homOfLe_comp (Dynamic.Affine.isRepresentedBy_parabolicHom _)
    (le_dynamicParabolic_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

/-- A smooth connected invariant closed subgroup with tangent image in the
zero pairing span lies in the actual centralizer Dynamic functor. -/
theorem le_dynamicCentralizer_of_tangentSubmodule_le
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν)) :
    F ≤ Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) := by
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
  have hcomap : a.centralizer = (Dynamic.centralizer χ).comap j := by
    simpa only [AutomorphicAction.cocharacterAction_centralizer] using
      heq.centralizer_eq_comap_of_isClosedSubgroup hc
  have htop : a.centralizer = ⊤ := by
    apply a.centralizer_eq_top_of_lieKernel
    intro X
    have hXF : (Lie.targetMap j k X).val ∈ F.carrier _ := by
      rw [← hj.2]
      exact SubgroupFunctor.mem_range.mpr ⟨X.val, rfl⟩
    have hXW := hLie hXF
    rw [semigroupWeightSpan_conjugation_zero hS i ν] at hXW
    have hXD : (Lie.targetMap j k X).val ∈ (Dynamic.centralizer χ).carrier _ :=
      ((dynamicLie k G χ (Lie.targetMap j k X)).1).mpr hXW
    rw [hcomap, SubgroupFunctor.mem_comap]
    exact hXD
  intro T g hg
  rw [← hj.2] at hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  have hx : x ∈ a.centralizer.carrier T := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [hcomap, SubgroupFunctor.mem_comap] at hx
  exact hx

/-- Every admissible zero semigroup generator lies in the Dynamic functor. -/
theorem zero_generator_le_dynamicCentralizer
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G}
    (hF : IsSemigroupGenerator (AutomorphicAction.conjugation i) (zeroSemigroup ν) F) :
    F ≤ Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) :=
  le_dynamicCentralizer_of_tangentSubmodule_le G S hS i ν hF.1 hF.2.1
    ((hF.1.actionWeightSupport_subset_iff_tangentSubmodule_le
      (AutomorphicAction.conjugation i) hS hF.2.1 (zeroSemigroup ν)).mp hF.2.2)

/-- The actual morphism to the affine Dynamic centralizer representative induced by
a zero tangent bound on a represented smooth connected stable subgroup. -/
def dynamicCentralizerFactorOfTangent
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    H ⟶ Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom ν ≫ i) :=
  hj.homOfLe (Dynamic.Affine.isRepresentedBy_centralizerHom _)
    (le_dynamicCentralizer_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

/-- The factorization preserves the original inclusion into the ambient group. -/
theorem dynamicCentralizerFactorOfTangent_comp
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hstable : (AutomorphicAction.conjugation i).IsStable F)
    (hLie : tangentSubmodule F ≤
      semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν))
    {H : GroupScheme (Spec (CommRingCat.of k))} {j : H ⟶ G}
    (hj : F.IsRepresentedBy j) :
    dynamicCentralizerFactorOfTangent G S hS i ν hF hstable hLie hj ≫
      Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom ν ≫ i) = j :=
  hj.homOfLe_comp (Dynamic.Affine.isRepresentedBy_centralizerHom _)
    (le_dynamicCentralizer_of_tangentSubmodule_le G S hS i ν hF hstable hLie)

end Langlands.GroupScheme.RelativeRoot

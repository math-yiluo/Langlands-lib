import Langlands.GroupScheme.Rational.RootConeTorusLift
import Langlands.GroupScheme.Rational.RootConeGroupIntersection
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Supplied cone-root groups after field extension and torus enlargement -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The generation predicate depends only on the represented subgroup functor. -/
theorem IsRootSubsetGroup.of_range_eq
    {i : S.toGrp ⟶ G} {X : Set (characterLattice S)}
    {H Q : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G} {q : Q ⟶ G}
    (hq : IsRootSubsetGroup i X q) (hc : IsClosedSubgroup h)
    (hr : SubgroupFunctor.range h = SubgroupFunctor.range q) :
    IsRootSubsetGroup i X h := by
  refine ⟨hc, ?_⟩
  simpa only [hr] using hq.2

/-- A closed representative of the cone semigroup group is the full-root
cone-slice group for a maximal split torus. -/
theorem isRootSubsetGroup_of_range_eq_rootConeSemigroupGroup
    [IsAffineHom G.X.hom] (i : S.toGrp ⟶ G)
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (C : PointedCone ℝ (RealTorusSpace.Vstar S))
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}
    (hc : IsClosedSubgroup h)
    (hr : SubgroupFunctor.range h =
      RelativeRoot.semigroupSubgroup (AutomorphicAction.conjugation i)
        (rootConeSemigroup C)) :
    IsRootSubsetGroup i {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h := by
  obtain ⟨Q, q, hq, _, _, _⟩ :=
    exists_smooth_rootSubsetGroup i {a | a ∈ relativeRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} hG hi
      (fun _ ha => ha.1)
  exact hq.of_range_eq hc
    (hr.trans (hq.range_eq_rootConeSemigroupGroup i hG hi C).symm)

/-- Over a separably closed field, a split subtorus factors through a split
maximal torus of an affine group locally of finite type. -/
theorem exists_splitMaximalTorus_extension_of_isSepClosed
    [IsSepClosed k] [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (i : S.toGrp ⟶ G) (hi : IsSplitSubtorus i) :
    ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
      IsMaximalSplitTorus j ∧ IsMaximalTorus j ∧
        ∃ f : S ⟶ T, CommGroupScheme.groupHom f ≫ j = i := by
  obtain ⟨T, j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i hi.1.isTorus hi.2
  have hT := SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T.toGrp hj.1
  exact ⟨T, j, hj.isMaximalSplitTorus hT, hj, Additive.ofMul f, hf⟩

section FieldExtension

variable {K : Type u} [Field K] [Algebra k K]
    [IsAffineHom G.X.hom]
    (i : S.toGrp ⟶ G) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (C : PointedCone ℝ (RealTorusSpace.Vstar S))
    {H : GroupScheme (Spec (CommRingCat.of k))} {h : H ⟶ G}

include hG hi

/-- After field extension and a chosen larger maximal split torus, the supplied
indivisible-root cone group is the full-root group cut out by the pulled-back cone. -/
theorem IsRootSubsetGroup.baseChange_lift_rootCone
    (hh : IsRootSubsetGroup i
      {a | a ∈ RelativeRoot.indivisibleRoots i ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈ C} h)
    (hGK : IsConnectedReductive
      ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    {T : CommGroupScheme (Spec (CommRingCat.of K))}
    (j : T.toGrp ⟶ (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (hj : IsMaximalSplitTorus j)
    (f : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ j =
      (GroupScheme.baseChange (algebraBaseMap k K)).map i) :
    IsRootSubsetGroup j
      {a | a ∈ relativeRoots j ∧ (1 : ℝ) ⊗ₜ[ℤ] a ∈
        rootConePreimage f (rootConeBaseChange (algebraBaseMap k K) hi.1.1 C)}
      ((GroupScheme.baseChange (algebraBaseMap k K)).map h) := by
  let b := algebraBaseMap k K
  let : Smooth G.X.hom := hG.smooth
  let : LocallyOfFiniteType G.X.hom := inferInstance
  let : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
    hGK.isAffineHom
  let : Smooth ((GroupScheme.baseChange b).obj G).X.hom := hGK.smooth
  apply isRootSubsetGroup_of_range_eq_rootConeSemigroupGroup j hGK hj _
    (hh.1.baseChange b)
  rw [SubgroupFunctor.range_baseChangeHom,
    hh.range_eq_rootConeSemigroupGroup_of_indivisible i hG hi C,
    rootConeSemigroupGroup_baseChange hi.1.1 i C]
  rw [rootConeSemigroup_preimage, ← RelativeRoot.semigroupSubgroup_comp_torusHom
    (hi.1.1.baseChange b) hj.1.1 f j, hf]

end FieldExtension

end Langlands.GroupScheme

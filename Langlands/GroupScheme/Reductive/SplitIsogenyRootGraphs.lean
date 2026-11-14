import Langlands.GroupScheme.Reductive.SplitIsogenyGraph
import Langlands.GroupScheme.Rational.RootSubgroupPositive

/-! # Source root subgroups in graphs of local isogenies -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

variable {k : Type u} [Field k]
    {G G' : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {t : T ⟶ T'}

namespace LocalIsogeny

variable {ν : cocharacterLattice T} {ν' : cocharacterLattice T'}
    (C : LocalIsogeny i i' t ν ν') (α : characterLattice T)

/-- An actual smooth connected closed representative of a source root subgroup
inside a chosen source centralizer. -/
structure SourceRoot where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ C.left
  rep : (RelativeRoot.subgroup C.leftTorus α).IsRepresentedBy inclusion
  closed : IsClosedSubgroup inclusion
  smooth : Smooth group.X.hom
  connected : ConnectedSpace group.X.left

/-- Construct the source root representative from the intrinsic root functor. -/
def sourceRoot [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0) : C.SourceRoot α := by
  apply Classical.choice
  obtain ⟨U, j, hj, hjc, hjs, hjconn⟩ :=
    RelativeRoot.subgroup_isSmoothConnectedClosed_of_ne_zero hT C.leftTorus α hα
  exact ⟨⟨U, j, hj, hjc, hjs, hjconn⟩⟩

namespace SourceRoot

variable {C α} (R : C.SourceRoot α)

/-- A source root annihilating the centralizer direction represents the full
ambient source root subgroup. -/
theorem ambientRep (hT : IsSplitTorus T.toGrp) (hα : α ≠ 0)
    (hαν : latticePairing T α ν = 0) :
    (RelativeRoot.subgroup i α).IsRepresentedBy
      (R.inclusion ≫ C.leftInclusion) := by
  rw [← LeviGluing.root_map_centralizer i ν C.leftInclusion C.leftRep C.leftClosed
    C.leftTorus C.leftTorusComp hT α hα hαν]
  exact R.rep.comp C.leftRep

end SourceRoot
end LocalIsogeny

namespace LocalIsogenyGraphEnvelope

variable {I : Type v} {ν : I → cocharacterLattice T}
    {ν' : I → cocharacterLattice T'}
    {C : ∀ j, LocalIsogeny i i' t (ν j) (ν' j)}
    (D : LocalIsogenyGraphEnvelope C)

/-- Lift a source root representative through its actual local graph. -/
def rootLift (j : I) {α : characterLattice T} (R : (C j).SourceRoot α) :
    R.group ⟶ D.group :=
  R.inclusion ≫ D.localLift j

@[reassoc (attr := simp)]
theorem rootLift_first (j : I) {α : characterLattice T} (R : (C j).SourceRoot α) :
    D.rootLift j R ≫ D.first = R.inclusion ≫ (C j).leftInclusion := by
  rw [rootLift, Category.assoc, D.localLift_first]

@[reassoc (attr := simp)]
theorem rootLift_second (j : I) {α : characterLattice T} (R : (C j).SourceRoot α) :
    D.rootLift j R ≫ D.second =
      R.inclusion ≫ (C j).hom ≫ (C j).rightInclusion := by
  rw [rootLift, Category.assoc, D.localLift_second]

theorem rootLift_closed [IsAffineHom G'.X.hom] (j : I) {α : characterLattice T}
    (R : (C j).SourceRoot α) : IsClosedSubgroup (D.rootLift j R) :=
  IsClosedSubgroup.comp R.closed (D.localLift_closed j (C j).leftClosed)

theorem rootLift_first_rep (hT : IsSplitTorus T.toGrp) (j : I)
    {α : characterLattice T} (R : (C j).SourceRoot α) (hα : α ≠ 0)
    (hαν : latticePairing T α (ν j) = 0) :
    (RelativeRoot.subgroup i α).IsRepresentedBy (D.rootLift j R ≫ D.first) := by
  rw [rootLift_first]
  exact R.ambientRep hT hα hαν

/-- The source torus acts on the root representative in its source centralizer. -/
def rootTorusAction (j : I) {α : characterLattice T} (R : (C j).SourceRoot α) :
    AutomorphicAction T.toGrp R.group :=
  RelativeRoot.subgroupAction (C j).leftTorus α R.inclusion R.rep

theorem rootTorusAction_act_comp (j : I) {α : characterLattice T}
    (R : (C j).SourceRoot α) {W : Over (Spec (CommRingCat.of k))}
    (s : W ⟶ T.X) (g : W ⟶ R.group.X) :
    (rootTorusAction j R).act s g ≫ (D.rootLift j R).hom.hom =
      (s ≫ D.torusLift.hom.hom) * (g ≫ (D.rootLift j R).hom.hom) *
        (s ≫ D.torusLift.hom.hom)⁻¹ := by
  have h := congrArg (· ≫ (D.localLift j).hom.hom)
    (RelativeRoot.subgroupAction_act_comp (C j).leftTorus α R.inclusion R.rep s g)
  simp only [Category.assoc, MonObj.mul_comp, GrpObj.inv_comp] at h
  simp only [rootTorusAction, rootLift, Grp.comp_hom_hom, ← D.leftTorus_localLift j]
  exact h

theorem range_rootLift_isNormalizedBy (j : I) {α : characterLattice T}
    (R : (C j).SourceRoot α) :
    (SubgroupFunctor.range (D.rootLift j R)).IsNormalizedBy
      (SubgroupFunctor.range D.torusLift) := by
  intro W g x hg hx
  obtain ⟨s, rfl⟩ := SubgroupFunctor.mem_range.mp hg
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr
    ⟨(rootTorusAction j R).act s y, D.rootTorusAction_act_comp j R s y⟩

/-- A lifted source root lies in the intrinsic graph root functor for the
distinguished source torus. -/
theorem range_rootLift_le (j : I) {α : characterLattice T}
    (R : (C j).SourceRoot α) :
    SubgroupFunctor.range (D.rootLift j R) ≤ RelativeRoot.subgroup D.torusLift α := by
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  have hy : y ≫ R.inclusion.hom.hom ∈
      (RelativeRoot.subgroup (C j).leftTorus α).carrier W := by
    rw [← R.rep.2]
    exact SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩
  have h := RelativeRoot.comp_mem_subgroup (C j).leftTorus α (D.localLift j) hy
  rw [D.leftTorus_localLift j] at h
  simpa only [rootLift, Grp.comp_hom_hom, Category.assoc] using h

end LocalIsogenyGraphEnvelope

end Langlands.GroupScheme.RootDatumIsogenyRealization

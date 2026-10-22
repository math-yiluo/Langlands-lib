import Langlands.Cohomology.Continuous.FiniteQuotientComparison
import Langlands.Cohomology.Continuous.SubgroupFiniteStages

universe u

open CategoryTheory

namespace Langlands.Continuous

variable {k G : Type u} [CommRing k] [TopologicalSpace k]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
theorem restrictOpenNormal_le (H : OpenSubgroup G) {M N : OpenNormalSubgroup G}
    (h : M ≤ N) : restrictOpenNormal H M ≤ restrictOpenNormal H N := by
  intro x hx
  exact h hx

/-- Restriction of fixed coefficients to the subgroup's quotient. -/
noncomputable def fixedSubgroupRestriction (A : Rep.{u} k G) (H N : Subgroup G) [N.Normal] :
    Rep.res (quotientSubgroupMap H N) (A.quotientToInvariants N) ⟶
      (Rep.res H.subtype A).quotientToInvariants (N.comap H.subtype) :=
  Rep.ofHom
    { toLinearMap :=
        { toFun x := ⟨x.1, fun n => x.2 ⟨n.1.1, n.2⟩⟩
          map_add' _ _ := Subtype.ext rfl
          map_smul' _ _ := Subtype.ext rfl }
      isIntertwining' q := by
        refine QuotientGroup.induction_on q (fun g => ?_)
        ext x
        rfl }

/-- Restriction at a genuine finite ordinary-cohomology stage. -/
noncomputable def finiteRestrictionCochains (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) :
    groupCohomology.inhomogeneousCochains (finiteQuotientRep A.toRep N) ⟶
      groupCohomology.inhomogeneousCochains
        (finiteQuotientRep (A.restrict H.toSubgroup).toRep (restrictOpenNormal H N)) :=
  groupCohomology.cochainsMap (quotientSubgroupMap H.toSubgroup N.toSubgroup)
    (fixedSubgroupRestriction A.toRep H.toSubgroup N.toSubgroup)

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalGroup G] in
theorem finiteRestrictionCochains_refinement (A : DiscreteModule k G)
    (H : OpenSubgroup G) {M N : OpenNormalSubgroup G} (h : M ≤ N) :
    finiteRestrictionCochains A H N ≫
        groupCohomology.cochainsMap
          (quotientTransition (M := restrictOpenNormal H M) (N := restrictOpenNormal H N)
            (restrictOpenNormal_le H h))
          (fixedTransition (A.restrict H.toSubgroup).toRep (restrictOpenNormal_le H h)) =
      groupCohomology.cochainsMap (quotientTransition h) (fixedTransition A.toRep h) ≫
        finiteRestrictionCochains A H M := by
  unfold finiteRestrictionCochains
  rw [← groupCohomology.cochainsMap_comp, ← groupCohomology.cochainsMap_comp]
  apply groupCohomology.cochainsMap_congr
  · ext g
    rfl
  · rfl

/-- The underlying cochain map of the existing continuous restriction. -/
noncomputable def continuousRestrictionCochains (A : DiscreteModule k G) (H : Subgroup G) :
    underlyingContinuousCochains A.toTopRep ⟶
      underlyingContinuousCochains (A.restrict H).toTopRep :=
  ((forget₂ (TopModuleCat.{u} k) (ModuleCat.{u} k)).mapHomologicalComplex
    (ComplexShape.up ℕ)).map
      (ContinuousCohomology.cochainsMap (subgroupInclusion H) (𝟙 (A.restrict H).toTopRep))

/-- Restriction between the actual ordinary cohomology groups of finite quotients. -/
noncomputable def finiteRestriction (A : DiscreteModule k G)
    (H : OpenSubgroup G) (N : OpenNormalSubgroup G) (q : ℕ) :
    groupCohomology (finiteQuotientRep A.toRep N) q ⟶
      groupCohomology
        (finiteQuotientRep (A.restrict H.toSubgroup).toRep (restrictOpenNormal H N)) q :=
  HomologicalComplex.homologyMap (finiteRestrictionCochains A H N) q

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalGroup G] in
theorem finiteRestriction_refinement (A : DiscreteModule k G)
    (H : OpenSubgroup G) {M N : OpenNormalSubgroup G} (h : M ≤ N) (q : ℕ) :
    finiteRestriction A H N q ≫
        finiteInflation (A.restrict H.toSubgroup).toRep q
          (M := restrictOpenNormal H M) (N := restrictOpenNormal H N) (restrictOpenNormal_le H h) =
      finiteInflation A.toRep q h ≫ finiteRestriction A H M q := by
  unfold finiteRestriction finiteInflation groupCohomology.map
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    finiteRestrictionCochains_refinement]

set_option backward.isDefEq.respectTransparency false in
omit [TopologicalSpace k] [IsTopologicalGroup G] in
theorem finiteStageToColimit_refinement (A : Rep.{u} k G)
    {M N : OpenNormalSubgroup G} (h : M ≤ N) (q : ℕ) :
    finiteInflation A q h ≫ finiteStageToColimit A M q = finiteStageToColimit A N q :=
  Limits.colimit.w (finiteQuotientDiagram A q)
    (homOfLE (show OrderDual.toDual N ≤ OrderDual.toDual M from h))

set_option backward.isDefEq.respectTransparency false in
/-- The actual finite-quotient restriction cocone, before comparison with continuous cohomology. -/
noncomputable def finiteRestrictionCocone (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) : Limits.Cocone (finiteQuotientDiagram A.toRep q) where
  pt := finiteQuotientCohomology (A.restrict H.toSubgroup).toRep q
  ι :=
    { app := fun N => finiteRestriction A H (OrderDual.ofDual N) q ≫
        finiteStageToColimit (A.restrict H.toSubgroup).toRep
          (restrictOpenNormal H (OrderDual.ofDual N)) q
      naturality := fun N M f => by
        change finiteInflation A.toRep q
            (M := OrderDual.ofDual M) (N := OrderDual.ofDual N)
              (leOfHom (X := FiniteQuotientIndex (G := G)) f) ≫
            (finiteRestriction A H (OrderDual.ofDual M) q ≫
              finiteStageToColimit (A.restrict H.toSubgroup).toRep
                (restrictOpenNormal H (OrderDual.ofDual M)) q) = _
        rw [← Category.assoc, ← finiteRestriction_refinement, Category.assoc,
          finiteStageToColimit_refinement]
        simp only [Functor.const_obj_map]
        exact (Category.comp_id _).symm }

/-- Restriction on the actual directed colimit, defined intrinsically from finite-stage restriction. -/
noncomputable def finiteQuotientRestriction (A : DiscreteModule k G)
    (H : OpenSubgroup G) (q : ℕ) :
    finiteQuotientCohomology A.toRep q ⟶
      finiteQuotientCohomology (A.restrict H.toSubgroup).toRep q :=
  Limits.colimit.desc _ (finiteRestrictionCocone A H q)

end Langlands.Continuous

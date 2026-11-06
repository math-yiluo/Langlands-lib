import Langlands.GroupScheme.HomScheme.RelativeGraphRecovery
import Langlands.GroupScheme.HomScheme.SubgroupFamilyEvaluation
import Langlands.GroupScheme.Torus.IsomorphismLocusEtale
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityStatement
import Langlands.GroupScheme.HomScheme.SmoothSplitSourceRepresentabilityStatement
import Langlands.GroupScheme.Torus.SplitReductiveProof

/-! # Universal Hom families from the open graph locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}
variable {K : GroupScheme M.left}

/-- The open parameter scheme where the subgroup family's first projection
is invertible. -/
def graphLocus (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) : Over S :=
  Over.mk ((TorusIsomorphismLocus.opens
    (j ≫ (baseChange M.hom).map (fst H G))).ι ≫ M.hom)

/-- The actual open inclusion of graph parameters into subgroup parameters. -/
def graphLocusMap (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) :
    graphLocus j ⟶ M :=
  Over.homMk (TorusIsomorphismLocus.opens
    (j ≫ (baseChange M.hom).map (fst H G))).ι rfl

instance (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) :
    Mono (graphLocusMap j) := by
  have : Mono (graphLocusMap j).left := by
    change Mono (TorusIsomorphismLocus.opens
      (j ≫ (baseChange M.hom).map (fst H G))).ι
    infer_instance
  exact Over.mono_of_mono_left _

/-- Invertibility of an evaluated first projection is precisely invertibility
of the pulled-back original first projection. -/
theorem isIso_familyHom_fst_iff
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) (a : T ⟶ M) :
    IsIso (TorusSubgroupModuli.familyHom j a ≫
      (baseChange T.hom).map (fst H G)) ↔
      IsIso ((baseChange a.left).map
        (j ≫ (baseChange M.hom).map (fst H G))) := by
  rw [familyHom_fst]
  exact isIso_comp_right_iff _ _

instance graphLocus_firstProjection_isIso
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) :
    IsIso (TorusSubgroupModuli.familyHom j (graphLocusMap j) ≫
      (baseChange (graphLocus j).hom).map (fst H G)) := by
  apply (isIso_familyHom_fst_iff j (graphLocusMap j)).mpr
  apply TorusIsomorphismLocus.isIso_of_range_subset_opens
  change Set.range (TorusIsomorphismLocus.opens
    (j ≫ (baseChange M.hom).map (fst H G))).ι ⊆ _
  simp only [Scheme.Opens.range_ι]
  exact Set.Subset.rfl

/-- Recover the actual Hom family on the open graph locus. -/
def graphLocusHom (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) :
    RelativeHom H G (graphLocus j) :=
  homOfRelativeGraphRepresentative
    (TorusSubgroupModuli.familyHom j (graphLocusMap j))

/-- Evaluating the recovered Hom family and then taking its graph gives the
original subgroup family at the composite parameter. -/
theorem evaluate_graphLocusHom
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) (a : T ⟶ graphLocus j) :
    TorusSubgroupModuli.evaluate j (a ≫ graphLocusMap j) =
      relativeGraph (evaluate a (graphLocusHom j)) := by
  rw [← TorusSubgroupModuli.evaluate_comp]
  exact evaluate_eq_relativeGraph_evaluate_homOfRepresentative _ a

/-- The graph locus in a smooth parameter scheme is smooth over the base. -/
theorem smooth_graphLocus
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G)) [Smooth M.hom] :
    Smooth (graphLocus j).hom := by
  change Smooth ((TorusIsomorphismLocus.opens
    (j ≫ (baseChange M.hom).map (fst H G))).ι ≫ M.hom)
  infer_instance

/-- Restricting an actual universal closed torus-subgroup family to its open
graph locus gives an actual universal Hom family. -/
theorem isUniversal_graphLocusHom [IsSeparated G.X.hom]
    (hH : IsSplitTorus H)
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) :
    IsUniversal (graphLocusHom j) := by
  intro T
  constructor
  · intro a b hab
    obtain ⟨c, hc, hu⟩ := huni T
      (relativeGraph (evaluate a (graphLocusHom j)))
      (isAdmissible_relativeGraph hH _)
    have ha : a ≫ graphLocusMap j = c :=
      hu _ (evaluate_graphLocusHom j a)
    have hb : b ≫ graphLocusMap j = c := by
      apply hu
      rw [evaluate_graphLocusHom]
      exact congrArg relativeGraph hab.symm
    exact (cancel_mono (graphLocusMap j)).mp (ha.trans hb.symm)
  · intro f
    obtain ⟨c, hc, _⟩ := huni T (relativeGraph f)
      (isAdmissible_relativeGraph hH f)
    let : IsClosedImmersion (TorusSubgroupModuli.familyHom j c).hom.hom.left :=
      TorusSubgroupModuli.isClosedSubgroup_familyHom j hj c
    let : Mono (TorusSubgroupModuli.familyHom j c).hom.hom :=
      Over.mono_of_mono_left _
    have hi : IsIso (TorusSubgroupModuli.familyHom j c ≫
        (baseChange T.hom).map (fst H G)) :=
      isIso_firstProjection_of_range_eq_relativeGraph _ f hc
    have hp := (isIso_familyHom_fst_iff j c).mp hi
    obtain ⟨a, ha⟩ :=
      (TorusIsomorphismLocus.isIso_baseChange_iff_factors_of_relative_split
        hK (hH.baseChange M.hom)
        (j ≫ (baseChange M.hom).map (fst H G)) c.left).mp hp
    let a' : T ⟶ graphLocus j := Over.homMk a (by
      change a ≫ ((TorusIsomorphismLocus.opens
        (j ≫ (baseChange M.hom).map (fst H G))).ι ≫ M.hom) = T.hom
      rw [← Category.assoc, ha]
      exact Over.w c)
    have hfac : a' ≫ graphLocusMap j = c := by
      apply Over.OverMorphism.ext
      exact ha
    refine ⟨a', relativeGraph_injective ?_⟩
    rw [← evaluate_graphLocusHom, hfac, hc]

/-- A smooth universal subgroup family in the product supplies smooth actual
Hom representability. Existence of that subgroup family is an explicit premise. -/
theorem exists_smooth_universal_of_torusSubgroupFamily [IsSeparated G.X.hom]
    (hH : IsSplitTorus H)
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) [Smooth M.hom] :
    ∃ (N : Over S) (i : RelativeHom H G N), IsUniversal i ∧ Smooth N.hom :=
  ⟨graphLocus j, graphLocusHom j, isUniversal_graphLocusHom hH j hj hK huni,
    smooth_graphLocus j⟩

/-- Conditional assembly of the exact smooth Hom target from the independent
smooth closed-torus-subgroup moduli proposition. -/
theorem smoothSplitSourceRepresentability_of_torusSubgroupModuli
    (hmod : TorusSubgroupModuli.SmoothTorusSubgroupRepresentabilityStatement.{u}) :
    SmoothSplitSourceRepresentabilityStatement.{u} := by
  intro S H G _ _ hH
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth (H ⊗ G).X.hom := smooth_tensor H.X G.X inferInstance inferInstance
  let : IsAffineHom (H ⊗ G).X.hom := by
    change IsAffineHom (pullback.fst H.X.hom G.X.hom ≫ H.X.hom)
    let : IsAffineHom (pullback.fst H.X.hom G.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom G.X.hom)
    infer_instance
  obtain ⟨M, K, j, hj, hK, huni, hM⟩ := hmod S (H ⊗ G)
  let := hM
  exact exists_smooth_universal_of_torusSubgroupFamily hH j hj hK huni

end Langlands.GroupScheme.HomScheme

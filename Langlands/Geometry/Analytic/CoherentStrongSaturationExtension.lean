import Langlands.Geometry.Analytic.CoherentStrongLocalDomain
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # Actual strong extension to both enlarged affinoid atlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A containing target for the original parent gives an actual enlarged
original-chart target for each new source chart. -/
theorem saturated_target_exists (f : StrongHom A B) (S : A.atlas.localDomainFamily) :
    ∃ T : B.atlas.localDomainFamily,
      f.baseMap '' Set.range (A.atlas.saturatedChart S) ⊆
        Set.range (B.atlas.saturatedChart T) := by
  let U := A.atlas.saturatedRepresentative S
  refine ⟨B.atlas.originalSaturatedIndex (f.chosenTargetIndex U.index), ?_⟩
  rw [B.atlas.range_saturatedChart]
  exact (Set.image_mono U.range_ambientMap.subset).trans
    (f.localDomain_chosenTarget_admissible U)

/-- Extend the actual original bounded maps to every admissible pair of full
local domains in the two constructed enlarged atlases. The sole extra law is
intrinsic coefficient-test coherence of the original supplied family. -/
def saturationExtension (f : StrongHom A B) (hf : f.HasCoherentPullbacks) :
    StrongHom A.saturatedPresentation B.saturatedPresentation where
  baseMap := f.baseMap
  target_exists := f.saturated_target_exists
  pullback S T h := f.localDomainPullback
    (A.atlas.saturatedRepresentative S) (B.atlas.saturatedRepresentative T) (by
      rw [← (A.atlas.saturatedRepresentative S).range_ambientMap,
        ← (B.atlas.saturatedRepresentative T).range_ambientMap]
      exact h)
  chart_comm S T h x := f.localDomainPullback_ambient
    (A.atlas.saturatedRepresentative S) (B.atlas.saturatedRepresentative T) _ x
  restriction_comm S S' T T' hS hT h h' :=
    f.localDomainPullback_naturality hf
      (A.atlas.saturatedInclusion S S' hS) (B.atlas.saturatedInclusion T T' hT) _ _

@[simp]
theorem saturationExtension_baseMap (f : StrongHom A B) (hf : f.HasCoherentPullbacks) :
    (f.saturationExtension hf).baseMap = f.baseMap := rfl

/-- On the literal whole original local domains the construction recovers
every original admissible bounded map. -/
theorem localDomainPullback_original (f : StrongHom A B) (hf : f.HasCoherentPullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.localDomainPullback (A.atlas.originalLocalDomain i) (B.atlas.originalLocalDomain j)
      (by rw [A.atlas.originalLocalDomain_locus, B.atlas.originalLocalDomain_locus]; exact h) =
        f.pullback i j h := by
  have heq := (f.localDomainPullback_comp_baseMap
    (A.atlas.originalLocalDomain i) (B.atlas.originalLocalDomain j)
    (by rw [A.atlas.originalLocalDomain_locus, B.atlas.originalLocalDomain_locus]; exact h)).trans
      (f.localChartPullback_of_parent_admissible hf (A.atlas.originalLocalDomain i) j h _)
  change (f.localDomainPullback (A.atlas.originalLocalDomain i)
      (B.atlas.originalLocalDomain j) _).comp (BoundedAlgHom.id K (B.atlas.algebra j)) =
    (BoundedAlgHom.id K (A.atlas.algebra i)).comp (f.pullback i j h) at heq
  exact (BoundedAlgHom.comp_id _).symm.trans (heq.trans (BoundedAlgHom.id_comp _))

/-- Original admissibility is unchanged when the original domains are viewed
as members of the enlarged atlases. -/
theorem saturationExtension_original_admissible (f : StrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.baseMap '' Set.range (A.atlas.saturatedChart (A.atlas.originalSaturatedIndex i)) ⊆
      Set.range (B.atlas.saturatedChart (B.atlas.originalSaturatedIndex j)) := by
  rw [A.atlas.range_saturatedChart, B.atlas.range_saturatedChart]
  exact h

private theorem localDomainPullback_heq (f : StrongHom A B)
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (eU : U = U') (eV : V = V')
    (h : f.baseMap '' U.locus ⊆ V.locus) (h' : f.baseMap '' U'.locus ⊆ V'.locus) :
    HEq (f.localDomainPullback U V h) (f.localDomainPullback U' V' h') := by
  cases eU
  cases eV
  rfl

/-- The enlarged pullback at every original admissible pair is the unchanged
old bounded map. Heterogeneous equality records only the chosen algebra's
propositional identification with the original algebra. -/
theorem saturationExtension_pullback_original (f : StrongHom A B)
    (hf : f.HasCoherentPullbacks) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    HEq ((f.saturationExtension hf).pullback
      (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
      (f.saturationExtension_original_admissible i j h)) (f.pullback i j h) := by
  have hlocal : f.baseMap ''
      (A.atlas.saturatedRepresentative (A.atlas.originalSaturatedIndex i)).locus ⊆
      (B.atlas.saturatedRepresentative (B.atlas.originalSaturatedIndex j)).locus := by
    rw [A.atlas.saturatedRepresentative_locus, B.atlas.saturatedRepresentative_locus]
    exact h
  change HEq (f.localDomainPullback
    (A.atlas.saturatedRepresentative (A.atlas.originalSaturatedIndex i))
    (B.atlas.saturatedRepresentative (B.atlas.originalSaturatedIndex j)) hlocal) _
  exact (localDomainPullback_heq f (A.atlas.saturatedRepresentative_original i)
    (B.atlas.saturatedRepresentative_original j) hlocal
    (by
      change f.baseMap '' (A.atlas.originalLocalDomain i).locus ⊆
        (B.atlas.originalLocalDomain j).locus
      rw [A.atlas.originalLocalDomain_locus, B.atlas.originalLocalDomain_locus]
      exact h)).trans
      (heq_of_eq (f.localDomainPullback_original hf i j h))

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

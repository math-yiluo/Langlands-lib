import Langlands.Geometry.Analytic.OriginalDomainRefinement
import Langlands.Geometry.Analytic.OriginalDomainStrongRestriction

/-! # Actual domain presentations under locally refining subatlas selection -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

@[simp]
theorem coe_originalDomainSubatlasOrderIso (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (S : a.OriginalChartDomain) :
    (a.originalDomainSubatlasOrderIso P hP S : Set X) = S := rfl

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)
  (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P)

/-- Transport the domain subset to the selected atlas, then realize its
actual contained-chart presentation. -/
def originalDomainSubatlasFunctor : A.atlas.OriginalChartDomain ⥤
    AffinoidAtlasPresentation.{u, v, w} K :=
  (A.atlas.originalDomainSubatlasOrderIso P hP).equivalence.functor ⋙
    (A.subpresentation P hP).originalDomainFunctor

/-- The chosen comparison uses the same chart algebra and its bounded identity. -/
def originalDomainSubatlasMap (S : A.atlas.OriginalChartDomain) :
    (A.originalDomainSubatlasFunctor P hP).obj S ⟶ A.originalDomainPresentation S where
  baseMap := ContinuousMap.id S.carrier
  indexMap c := ⟨c.val.val, c.property⟩
  index_mono c d h := A.atlas.subspaceChart_subset S.carrier _ _
    ((A.atlas.subatlas P hP).chart_subset_of_subspaceSubset S.carrier c d h)
  pullback c := BoundedAlgHom.id K (A.atlas.algebra c.val.val)
  chart_comm _ _ := rfl
  restriction_comm _ _ _ := rfl

@[simp]
theorem originalDomainSubatlasMap_apply (S : A.atlas.OriginalChartDomain)
    (x : S.carrier) :
    (A.originalDomainSubatlasMap P hP S).baseMap x = x := rfl

@[simp]
theorem originalDomainSubatlasMap_pullback (S : A.atlas.OriginalChartDomain)
    (c : ((A.originalDomainSubatlasFunctor P hP).obj S).atlas.Index) :
    (A.originalDomainSubatlasMap P hP S).pullback c =
      BoundedAlgHom.id K (A.atlas.algebra c.val.val) := rfl

/-- Naturality compares the complete chosen arrows, including bounded maps. -/
theorem originalDomainSubatlasMap_naturality {S T : A.atlas.OriginalChartDomain}
    (hST : S ≤ T) :
    (A.originalDomainSubatlasFunctor P hP).map (homOfLE hST) ≫
        A.originalDomainSubatlasMap P hP T =
      A.originalDomainSubatlasMap P hP S ≫ A.originalDomainMap hST :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- A natural comparison of actual presentation-valued domain functors. -/
def originalDomainSubatlasComparison :
    A.originalDomainSubatlasFunctor P hP ⟶ A.originalDomainFunctor where
  app := A.originalDomainSubatlasMap P hP
  naturality _ _ f := A.originalDomainSubatlasMap_naturality P hP (leOfHom f)

/-- The domain comparison commutes with the actual ambient subatlas inclusion. -/
theorem originalDomainSubatlasMap_inclusion (S : A.atlas.OriginalChartDomain) :
    A.originalDomainSubatlasMap P hP S ≫ A.originalDomainInclusion S =
      (A.subpresentation P hP).originalDomainInclusion
          (A.atlas.originalDomainSubatlasOrderIso P hP S) ≫ A.subatlasInclusion P hP :=
  Hom.ext rfl rfl (heq_of_eq (funext fun _ => rfl))

/-- Each selected chart contained in S supplies its identical original chart
contained in S, so simultaneous domain restriction is available. -/
theorem strongSubatlasInclusion_mapsOriginalDomainCharts
    (S : A.atlas.OriginalChartDomain) :
    (A.strongSubatlasInclusion P hP).MapsOriginalDomainCharts
      (A.atlas.originalDomainSubatlasOrderIso P hP S) S := by
  intro c
  exact ⟨⟨c.val.val, c.property⟩, fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx⟩

/-- The full strong domain comparison retains all admissible bounded pullbacks. -/
def originalDomainStrongSubatlasMap (S : A.atlas.OriginalChartDomain) :
    StrongHom ((A.originalDomainSubatlasFunctor P hP).obj S)
      (A.originalDomainPresentation S) :=
  (A.strongSubatlasInclusion P hP).restrictDomains
    (A.atlas.originalDomainSubatlasOrderIso P hP S) S
    (A.strongSubatlasInclusion_mapsOriginalDomainCharts P hP S)

@[simp]
theorem originalDomainStrongSubatlasMap_apply (S : A.atlas.OriginalChartDomain)
    (x : S.carrier) :
    (A.originalDomainStrongSubatlasMap P hP S).baseMap x = x := rfl

@[simp]
theorem originalDomainStrongSubatlasMap_baseMap (S : A.atlas.OriginalChartDomain) :
    (A.originalDomainStrongSubatlasMap P hP S).baseMap =
      (A.originalDomainSubatlasMap P hP S).baseMap := rfl

/-- Every admissible bounded map is the corresponding original atlas restriction,
as an entire bounded algebra homomorphism. -/
theorem originalDomainStrongSubatlasMap_pullback (S : A.atlas.OriginalChartDomain)
    (c : ((A.originalDomainSubatlasFunctor P hP).obj S).atlas.Index)
    (d : A.atlas.SubspaceChart S.carrier)
    (hc : (A.originalDomainStrongSubatlasMap P hP S).baseMap ''
      Set.range (((A.originalDomainSubatlasFunctor P hP).obj S).atlas.chart c) ⊆
        Set.range ((A.originalDomainPresentation S).atlas.chart d)) :
    (A.originalDomainStrongSubatlasMap P hP S).pullback c d hc =
      A.atlas.restriction c.val.val d.val
        (fun x hx => ((A.strongSubatlasInclusion P hP).restrictDomainsBaseMap_admissible_iff
          (A.atlas.originalDomainSubatlasOrderIso P hP S) S
          (A.strongSubatlasInclusion_mapsOriginalDomainCharts P hP S) c d).mp hc
            ⟨x, hx, rfl⟩) := rfl

/-- At the selected identical target chart, the full map recovers the chosen
comparison's bounded identity. -/
theorem originalDomainStrongSubatlasMap_pullback_selected
    (S : A.atlas.OriginalChartDomain)
    (c : ((A.originalDomainSubatlasFunctor P hP).obj S).atlas.Index)
    (hc : (A.originalDomainStrongSubatlasMap P hP S).baseMap ''
      Set.range (((A.originalDomainSubatlasFunctor P hP).obj S).atlas.chart c) ⊆
        Set.range ((A.originalDomainPresentation S).atlas.chart
          ((A.originalDomainSubatlasMap P hP S).indexMap c))) :
    (A.originalDomainStrongSubatlasMap P hP S).pullback c
        ((A.originalDomainSubatlasMap P hP S).indexMap c) hc =
      (A.originalDomainSubatlasMap P hP S).pullback c :=
  A.atlas.restriction_id c.val.val _

/-- Local refinement of the ambient original charts gives a full strong
quasi-isomorphism on each actual original-chart domain. -/
theorem isQuasiIso_originalDomainStrongSubatlasMap (S : A.atlas.OriginalChartDomain) :
    (A.originalDomainStrongSubatlasMap P hP S).IsQuasiIso := by
  apply (A.isQuasiIso_strongSubatlasInclusion P hP).restrictDomains
    (A.atlas.originalDomainSubatlasOrderIso P hP S) S
    (A.strongSubatlasInclusion_mapsOriginalDomainCharts P hP S)
  exact Set.image_id S.carrier

end AffinoidAtlasPresentation

end Langlands.Analytic

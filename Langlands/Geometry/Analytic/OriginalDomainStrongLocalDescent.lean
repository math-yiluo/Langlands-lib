import Langlands.Geometry.Analytic.OriginalDomainStrongDescent
import Langlands.Geometry.Analytic.OriginalDomainStrongLocalization

/-! # Full strong-map descent inside an actual original-chart domain -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set CategoryTheory IndexedAffinoidAtlas.OriginalChartDomain

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {ι : Type z}

/-- Each original chart contained in `S` lies wholly in a member of `D`. -/
def OriginalDomainCoversChartsWithin (S : A.atlas.OriginalChartDomain)
    (D : ι → A.atlas.OriginalChartDomain) : Prop :=
  ∀ c : A.atlas.SubspaceChart S.carrier, ∃ k, ofChart c.val ≤ D k

/-- Whole-contained-chart coverage implies the full quasinet covering condition,
not just coverage of points. -/
theorem OriginalDomainCoversChartsWithin.ofArrows_mem
    {S : A.atlas.OriginalChartDomain} {D : ι → A.atlas.OriginalChartDomain}
    (hD : OriginalDomainCoversChartsWithin S D) (hDS : ∀ k, D k ≤ S) :
    Sieve.ofArrows D (fun k => homOfLE (hDS k)) ∈ quasinetTopology A.atlas S := by
  apply (quasinetTopology A.atlas).superset_covering ?_ (ofArrows_originalCharts_mem S)
  intro V f hf
  obtain ⟨c, g, _⟩ := (Sieve.mem_ofArrows_iff
    (fun c : A.atlas.SubspaceChart S.carrier => ofChart c.val)
    (fun c => homOfLE (show ofChart c.val ≤ S from c.property)) f).mp hf
  obtain ⟨k, hk⟩ := hD c
  exact (Sieve.mem_ofArrows_iff D (fun k => homOfLE (hDS k)) f).mpr
    ⟨k, g ≫ homOfLE hk, Subsingleton.elim _ _⟩

/-- The corresponding family on the actual subspace of `S` is a quasinet. -/
theorem OriginalDomainCoversChartsWithin.isQuasinet
    {S : A.atlas.OriginalChartDomain} {D : ι → A.atlas.OriginalChartDomain}
    (hD : OriginalDomainCoversChartsWithin S D) (hDS : ∀ k, D k ≤ S) :
    AtlasTopology.IsQuasinet
      (AtlasTopology.restrictedFamily (Set.range (fun k => (D k).carrier)) S.carrier) :=
  (ofArrows_mem_iff_isQuasinet D (fun k => homOfLE (hDS k))).mp (hD.ofArrows_mem hDS)

/-- Restricting the ambient domains to the actual subspace atlas converts the
same whole-chart hypothesis into the one used by global chart descent. -/
theorem OriginalDomainCoversChartsWithin.toSubspace
    {S : A.atlas.OriginalChartDomain} {D : ι → A.atlas.OriginalChartDomain}
    (hD : OriginalDomainCoversChartsWithin S D) (hDS : ∀ k, D k ≤ S) :
    OriginalDomainCoversCharts (A := A.originalDomainPresentation S)
      (fun k => S.subspaceRestrict ⟨D k, hDS k⟩) := by
  intro c
  obtain ⟨k, hk⟩ := hD c
  refine ⟨k, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hk ⟨x, rfl⟩

namespace StrongHom

/-- Restrict a map on `S` to an ambient image and then move to the nested
presentation. This is its ordinary subspace restriction as a full strong map. -/
theorem toNestedOriginalDomain_restrictFromDomain
    (S : A.atlas.OriginalChartDomain)
    (U : (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (f : StrongHom (A.originalDomainPresentation S) B) :
    toNestedOriginalDomain S U (f.restrictOriginalDomain (S.subspaceExtend_le U)) =
      f.restrictSubspace U.carrier U.is_domain := by
  refine ext_of_pullback rfl ?_
  intro c j h h'
  rfl

/-- Restriction of a full map on `S` is an ambient-domain matching family. -/
def toOriginalDomainStrongMatchingFamilyWithin
    {S : A.atlas.OriginalChartDomain}
    (f : StrongHom (A.originalDomainPresentation S) B)
    (D : ι → A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S) :
    OriginalDomainStrongMatchingFamily A B D where
  localMap k := f.restrictOriginalDomain (hDS k)
  overlap k l := (f.restrictOriginalDomain_trans
    (inf_le_left : D k ⊓ D l ≤ D k) (hDS k)).trans
      (f.restrictOriginalDomain_trans
        (inf_le_right : D k ⊓ D l ≤ D l) (hDS l)).symm

end StrongHom

namespace OriginalDomainStrongMatchingFamily

/-- Transport actual ambient-image local maps to the corresponding nested maps.
Full restriction naturality carries the intersection matching equations. -/
def toNestedFamily (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (d : OriginalDomainStrongMatchingFamily A B (fun k => S.subspaceExtend (U k))) :
    OriginalDomainStrongMatchingFamily (A.originalDomainPresentation S) B U where
  localMap k := StrongHom.toNestedOriginalDomain S (U k) (d.localMap k)
  overlap k l := by
    rw [← StrongHom.toNestedOriginalDomain_restrict,
      ← StrongHom.toNestedOriginalDomain_restrict]
    exact congrArg (StrongHom.toNestedOriginalDomain S (U k ⊓ U l))
      (d.restrict_eq k l (S.subspaceExtend_mono inf_le_left)
        (S.subspaceExtend_mono inf_le_right))

/-- Glue ambient-image local maps on the actual domain presentation of `S`. -/
def glueIn (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U)
    (d : OriginalDomainStrongMatchingFamily A B (fun k => S.subspaceExtend (U k))) :
    StrongHom (A.originalDomainPresentation S) B :=
  (toNestedFamily S U d).glue hU

/-- Recover every complete ambient-image local map. -/
theorem glueIn_restrictOriginalDomain (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U)
    (d : OriginalDomainStrongMatchingFamily A B (fun k => S.subspaceExtend (U k)))
    (k : ι) :
    (glueIn S U hU d).restrictOriginalDomain (S.subspaceExtend_le (U k)) =
      d.localMap k := by
  apply (A.originalDomainStrongEquiv B S (U k)).injective
  change StrongHom.toNestedOriginalDomain S (U k) _ =
    StrongHom.toNestedOriginalDomain S (U k) _
  rw [StrongHom.toNestedOriginalDomain_restrictFromDomain]
  exact (toNestedFamily S U d).glue_restrictSubspace hU k

/-- The ambient-image restrictions determine the entire map on `S`. -/
theorem glueIn_unique (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U)
    (d : OriginalDomainStrongMatchingFamily A B (fun k => S.subspaceExtend (U k)))
    (f : StrongHom (A.originalDomainPresentation S) B)
    (hf : ∀ k, f.restrictOriginalDomain (S.subspaceExtend_le (U k)) = d.localMap k) :
    f = glueIn S U hU d := by
  apply (toNestedFamily S U d).glue_unique hU f
  intro k
  have h := congrArg (StrongHom.toNestedOriginalDomain S (U k)) (hf k)
  rw [StrongHom.toNestedOriginalDomain_restrictFromDomain] at h
  exact h

private def glueTransport (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U) {D : ι → A.atlas.OriginalChartDomain}
    (e : (fun k => S.subspaceExtend (U k)) = D)
    (d : OriginalDomainStrongMatchingFamily A B D) :
    StrongHom (A.originalDomainPresentation S) B :=
  glueIn S U hU (e.symm ▸ d)

private theorem glueTransport_restrict (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U) {D : ι → A.atlas.OriginalChartDomain}
    (e : (fun k => S.subspaceExtend (U k)) = D)
    (d : OriginalDomainStrongMatchingFamily A B D) (hDS : ∀ k, D k ≤ S) (k : ι) :
    (glueTransport S U hU e d).restrictOriginalDomain (hDS k) = d.localMap k := by
  cases e
  exact glueIn_restrictOriginalDomain S U hU d k

private theorem glueTransport_unique (S : A.atlas.OriginalChartDomain)
    (U : ι → (A.originalDomainPresentation S).atlas.OriginalChartDomain)
    (hU : OriginalDomainCoversCharts U) {D : ι → A.atlas.OriginalChartDomain}
    (e : (fun k => S.subspaceExtend (U k)) = D)
    (d : OriginalDomainStrongMatchingFamily A B D) (hDS : ∀ k, D k ≤ S)
    (f : StrongHom (A.originalDomainPresentation S) B)
    (hf : ∀ k, f.restrictOriginalDomain (hDS k) = d.localMap k) :
    f = glueTransport S U hU e d := by
  cases e
  exact glueIn_unique S U hU d f hf

variable {D : ι → A.atlas.OriginalChartDomain}

/-- Full descent over any actual original-chart domain `S`. Only the supplied
local maps are inputs; no global output map or bounded pullback is assumed. -/
def glueWithin (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) :
    StrongHom (A.originalDomainPresentation S) B :=
  glueTransport S (fun k => S.subspaceRestrict ⟨D k, hDS k⟩) (hD.toSubspace hDS)
    (funext fun k => S.subspaceExtend_subspaceRestrict ⟨D k, hDS k⟩) d

/-- Each complete local map is recovered on its literal ambient domain. -/
@[simp]
theorem glueWithin_restrictOriginalDomain (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) (k : ι) :
    (d.glueWithin S hDS hD).restrictOriginalDomain (hDS k) = d.localMap k :=
  glueTransport_restrict S _ _ _ d hDS k

/-- All local point values are retained by the constructed map on `S`. -/
theorem glueWithin_apply (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) (k : ι) (x : D k) :
    (d.glueWithin S hDS hD).baseMap ⟨x.val, hDS k x.property⟩ =
      (d.localMap k).baseMap x :=
  congrArg (fun f : StrongHom (A.originalDomainPresentation (D k)) B => f.baseMap x)
    (d.glueWithin_restrictOriginalDomain S hDS hD k)

/-- Every admissible bounded algebra pullback is retained, with independent
admissibility witnesses on the map on `S` and on the given local map. -/
theorem glueWithin_pullback (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) (k : ι)
    (c : A.atlas.SubspaceChart (D k).carrier) (j : B.atlas.Index)
    (h : (d.glueWithin S hDS hD).baseMap ''
      Set.range ((A.originalDomainPresentation S).atlas.chart
        ⟨c.val, c.property.trans (hDS k)⟩) ⊆ Set.range (B.atlas.chart j))
    (hk : (d.localMap k).baseMap ''
      Set.range ((A.originalDomainPresentation (D k)).atlas.chart c) ⊆
        Set.range (B.atlas.chart j)) :
    (d.glueWithin S hDS hD).pullback ⟨c.val, c.property.trans (hDS k)⟩ j h =
      (d.localMap k).pullback c j hk :=
  StrongHom.pullback_congr (d.glueWithin_restrictOriginalDomain S hDS hD k) c j
    ((StrongHom.restrictOriginalDomain_admissible_iff (A := A)
      (S := D k) (T := S) (hDS k) (d.glueWithin S hDS hD) c j).mpr h) hk

/-- The full ambient-domain restrictions uniquely determine the map on `S`. -/
theorem glueWithin_unique (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D)
    (f : StrongHom (A.originalDomainPresentation S) B)
    (hf : ∀ k, f.restrictOriginalDomain (hDS k) = d.localMap k) :
    f = d.glueWithin S hDS hD :=
  glueTransport_unique S _ _ _ d hDS f hf

@[simp]
theorem glueWithin_toOriginalDomainStrongMatchingFamilyWithin
    (d : OriginalDomainStrongMatchingFamily A B D)
    (S : A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) :
    (d.glueWithin S hDS hD).toOriginalDomainStrongMatchingFamilyWithin D hDS = d := by
  apply ext
  funext k
  exact d.glueWithin_restrictOriginalDomain S hDS hD k

/-- Full matching families on arbitrary ambient domains inside `S` correspond
to full maps on `S`, under explicit whole-contained-chart coverage. -/
def strongHomWithinEquiv (S : A.atlas.OriginalChartDomain)
    (D : ι → A.atlas.OriginalChartDomain) (hDS : ∀ k, D k ≤ S)
    (hD : OriginalDomainCoversChartsWithin S D) :
    OriginalDomainStrongMatchingFamily A B D ≃ StrongHom (A.originalDomainPresentation S) B where
  toFun d := d.glueWithin S hDS hD
  invFun f := f.toOriginalDomainStrongMatchingFamilyWithin D hDS
  left_inv d := d.glueWithin_toOriginalDomainStrongMatchingFamilyWithin S hDS hD
  right_inv f := ((f.toOriginalDomainStrongMatchingFamilyWithin D hDS).glueWithin_unique
    S hDS hD f (fun _ => rfl)).symm

end OriginalDomainStrongMatchingFamily

end Langlands.Analytic.AffinoidAtlasPresentation

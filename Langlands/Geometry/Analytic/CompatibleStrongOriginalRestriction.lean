import Langlands.Geometry.Analytic.CompatibleStrongSaturationFunctor

/-! # Restriction from the actual enlargement to original compatible maps -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K]

namespace BoundedAlgHom

/-- Transport a complete bounded map along equalities of its presented
affinoid source and target algebras. -/
def transport {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (p : BoundedAlgHom K S R) :
    BoundedAlgHom K S' R' := by
  cases hR
  cases hS
  exact p

theorem transport_heq {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (p : BoundedAlgHom K S R) :
    HEq (transport hR hS p) p := by
  cases hR
  cases hS
  rfl

theorem comp_heq {R R' S S' T T' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S') (hT : T = T')
    {p : BoundedAlgHom K S R} {p' : BoundedAlgHom K S' R'}
    {q : BoundedAlgHom K T S} {q' : BoundedAlgHom K T' S'}
    (hp : HEq p p') (hq : HEq q q') :
    HEq (p.comp q) (p'.comp q') := by
  cases hR
  cases hS
  cases hT
  cases eq_of_heq hp
  cases eq_of_heq hq
  rfl

private theorem chart_comm_transport {X Y : Type v}
    {R R' S S' : PresentedAffinoidAlgebra K}
    (hR : R = R') (hS : S = S')
    {c : BanachSpectrum R → X} {c' : BanachSpectrum R' → X}
    {d : BanachSpectrum S → Y} {d' : BanachSpectrum S' → Y}
    (hc : HEq c c') (hd : HEq d d')
    {p : BoundedAlgHom K S R} {p' : BoundedAlgHom K S' R'}
    (hp : HEq p p') (f : X → Y)
    (h : ∀ x, d (BanachSpectrum.comap p.toBoundedRingHom x) = f (c x)) :
    ∀ x, d' (BanachSpectrum.comap p'.toBoundedRingHom x) = f (c' x) := by
  cases hR
  cases hS
  cases eq_of_heq hc
  cases eq_of_heq hd
  cases eq_of_heq hp
  exact h

end BoundedAlgHom

variable [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

private theorem localDomain_original_chart_heq (U : LocalDomain a) (i : a.Index)
    (hU : U = a.originalLocalDomain i) :
    HEq (U.ambientMap : BanachSpectrum U.algebra → X) (a.chart i) := by
  cases hU
  exact heq_of_eq (funext (a.originalLocalDomain_ambientMap i))

/-- Original charts in the enlargement retain the complete chart map,
up to the proved equality of their chosen algebras. -/
theorem saturatedAtlas_original_chart_heq (i : a.Index) :
    HEq (a.saturatedAtlas.chart (a.originalSaturatedIndex i)) (a.chart i) :=
  a.localDomain_original_chart_heq _ i (a.saturatedRepresentative_original i)

private theorem localDomain_original_restriction_heq
    (U V : LocalDomain a) (i j : a.Index)
    (hU : U = a.originalLocalDomain i) (hV : V = a.originalLocalDomain j)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j)) (p : U ⟶ V) :
    HEq p.restriction (a.restriction i j h) := by
  cases hU
  cases hV
  exact heq_of_eq (a.originalLocalDomain_restriction i j h p)

/-- The enlargement's restriction between original charts is the actual
original bounded restriction, with only its algebra endpoints transported. -/
theorem saturatedAtlas_original_restriction_heq (i j : a.Index)
    (h : Set.range (a.chart i) ⊆ Set.range (a.chart j))
    (h' : Set.range (a.saturatedAtlas.chart (a.originalSaturatedIndex i)) ⊆
      Set.range (a.saturatedAtlas.chart (a.originalSaturatedIndex j))) :
    HEq (a.saturatedAtlas.restriction (a.originalSaturatedIndex i)
      (a.originalSaturatedIndex j) h') (a.restriction i j h) :=
  a.localDomain_original_restriction_heq _ _ i j
    (a.saturatedRepresentative_original i) (a.saturatedRepresentative_original j) h _

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Original admissibility is equivalent to admissibility of the same charts
in the actual enlargement. -/
theorem original_admissible (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    F.baseMap '' Set.range (A.atlas.saturatedAtlas.chart (A.atlas.originalSaturatedIndex i)) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (B.atlas.originalSaturatedIndex j)) := by
  exact (Set.image_mono (A.atlas.saturatedAtlas_original_range i).subset).trans
    (h.trans (B.atlas.saturatedAtlas_original_range j).superset)

/-- Each enlarged containing target has an original parent containing it. -/
theorem original_target_exists
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) (i : A.atlas.Index) :
    ∃ j, F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := by
  obtain ⟨T, hT⟩ := F.target_exists (A.atlas.originalSaturatedIndex i)
  refine ⟨(B.atlas.saturatedRepresentative T).index, ?_⟩
  exact (Set.image_mono (A.atlas.saturatedAtlas_original_range i).superset).trans
    (hT.trans ((saturated_chart_subset_parent T).trans
      (B.atlas.saturatedAtlas_original_range _).subset))

/-- Restrict an enlarged pullback to an original admissible pair by actual
algebra identification. No map is reconstructed from its spectrum action. -/
def originalPullback (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) :=
  BoundedAlgHom.transport (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra j)
    (F.pullback (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
      (F.original_admissible i j h))

theorem originalPullback_heq
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    HEq (F.originalPullback i j h)
      (F.pullback (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
        (F.original_admissible i j h)) :=
  BoundedAlgHom.transport_heq _ _ _

theorem originalPullback_chart
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    ∀ x : BanachSpectrum (A.atlas.algebra i),
      B.atlas.chart j
        (BanachSpectrum.comap (F.originalPullback i j h).toBoundedRingHom x) =
          F.baseMap (A.atlas.chart i x) :=
  BoundedAlgHom.chart_comm_transport
    (A.atlas.saturatedAtlas_original_algebra i) (B.atlas.saturatedAtlas_original_algebra j)
    (A.atlas.saturatedAtlas_original_chart_heq i) (B.atlas.saturatedAtlas_original_chart_heq j)
    (F.originalPullback_heq i j h).symm F.baseMap
    (F.chart_comm _ _ _)

/-- Original source and target restriction equations follow by transport
of the full enlarged bounded-map equation. -/
theorem originalPullback_naturality
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i i' : A.atlas.Index) (j j' : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : F.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')) :
    (A.atlas.restriction i i' hi).comp (F.originalPullback i' j' h') =
      (F.originalPullback i j h).comp (B.atlas.restriction j j' hj) := by
  have hI := (A.atlas.saturatedAtlas_original_range i).subset.trans
    (hi.trans (A.atlas.saturatedAtlas_original_range i').superset)
  have hJ := (B.atlas.saturatedAtlas_original_range j).subset.trans
    (hj.trans (B.atlas.saturatedAtlas_original_range j').superset)
  have hs := F.restriction_comm
    (A.atlas.originalSaturatedIndex i) (A.atlas.originalSaturatedIndex i')
    (B.atlas.originalSaturatedIndex j) (B.atlas.originalSaturatedIndex j')
    hI hJ (F.original_admissible i j h) (F.original_admissible i' j' h')
  have hl := BoundedAlgHom.comp_heq
    (A.atlas.saturatedAtlas_original_algebra i)
    (A.atlas.saturatedAtlas_original_algebra i')
    (B.atlas.saturatedAtlas_original_algebra j')
    (A.atlas.saturatedAtlas_original_restriction_heq i i' hi hI)
    (F.originalPullback_heq i' j' h').symm
  have hr := BoundedAlgHom.comp_heq
    (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra j)
    (B.atlas.saturatedAtlas_original_algebra j')
    (F.originalPullback_heq i j h).symm
    (B.atlas.saturatedAtlas_original_restriction_heq j j' hj hJ)
  exact eq_of_heq (hl.symm.trans ((heq_of_eq hs).trans hr))

/-- Saturated coherence transfers to the original family on every bounded
coefficient test and every common original target subchart. -/
theorem originalPullback_isMapChartChange
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (i : A.atlas.Index) (j k : B.atlas.Index)
    (hj : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hk : F.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart k)) :
    B.atlas.IsMapChartChange j k (A.atlas.algebra i)
      (F.originalPullback i j hj) (F.originalPullback i k hk) := by
  intro T η m hmj hmk α hα
  let ηS := BoundedAlgHom.transport rfl
    (A.atlas.saturatedAtlas_original_algebra i).symm η
  let αS := BoundedAlgHom.transport rfl
    (B.atlas.saturatedAtlas_original_algebra m).symm α
  have hη : HEq ηS η := BoundedAlgHom.transport_heq _ _ _
  have hαS : HEq αS α := BoundedAlgHom.transport_heq _ _ _
  have hMJ := (B.atlas.saturatedAtlas_original_range m).subset.trans
    (hmj.trans (B.atlas.saturatedAtlas_original_range j).superset)
  have hMK := (B.atlas.saturatedAtlas_original_range m).subset.trans
    (hmk.trans (B.atlas.saturatedAtlas_original_range k).superset)
  have hleft := BoundedAlgHom.comp_heq rfl
    (B.atlas.saturatedAtlas_original_algebra m)
    (B.atlas.saturatedAtlas_original_algebra j) hαS
    (B.atlas.saturatedAtlas_original_restriction_heq m j hmj hMJ)
  have hright := BoundedAlgHom.comp_heq rfl
    (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra j) hη
    (F.originalPullback_heq i j hj).symm
  have htest := F.pullback_isMapChartChange A.atlas.saturatedAtlas_hasAllLocalDomains
    (A.atlas.originalSaturatedIndex i) (B.atlas.originalSaturatedIndex j)
    (B.atlas.originalSaturatedIndex k)
    (F.original_admissible i j hj) (F.original_admissible i k hk)
    T ηS (B.atlas.originalSaturatedIndex m) hMJ hMK αS
    (eq_of_heq (hleft.trans ((heq_of_eq hα).trans hright.symm)))
  have houtleft := BoundedAlgHom.comp_heq rfl
    (A.atlas.saturatedAtlas_original_algebra i)
    (B.atlas.saturatedAtlas_original_algebra k) hη
    (F.originalPullback_heq i k hk).symm
  have houtright := BoundedAlgHom.comp_heq rfl
    (B.atlas.saturatedAtlas_original_algebra m)
    (B.atlas.saturatedAtlas_original_algebra k) hαS
    (B.atlas.saturatedAtlas_original_restriction_heq m k hmk hMK)
  exact eq_of_heq (houtleft.symm.trans ((heq_of_eq htest).trans houtright))

/-- Restrict any actual enlarged strong map to the complete compatible
original bounded family. Source saturation proves the original local law. -/
def originalRestriction
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    CompatibleStrongHom A B where
  baseMap := F.baseMap
  target_exists := F.original_target_exists
  pullback := F.originalPullback
  chart_comm := F.originalPullback_chart
  restriction_comm := F.originalPullback_naturality
  compatible := (hasLocallyCompatiblePullbacks_iff _).mpr F.originalPullback_isMapChartChange

@[simp]
theorem originalRestriction_baseMap
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    F.originalRestriction.baseMap = F.baseMap := rfl

/-- The original restriction recovers the enlarged map on every original
admissible pair as a complete bounded map. -/
theorem originalRestriction_recovers
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    F.originalRestriction.toStrongHom.IsSaturationExtension F :=
  ⟨rfl, fun i j h => (F.originalPullback_heq i j h).symm⟩

/-- Extending the actual original restriction recovers the entire enlarged
map, including all new source and target pullbacks. -/
@[simp]
theorem saturationExtension_originalRestriction
    (F : StrongHom A.saturatedPresentation B.saturatedPresentation) :
    F.originalRestriction.saturationExtension = F :=
  (F.originalRestriction.saturationExtension_unique F F.originalRestriction_recovers).symm

end AffinoidAtlasPresentation.StrongHom

namespace AffinoidAtlasPresentation.CompatibleStrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Every original admissible bounded pullback is recovered after extension
and restriction, with equality in the literal original algebra types. -/
@[simp]
theorem originalPullback_saturationExtension (f : CompatibleStrongHom A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.saturationExtension.originalPullback i j h = f.pullback i j h :=
  eq_of_heq ((f.saturationExtension.originalPullback_heq i j h).trans
    (f.toStrongHom.saturationExtension_pullback_original f.coherent i j h))

/-- Restricting the actual extension recovers the complete original
compatible map. -/
@[simp]
theorem originalRestriction_saturationExtension (f : CompatibleStrongHom A B) :
    f.saturationExtension.originalRestriction = f := by
  refine ext_of_pullback rfl ?_
  intro i
  obtain ⟨j, h⟩ := f.target_exists i
  exact ⟨j, h, f.originalPullback_saturationExtension i j h⟩

/-- Actual extension and restriction are inverse on complete Hom sets,
including the continuous maps and every bounded pullback. -/
def saturationExtensionEquiv :
    CompatibleStrongHom A B ≃ StrongHom A.saturatedPresentation B.saturatedPresentation where
  toFun := saturationExtension
  invFun := StrongHom.originalRestriction
  left_inv := originalRestriction_saturationExtension
  right_inv := StrongHom.saturationExtension_originalRestriction

end AffinoidAtlasPresentation.CompatibleStrongHom

namespace CompatibleAtlasPresentation

instance : (saturationFunctor (K := K) :
    CompatibleAtlasPresentation.{u, v, w} K ⥤ _).Full where
  map_surjective F := ⟨F.originalRestriction, F.saturationExtension_originalRestriction⟩

end CompatibleAtlasPresentation
end Langlands.Analytic

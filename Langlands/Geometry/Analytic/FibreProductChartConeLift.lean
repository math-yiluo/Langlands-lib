import Langlands.Geometry.Analytic.FibreProductSmallCone
import Langlands.Geometry.Analytic.OriginalChartSourceMaps
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction

/-! # Complete cone lifts on nonempty aligned source charts -/

noncomputable section

universe u v

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C T : AffinoidAtlasPresentation.{u, v, v} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)
  (a : CompatibleStrongHom T A) (b : CompatibleStrongHom T B)
  (hab : a.comp f = b.comp g)

include hab

/-- A complete commuting cone has compatible bounded pullbacks over every
admissible common original base. -/
theorem coneChartPullbacks_compatible (i : T.atlas.Index) (p : PairIndex f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2)) :
    (a.pullback i p.val.1 ha).comp (leftBase f g p) =
      (b.pullback i p.val.2 hb).comp (rightBase f g p) := by
  have hfa := a.toStrongHom.comp_admissible f.toStrongHom i p.val.1 (base f g p)
    ha (isCommonBase_base f g p).1
  have hgb := b.toStrongHom.comp_admissible g.toStrongHom i p.val.2 (base f g p)
    hb (isCommonBase_base f g p).2
  exact (CompatibleStrongHom.comp_pullback a f i p.val.1 (base f g p)
    ha (isCommonBase_base f g p).1 hfa).symm.trans
      ((StrongHom.pullback_congr (congrArg CompatibleStrongHom.toStrongHom hab)
        i (base f g p) hfa hgb).trans
        (CompatibleStrongHom.comp_pullback b g i p.val.2 (base f g p)
          hb (isCommonBase_base f g p).2 hgb))

/-- The actual bounded pushout lift at one aligned source chart. -/
def coneChartPullback (i : T.atlas.Index) (p : PairIndex f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2)) :
    BoundedAlgHom K (algebra f g p) (T.atlas.algebra i) :=
  AffinoidPushout.lift (leftBase f g p) (rightBase f g p) (T.atlas.algebra i)
    (a.pullback i p.val.1 ha) (b.pullback i p.val.2 hb)
      (coneChartPullbacks_compatible f g a b hab i p ha hb)

/-- A nonempty aligned source spectrum supplies a nonempty actual pair-chart
range, hence an index of the domain-indexed local atlas. -/
def coneChartDomainIndex (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) : LocalAtlasIndex f g :=
  ⟨range ((chartSystem f g).chart p), ⟨by
    let x := Classical.choice hne
    exact ⟨_, ⟨BanachSpectrum.comap (coneChartPullback f g a b hab i p ha hb).toBoundedRingHom x, rfl⟩⟩,
    p, hp, rfl⟩⟩

variable [Small.{v} (chartSystem f g).Space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- The shrunk target index of the actual selected chart domain. -/
def coneChartTargetIndex (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) :
    (smallPresentation f g hA hB hC).atlas.Index :=
  equivShrink (LocalAtlasIndex f g) (coneChartDomainIndex f g a b hab i p hp ha hb hne)

/-- Domain-indexing may choose a different representative pair, with the
same literal quotient range. -/
theorem range_coneChartTargetIndex (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) :
    range ((chartSystem f g).chart (smallRep f g hA hB hC
      (coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne))) =
        range ((chartSystem f g).chart p) := by
  change range ((chartSystem f g).chart
    (((equivShrink (LocalAtlasIndex f g)).symm
      (equivShrink (LocalAtlasIndex f g) (coneChartDomainIndex f g a b hab i p hp ha hb hne))).rep)) = _
  rw [Equiv.symm_apply_apply]
  exact (coneChartDomainIndex f g a b hab i p hp ha hb hne).range_rep

/-- Change the pushout lift to the chosen atlas representative by the actual
bounded range restriction, then construct the entire original compatible map. -/
def coneChartLift (hT : T.atlas.HasAllLocalDomains)
    (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) :
    CompatibleStrongHom (T.chartPresentation i) (smallPresentation f g hA hB hC) :=
  let J := coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne
  let hpr := (range_coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne).symm.subset
  CompatibleStrongHom.fromChartPullback (TopChartPresentation.ofChart T i)
    (IndexedAffinoidAtlas.subspaceAtlas_hasAllLocalDomains hT _ (T.atlas.isOriginalChartDomain_chart i))
    J ((coneChartPullback f g a b hab i p ha hb).comp (rangeRestriction f g hpr))

/-- The complete first projection of the constructed chart lift is the
entire original first cone leg restricted to the actual source chart domain. -/
theorem coneChartLift_comp_fst (hT : T.atlas.HasAllLocalDomains)
    (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) :
    (coneChartLift f g a b hab hA hB hC hT i p hp ha hb hne).comp (smallFstHom f g hA hB hC) =
      a.restrictSubspace (range (T.atlas.chart i)) (T.atlas.isOriginalChartDomain_chart i) := by
  let J := coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne
  let r := smallRep f g hA hB hC J
  have her : range ((chartSystem f g).chart r) = range ((chartSystem f g).chart p) :=
    range_coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne
  have hpr : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart r) := her.symm.subset
  have hFJ : (smallFstHom f g hA hB hC).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (A.atlas.chart p.val.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx := ((mem_range_chart_iff f g p ((chartSystem f g).chart r x)).mp
      (her.subset ⟨x, rfl⟩)).1
    exact (smallFstBase_chart f g hA hB hC J x).symm ▸ hx
  have hmem : ∀ x, A.atlas.chart r.val.1 (leftPoint f g r x) ∈ range (A.atlas.chart p.val.1) :=
    fun x => ((mem_range_chart_iff f g p ((chartSystem f g).chart r x)).mp
      (her.subset ⟨x, rfl⟩)).1
  have hR : (rangeRestriction f g hpr).comp (smallFstPullback f g hA hB hC J p.val.1 hFJ) =
      leftMap f g p :=
    (A.atlas.eq_changeMapChart p.val.1 p.val.1 (algebra f g p) (leftMap f g p)
      (fun x => ⟨_, rfl⟩) _ (isMapChartChange_rangeRestriction_left f g hpr p.val.1 hmem)).trans
        (A.atlas.changeMapChart_self _ _ _ _)
  have hbound : ((coneChartPullback f g a b hab i p ha hb).comp (rangeRestriction f g hpr)).comp
      ((smallFstHom f g hA hB hC).pullback J p.val.1 hFJ) = a.pullback i p.val.1 ha := by
    change ((coneChartPullback f g a b hab i p ha hb).comp (rangeRestriction f g hpr)).comp
      (smallFstPullback f g hA hB hC J p.val.1 hFJ) = _
    rw [BoundedAlgHom.comp_assoc, hR]
    exact AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _
  let hs := IndexedAffinoidAtlas.subspaceAtlas_hasAllLocalDomains hT _
    (T.atlas.isOriginalChartDomain_chart i)
  let P := TopChartPresentation.ofChart T i
  have halocal : (a.restrictSubspace (range (T.atlas.chart i))
      (T.atlas.isOriginalChartDomain_chart i)).baseMap ''
        range (P.presentation.atlas.chart P.topChart) ⊆ range (A.atlas.chart p.val.1) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ha ⟨_, ⟨x, rfl⟩, rfl⟩
  exact (CompatibleStrongHom.fromChartPullback_comp P hs J _ (smallFstHom f g hA hB hC)
    p.val.1 hFJ).trans
      ((congrArg (CompatibleStrongHom.fromChartPullback P hs p.val.1) hbound).trans
        (CompatibleStrongHom.fromChartPullback_eq P hs p.val.1 _ halocal))

/-- The complete second projection of the constructed chart lift is the
entire original second cone leg on the actual source chart domain. -/
theorem coneChartLift_comp_snd (hT : T.atlas.HasAllLocalDomains)
    (i : T.atlas.Index) (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (ha : a.baseMap '' range (T.atlas.chart i) ⊆ range (A.atlas.chart p.val.1))
    (hb : b.baseMap '' range (T.atlas.chart i) ⊆ range (B.atlas.chart p.val.2))
    (hne : Nonempty (BanachSpectrum (T.atlas.algebra i))) :
    (coneChartLift f g a b hab hA hB hC hT i p hp ha hb hne).comp (smallSndHom f g hA hB hC) =
      b.restrictSubspace (range (T.atlas.chart i)) (T.atlas.isOriginalChartDomain_chart i) := by
  let J := coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne
  let r := smallRep f g hA hB hC J
  have her : range ((chartSystem f g).chart r) = range ((chartSystem f g).chart p) :=
    range_coneChartTargetIndex f g a b hab hA hB hC i p hp ha hb hne
  have hpr : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart r) := her.symm.subset
  have hSJ : (smallSndHom f g hA hB hC).baseMap ''
      range ((smallPresentation f g hA hB hC).atlas.chart J) ⊆ range (B.atlas.chart p.val.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    have hx := ((mem_range_chart_iff f g p ((chartSystem f g).chart r x)).mp
      (her.subset ⟨x, rfl⟩)).2
    exact (smallSndBase_chart f g hA hB hC J x).symm ▸ hx
  have hmem : ∀ x, B.atlas.chart r.val.2 (rightPoint f g r x) ∈ range (B.atlas.chart p.val.2) :=
    fun x => ((mem_range_chart_iff f g p ((chartSystem f g).chart r x)).mp
      (her.subset ⟨x, rfl⟩)).2
  have hR : (rangeRestriction f g hpr).comp (smallSndPullback f g hA hB hC J p.val.2 hSJ) =
      rightMap f g p :=
    (B.atlas.eq_changeMapChart p.val.2 p.val.2 (algebra f g p) (rightMap f g p)
      (fun x => ⟨_, rfl⟩) _ (isMapChartChange_rangeRestriction_right f g hpr p.val.2 hmem)).trans
        (B.atlas.changeMapChart_self _ _ _ _)
  have hbound : ((coneChartPullback f g a b hab i p ha hb).comp (rangeRestriction f g hpr)).comp
      ((smallSndHom f g hA hB hC).pullback J p.val.2 hSJ) = b.pullback i p.val.2 hb := by
    change ((coneChartPullback f g a b hab i p ha hb).comp (rangeRestriction f g hpr)).comp
      (smallSndPullback f g hA hB hC J p.val.2 hSJ) = _
    rw [BoundedAlgHom.comp_assoc, hR]
    exact AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _
  let hs := IndexedAffinoidAtlas.subspaceAtlas_hasAllLocalDomains hT _
    (T.atlas.isOriginalChartDomain_chart i)
  let P := TopChartPresentation.ofChart T i
  have hblocal : (b.restrictSubspace (range (T.atlas.chart i))
      (T.atlas.isOriginalChartDomain_chart i)).baseMap ''
        range (P.presentation.atlas.chart P.topChart) ⊆ range (B.atlas.chart p.val.2) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact hb ⟨_, ⟨x, rfl⟩, rfl⟩
  exact (CompatibleStrongHom.fromChartPullback_comp P hs J _ (smallSndHom f g hA hB hC)
    p.val.2 hSJ).trans
      ((congrArg (CompatibleStrongHom.fromChartPullback P hs p.val.2) hbound).trans
        (CompatibleStrongHom.fromChartPullback_eq P hs p.val.2 _ hblocal))

end Langlands.Analytic.FibreProduct

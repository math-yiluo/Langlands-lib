import Langlands.Geometry.Analytic.FiniteOpenBaseChangeModels
import Langlands.Geometry.Analytic.FibreProductRestriction

/-! # Complete overlap transitions of finite open base-change models -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)

/-- The literal finite local pushout over any actual full source subdomain. -/
def restrictedAlgebra (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) : PresentedAffinoidAlgebra K :=
  AffinoidPushout.algebra (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i))

def restrictedLeftMap (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    BoundedAlgHom K (M.left i).algebra (M.restrictedAlgebra i r) :=
  AffinoidPushout.leftMap _ _

def restrictedRightMap (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    BoundedAlgHom K E.algebra (M.restrictedAlgebra i r) :=
  AffinoidPushout.rightMap _ _

theorem restrictedAmbientCondition (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (x : BanachSpectrum (M.restrictedAlgebra i r)) :
    f.baseMap ((M.left i).chart (BanachSpectrum.comap (M.restrictedLeftMap i r).toBoundedRingHom x)) =
      g.baseMap (R.chart (E.spectrumMap
        (BanachSpectrum.comap (M.restrictedRightMap i r).toBoundedRingHom x))) := by
  have he := congrArg
    (fun q : BoundedAlgHom K (M.rightCover.target i).algebra (M.restrictedAlgebra i r) =>
      BanachSpectrum.comap q.toBoundedRingHom x)
    (AffinoidPushout.condition (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i)))
  exact (f.fullRecognitionPairs.chart_comm (M.left i) (M.rightCover.target i)
    (M.left_admissible i) (BanachSpectrum.comap (M.restrictedLeftMap i r).toBoundedRingHom x)).symm.trans
    ((congrArg (M.rightCover.target i).chart he).trans
      ((M.rightCover.canonicalPullback_chart i
        (r.spectrumMap (BanachSpectrum.comap (M.restrictedRightMap i r).toBoundedRingHom x))).trans
          (congrArg (fun z => g.baseMap (R.chart z))
            (r.spectrumMap_over_base
              (BanachSpectrum.comap (M.restrictedRightMap i r).toBoundedRingHom x)))))

/-- The exact finite-open source loci force every left point into every
other local chart lying above the same actual full source subdomain. -/
theorem restrictedLeftPoint_mem
    (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j)
    (x : BanachSpectrum (M.restrictedAlgebra i r)) :
    (M.left i).chart (BanachSpectrum.comap (M.restrictedLeftMap i r).toBoundedRingHom x) ∈
      range (M.left j).chart := by
  rw [(M.left j).range_chart, M.left_locus j]
  refine ⟨((M.left_locus i).subset ((M.left i).range_chart.subset ⟨_, rfl⟩)).1, ?_⟩
  change f.baseMap _ ∈ (M.rightCover.target j).locus
  rw [M.restrictedAmbientCondition i r x]
  let y := BanachSpectrum.comap (M.restrictedRightMap i r).toBoundedRingHom x
  exact (M.rightCover.target j).range_chart.subset
    ⟨_, (M.rightCover.canonicalPullback_chart j (s.spectrumMap y)).trans
      (congrArg (fun z => g.baseMap (R.chart z)) (s.spectrumMap_over_base y))⟩

/-- Regard each finite left chart as a literal index of the admissible
recognition source, retaining its entire original pullback. -/
def leftIndex (i : Fin M.rightCover.cover.size) : f.recognitionSource.atlas.Index :=
  f.recognitionSourceIndex (M.left i) (M.rightCover.target i) (M.left_admissible i)

/-- The entire changed left map is constructed by coefficient-sensitive
chart change on the original recognition source atlas. -/
def transitionLeft (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    BoundedAlgHom K (M.left j).algebra (M.restrictedAlgebra i r) :=
  f.recognitionSource.atlas.changeMapChart (M.leftIndex i) (M.leftIndex j)
    (M.restrictedAlgebra i r) (M.restrictedLeftMap i r) (M.restrictedLeftPoint_mem i j r s)

/-- Entire source and target coefficient coherence transfers the full
bounded pushout equation to the other local model. -/
theorem transitionCondition (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    (M.transitionLeft i j r s).comp (M.leftBase j) =
      (M.restrictedRightMap i r).comp (s.restriction.comp (M.rightCover.canonicalPullback j)) := by
  let D := M.restrictedAlgebra i r
  let α := M.restrictedLeftMap i r
  let β := M.restrictedRightMap i r
  let η := M.transitionLeft i j r s
  have hL : C.fullRecognitionPresentation.atlas.IsMapChartChange
      (M.rightCover.target i) (M.rightCover.target j) D
      (α.comp (M.leftBase i)) (η.comp (M.leftBase j)) :=
    f.recognitionMap.mapAffinoidChart_isMapChartChange_of_coherent f.compatibleRecognitionMap.coherent
      (M.leftIndex i) (M.leftIndex j) (M.rightCover.target i) (M.rightCover.target j)
      (M.left_admissible i) (M.left_admissible j) D α η (M.restrictedLeftPoint_mem i j r s)
      (f.recognitionSource.atlas.changeMapChart_isMapChartChange _ _ _ _ _)
  have hR := (M.rightCover.canonicalPullback_overlap i j E r s).comp
    C.fullRecognitionPresentation.atlas β
  have hc : α.comp (M.leftBase i) =
      β.comp (r.restriction.comp (M.rightCover.canonicalPullback i)) :=
    AffinoidPushout.condition _ _
  erw [← hc] at hR
  have himg : ∀ x : BanachSpectrum D,
      (M.rightCover.target i).chart (BanachSpectrum.comap (α.comp (M.leftBase i)).toBoundedRingHom x) ∈
        range (M.rightCover.target j).chart := by
    intro x
    change C.fullRecognitionPresentation.atlas.chart (M.rightCover.target i)
      (BanachSpectrum.comap (f.fullRecognitionPairs.pullback (M.left i) (M.rightCover.target i)
        (M.left_admissible i)).toBoundedRingHom (BanachSpectrum.comap α.toBoundedRingHom x)) ∈
        range (C.fullRecognitionPresentation.atlas.chart (M.rightCover.target j))
    erw [f.fullRecognitionPairs.chart_comm]
    exact M.left_admissible j ⟨_, M.restrictedLeftPoint_mem i j r s x, rfl⟩
  exact (C.fullRecognitionPresentation.atlas.eq_changeMapChart _ _ D _ himg _ hL).trans
    (C.fullRecognitionPresentation.atlas.eq_changeMapChart _ _ D _ himg _ hR).symm

/-- The actual bounded transition is the original pushout lift. Its
contravariant direction follows the chart-change convention. -/
def transitionMap (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    BoundedAlgHom K (M.restrictedAlgebra j s) (M.restrictedAlgebra i r) :=
  AffinoidPushout.lift (M.leftBase j) (s.restriction.comp (M.rightCover.canonicalPullback j))
    (M.restrictedAlgebra i r) (M.transitionLeft i j r s) (M.restrictedRightMap i r)
      (M.transitionCondition i j r s)

theorem transitionMap_comp_left (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    (M.transitionMap i j r s).comp (M.restrictedLeftMap j s) = M.transitionLeft i j r s :=
  AffinoidPushout.lift_comp_leftMap _ _ _ _ _ _

theorem transitionMap_comp_right (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    (M.transitionMap i j r s).comp (M.restrictedRightMap j s) = M.restrictedRightMap i r :=
  AffinoidPushout.lift_comp_rightMap _ _ _ _ _ _

theorem transitionMap_self (i : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) :
    M.transitionMap i i r r = BoundedAlgHom.id K (M.restrictedAlgebra i r) := by
  apply AffinoidPushout.hom_ext (M.leftBase i) (r.restriction.comp (M.rightCover.canonicalPullback i))
  · change (M.transitionMap i i r r).comp (M.restrictedLeftMap i r) =
      (BoundedAlgHom.id K (M.restrictedAlgebra i r)).comp (M.restrictedLeftMap i r)
    rw [M.transitionMap_comp_left, BoundedAlgHom.id_comp]
    exact f.recognitionSource.atlas.changeMapChart_self _ _ _ _
  · change (M.transitionMap i i r r).comp (M.restrictedRightMap i r) =
      (BoundedAlgHom.id K (M.restrictedAlgebra i r)).comp (M.restrictedRightMap i r)
    rw [M.transitionMap_comp_right, BoundedAlgHom.id_comp]

/-- The complete transitions satisfy the literal triple-overlap cocycle. -/
theorem transitionMap_comp (i j k : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j)
    (t : E ⟶ M.rightCover.cover.obj k) :
    (M.transitionMap i j r s).comp (M.transitionMap j k s t) = M.transitionMap i k r t := by
  apply AffinoidPushout.hom_ext (M.leftBase k) (t.restriction.comp (M.rightCover.canonicalPullback k))
  · change ((M.transitionMap i j r s).comp (M.transitionMap j k s t)).comp (M.restrictedLeftMap k t) =
      (M.transitionMap i k r t).comp (M.restrictedLeftMap k t)
    rw [BoundedAlgHom.comp_assoc, M.transitionMap_comp_left, M.transitionMap_comp_left]
    have h₁ := f.recognitionSource.atlas.changeMapChart_isMapChartChange
      (M.leftIndex i) (M.leftIndex j) (M.restrictedAlgebra i r) (M.restrictedLeftMap i r)
      (M.restrictedLeftPoint_mem i j r s)
    change f.recognitionSource.atlas.IsMapChartChange (M.leftIndex i) (M.leftIndex j)
      (M.restrictedAlgebra i r) (M.restrictedLeftMap i r) (M.transitionLeft i j r s) at h₁
    have h₂ := (f.recognitionSource.atlas.changeMapChart_isMapChartChange
      (M.leftIndex j) (M.leftIndex k) (M.restrictedAlgebra j s) (M.restrictedLeftMap j s)
      (M.restrictedLeftPoint_mem j k s t)).comp f.recognitionSource.atlas (M.transitionMap i j r s)
    change f.recognitionSource.atlas.IsMapChartChange (M.leftIndex j) (M.leftIndex k)
      (M.restrictedAlgebra i r)
      ((M.transitionMap i j r s).comp (M.restrictedLeftMap j s))
      ((M.transitionMap i j r s).comp (M.transitionLeft j k s t)) at h₂
    erw [M.transitionMap_comp_left] at h₂
    have hm : ∀ x : BanachSpectrum (M.restrictedAlgebra i r),
        f.recognitionSource.atlas.chart (M.leftIndex i)
          (BanachSpectrum.comap (M.restrictedLeftMap i r).toBoundedRingHom x) ∈
            range (f.recognitionSource.atlas.chart (M.leftIndex j)) :=
      M.restrictedLeftPoint_mem i j r s
    have h₃ := IndexedAffinoidAtlas.IsMapChartChange.trans f.recognitionSource.atlas
      (i := M.leftIndex i) (j := M.leftIndex j) (k := M.leftIndex k)
      (R := M.restrictedAlgebra i r) (φ := M.restrictedLeftMap i r)
      (ψ := M.transitionLeft i j r s)
      (χ := (M.transitionMap i j r s).comp (M.transitionLeft j k s t)) hm h₁ h₂
    exact f.recognitionSource.atlas.eq_changeMapChart (M.leftIndex i) (M.leftIndex k)
      (M.restrictedAlgebra i r) (M.restrictedLeftMap i r)
      (M.restrictedLeftPoint_mem i k r t)
      ((M.transitionMap i j r s).comp (M.transitionLeft j k s t))
      h₃
  · change ((M.transitionMap i j r s).comp (M.transitionMap j k s t)).comp (M.restrictedRightMap k t) =
      (M.transitionMap i k r t).comp (M.restrictedRightMap k t)
    rw [BoundedAlgHom.comp_assoc, M.transitionMap_comp_right,
      M.transitionMap_comp_right, M.transitionMap_comp_right]

/-- Both inverse identities hold on entire algebras, so the transitions
are actual bounded E-algebra equivalences, not spectrum bijections. -/
def transitionEquiv (i j : Fin M.rightCover.cover.size) {E : Domain K R.algebra}
    (r : E ⟶ M.rightCover.cover.obj i) (s : E ⟶ M.rightCover.cover.obj j) :
    BoundedAlgEquiv K (M.restrictedAlgebra j s) (M.restrictedAlgebra i r) :=
  BoundedAlgEquiv.ofHomInv (M.transitionMap i j r s) (M.transitionMap j i s r)
    (fun x => congrArg
      (fun q : BoundedAlgHom K (M.restrictedAlgebra j s) (M.restrictedAlgebra j s) => q x)
      ((M.transitionMap_comp j i j s r s).trans (M.transitionMap_self j s)))
    (fun x => congrArg
      (fun q : BoundedAlgHom K (M.restrictedAlgebra i r) (M.restrictedAlgebra i r) => q x)
      ((M.transitionMap_comp i j i r s r).trans (M.transitionMap_self i r)))

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

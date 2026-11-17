import Langlands.Geometry.Analytic.FiniteAlgebraEffectiveDomains
import Langlands.Geometry.Analytic.FiniteChartParentRecognition

/-! # Recognition of geometrically bound effective finite algebra parents -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

open CategoryTheory Set Topology IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K}
  {c : Domain.FiniteCover (Domain.whole K R)} {F : LocalAlgebras c}
  {X : Type v} [TopologicalSpace X]

/-- The exact local geometric binding: original component and intersection
charts, with full bounded algebra comparisons respecting both original
overlap legs. No global parent chart or recognition is supplied. -/
structure ChartBinding (t : PairTransitions F) (a : IndexedAffinoidAtlas.{u, v, w} K X) where
  index : Fin c.size → a.Index
  overlap : Fin c.size → Fin c.size → a.Index
  overlap_range : ∀ i j, range (a.chart (overlap i j)) =
    range (a.chart (index i)) ∩ range (a.chart (index j))
  componentEquiv : ∀ i, BoundedAlgEquiv K (F.algebra i) (a.algebra (index i))
  overlapEquiv : ∀ i j, BoundedAlgEquiv K
    (F.baseChange j (F.overlap i j) (F.overlapRight i j)) (a.algebra (overlap i j))
  left_compatible : ∀ i j,
    (a.restriction (overlap i j) (index i) ((overlap_range i j).subset.trans inter_subset_left)).comp
      (componentEquiv i).toBoundedAlgHom =
        (overlapEquiv i j).toBoundedAlgHom.comp (t.leftRestriction i j)
  right_compatible : ∀ i j,
    (a.restriction (overlap i j) (index j) ((overlap_range i j).subset.trans inter_subset_right)).comp
      (componentEquiv j).toBoundedAlgHom =
        (overlapEquiv i j).toBoundedAlgHom.comp (t.rightRestriction i j)

namespace ChartBinding

variable {a : IndexedAffinoidAtlas.{u, v, w} K X} {t : PairTransitions F}
  (b : ChartBinding t a)

/-- The binding supplies an actual finite original-chart family. -/
abbrev gluingData : FiniteChartGluingData a where
  size := c.size
  index := b.index
  overlap := b.overlap
  overlap_range := b.overlap_range

theorem leftRestriction_compatible (i j : Fin c.size) :
    (b.gluingData.leftRestriction i j).comp (b.componentEquiv i).toBoundedAlgHom =
      (b.overlapEquiv i j).toBoundedAlgHom.comp (t.leftRestriction i j) :=
  b.left_compatible i j

theorem rightRestriction_compatible (i j : Fin c.size) :
    (b.gluingData.rightRestriction i j).comp (b.componentEquiv j).toBoundedAlgHom =
      (b.overlapEquiv i j).toBoundedAlgHom.comp (t.rightRestriction i j) :=
  b.right_compatible i j

end ChartBinding

namespace ChartBinding

variable {a : IndexedAffinoidAtlas.{u, v, w} K X} {d : DescentData F}
  (b : ChartBinding d.toPairTransitions a) (P : EffectiveRealization d)

/-- The actual parent restriction into each bound original chart. -/
def parentRestriction (i : Fin c.size) : BoundedAlgHom K P.algebra (a.algebra (b.index i)) :=
  (b.componentEquiv i).toBoundedAlgHom.comp (P.toMatchingPresentation.localMap i)

theorem parentRestriction_represents (i : Fin c.size) :
    Represents K (b.parentRestriction P i) (P.toMatchingPresentation.preimageLocus i) :=
  (P.localMap_represents i).postcomp_equiv (b.componentEquiv i)

/-- Entire parent restrictions commute through the actual original overlap
maps, by the two geometric comparison equations and the matching equations. -/
theorem parentRestriction_compatible : b.gluingData.MapCompatible (b.parentRestriction P) := by
  intro i j
  change (b.gluingData.leftRestriction i j).comp
      ((b.componentEquiv i).toBoundedAlgHom.comp (P.toMatchingPresentation.localMap i)) =
    (b.gluingData.rightRestriction i j).comp
      ((b.componentEquiv j).toBoundedAlgHom.comp (P.toMatchingPresentation.localMap j))
  rw [← BoundedAlgHom.comp_assoc, b.leftRestriction_compatible,
    BoundedAlgHom.comp_assoc, P.localMap_overlap, ← BoundedAlgHom.comp_assoc,
    ← b.rightRestriction_compatible, BoundedAlgHom.comp_assoc]

/-- Exact abstract parent overlap images transport through the entire
bounded geometric overlap equivalences. -/
theorem parentRestriction_overlap_range (i j : Fin c.size) :
    range (BanachSpectrum.comap
      ((b.gluingData.leftRestriction i j).comp (b.parentRestriction P i)).toBoundedRingHom) =
      range (BanachSpectrum.comap (b.parentRestriction P i).toBoundedRingHom) ∩
        range (BanachSpectrum.comap (b.parentRestriction P j).toBoundedRingHom) := by
  have hm : (b.gluingData.leftRestriction i j).comp (b.parentRestriction P i) =
      (b.overlapEquiv i j).toBoundedAlgHom.comp
        ((d.toPairTransitions.rightRestriction i j).comp (P.toMatchingPresentation.localMap j)) := by
    change (b.gluingData.leftRestriction i j).comp
      ((b.componentEquiv i).toBoundedAlgHom.comp (P.toMatchingPresentation.localMap i)) = _
    rw [← BoundedAlgHom.comp_assoc, b.leftRestriction_compatible,
      BoundedAlgHom.comp_assoc, P.localMap_overlap]
  have hrep := (P.restrictedLocalMap_represents j (F.overlap i j) (F.overlapRight i j)).postcomp_equiv
    (b.overlapEquiv i j)
  rw [hm]
  change range (BanachSpectrum.comap
    ((b.overlapEquiv i j).toBoundedAlgHom.comp
      ((F.localMap j (F.overlap i j) (F.overlapRight i j)).comp
        (P.toMatchingPresentation.localMap j))).toBoundedRingHom) = _
  rw [hrep.2.1, (b.parentRestriction_represents P i).2.1, (b.parentRestriction_represents P j).2.1]
  rfl

/-- The effective output and local geometric comparisons supply every
full algebraic parent datum required by actual finite-chart recognition. -/
def parentData : b.gluingData.ParentData where
  algebra := P.algebra
  restriction := b.parentRestriction P
  represents i := by
    rw [(b.parentRestriction_represents P i).2.1]
    exact b.parentRestriction_represents P i
  compatible := b.parentRestriction_compatible P
  covers x := by
    obtain ⟨i, hi⟩ := P.componentCover.covers x (mem_univ x)
    exact ⟨i, (b.parentRestriction_represents P i).2.1.symm ▸ hi⟩
  overlap_range := b.parentRestriction_overlap_range P

variable [T2Space b.gluingData.locus]

/-- Construct the actual embedded parent chart and entire realization in
the original atlas, from the effective output and local comparisons alone. -/
def affinoidRealization : b.gluingData.AffinoidRealization :=
  (b.parentData P).affinoidRealization

/-- The literal finite union is intrinsically recognized; specialness and
the whole parent-to-recognized bounded equivalence are constructed. -/
def recognizedSubset : a.RecognizedSubset := (b.parentData P).recognizedSubset

def recognitionEquiv : BoundedAlgEquiv K P.algebra (b.recognizedSubset P).algebra :=
  (b.parentData P).recognitionEquiv

end ChartBinding

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent

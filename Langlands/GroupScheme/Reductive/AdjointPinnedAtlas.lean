import Langlands.GroupScheme.Reductive.AdjointPinnedModel
import Langlands.GroupScheme.Reductive.GeometricNontrivial

/-! # Adjoint pinned charts with nontrivial geometric fibres -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- A supplied adjoint pinned model with nontrivial geometric fibres,
identified with an actual étale pullback of the original group scheme. -/
structure AffineAdjointPinnedChart {S : Scheme.{u}} (G : GroupScheme S) where
  model : AffineAdjointPinnedModel.{u}
  map : model.base ⟶ S
  etale : Etale map
  iso : (GroupScheme.baseChange map).obj G ≅ model.group
  nontrivial : IsFibrewiseNontrivial model.group

namespace AffineAdjointPinnedChart

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Every point is covered by an adjoint pinned chart with full integral
root generation and the original geometric nontriviality. -/
theorem exists_over (hG : IsReductive G) (hadj : IsFibrewiseAdjoint G)
    (hnt : IsFibrewiseNontrivial G) (s : S) :
    ∃ C : AffineAdjointPinnedChart G, ∃ x : C.model.base, C.map x = s := by
  obtain ⟨C, x, hx⟩ := AffinePinnedChart.exists_over hG s
  have hspan : C.model.rootDatum.rootSpan ℤ = ⊤ := by
    apply (C.model.isAdjoint_geometricFiber_iff x).mp
    exact (hadj.baseChange C.map x).of_iso
      ((GroupScheme.baseChange (geometricPoint C.model.base x)).mapIso C.iso).symm
  let M : AffineAdjointPinnedModel.{u} :=
    { C.model with rootSpan_eq_top := hspan }
  refine ⟨⟨M, C.map, C.etale, C.iso, ?_⟩, x, hx⟩
  exact (hnt.baseChange C.map).of_iso C.iso

/-- Forgetting the adjoint and nontrivial-fibre conditions gives an
ordinary affine pinned chart. -/
def toAffinePinnedChart (C : AffineAdjointPinnedChart G) : AffinePinnedChart G where
  model := C.model.toAffinePinnedModel
  map := C.map
  etale := C.etale
  iso := C.iso

end AffineAdjointPinnedChart

/-- A point-indexed covering by adjoint pinned charts with nontrivial
geometric fibres and full integral root generation. -/
structure AffineAdjointPinnedAtlas {S : Scheme.{u}} (G : GroupScheme S) where
  chart : S → AffineAdjointPinnedChart G
  point : ∀ s : S, (chart s).model.base
  image_point : ∀ s : S, (chart s).map (point s) = s

namespace AffineAdjointPinnedAtlas

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- Choose a chart above each point using the proved étale local splitting
theorem and the integral adjoint criterion. -/
def ofReductive (hG : IsReductive G) (hadj : IsFibrewiseAdjoint G)
    (hnt : IsFibrewiseNontrivial G) : AffineAdjointPinnedAtlas G where
  chart s := Classical.choose (AffineAdjointPinnedChart.exists_over hG hadj hnt s)
  point s := Classical.choose
    (Classical.choose_spec (AffineAdjointPinnedChart.exists_over hG hadj hnt s))
  image_point s := Classical.choose_spec
    (Classical.choose_spec (AffineAdjointPinnedChart.exists_over hG hadj hnt s))

variable (D : AffineAdjointPinnedAtlas G)

/-- The same family as an ordinary affine pinned atlas. -/
def toAffinePinnedAtlas : AffinePinnedAtlas G where
  chart s := (D.chart s).toAffinePinnedChart
  point := D.point
  image_point := D.image_point

/-- The actual étale covering family. -/
def cover : S.Cover Scheme.etalePrecoverage := D.toAffinePinnedAtlas.cover

/-- The single morphism from the disjoint union of the charts. -/
abbrev projection : D.toAffinePinnedAtlas.space ⟶ S :=
  D.toAffinePinnedAtlas.projection

instance : Etale D.projection := inferInstanceAs (Etale D.toAffinePinnedAtlas.projection)

instance : Surjective D.projection :=
  inferInstanceAs (Surjective D.toAffinePinnedAtlas.projection)

section AffineBase

variable {A : Type u} [CommRing A]
  {H : GroupScheme (Spec (CommRingCat.of A))}
  (D : AffineAdjointPinnedAtlas H)

/-- The ring of a specified chart as an algebra over the original affine base. -/
@[instance_reducible] def chartAlgebra (s : Spec (CommRingCat.of A)) :
    Algebra A (D.chart s).model.ring :=
  (Spec.preimage (D.chart s).map).hom.toAlgebra

/-- The spectrum map of the chart's original algebra structure is precisely
the original chart map. -/
theorem algebraBaseMap_chart (s : Spec (CommRingCat.of A)) :
    letI := D.chartAlgebra s
    algebraBaseMap A (D.chart s).model.ring = (D.chart s).map :=
  Spec.map_preimage _

end AffineBase

end AffineAdjointPinnedAtlas

end Langlands.GroupScheme

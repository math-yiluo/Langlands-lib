import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.SaturatedDomainCorestriction

/-! # Full field points on actual original-chart domains -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open Set CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]

namespace AffinoidAtlasPresentation.FieldPoint

variable {A : AffinoidAtlasPresentation.{u, v, w} K}

/-- Restrict a full field point by retaining its evaluations on exactly the
original charts contained in the domain. -/
def restrictOriginalDomain (p : FieldPoint L A)
    (S : A.atlas.OriginalChartDomain) (hp : p.point ∈ S) :
    FieldPoint L (A.originalDomainPresentation S) where
  point := ⟨p.point, hp⟩
  eval c hc := p.eval c.val (by
    obtain ⟨x, hx⟩ := hc
    exact ⟨x, congrArg Subtype.val hx⟩)
  isChartPoint c hc := by
    obtain ⟨x, hx⟩ := hc
    obtain ⟨s, hs, hn⟩ := p.isChartPoint c.val ⟨x, congrArg Subtype.val hx⟩
    exact ⟨s, Subtype.ext hs, hn⟩
  eval_restriction c d hcd hc :=
    p.eval_restriction c.val d.val
      (A.atlas.chart_subset_of_subspaceSubset S.carrier c d hcd) _

@[simp]
theorem restrictOriginalDomain_point (p : FieldPoint L A)
    (S : A.atlas.OriginalChartDomain) (hp : p.point ∈ S) :
    (p.restrictOriginalDomain S hp).point.val = p.point := rfl

theorem restrictOriginalDomain_eval (p : FieldPoint L A)
    (S : A.atlas.OriginalChartDomain) (hp : p.point ∈ S)
    (c : (A.originalDomainPresentation S).atlas.Index)
    (hc : (p.restrictOriginalDomain S hp).point ∈
      range ((A.originalDomainPresentation S).atlas.chart c))
    (hc' : p.point ∈ range (A.atlas.chart c.val)) :
    (p.restrictOriginalDomain S hp).eval c hc = p.eval c.val hc' := rfl

end AffinoidAtlasPresentation.FieldPoint

namespace SaturatedAtlasPresentation

open AffinoidAtlasPresentation

variable {A : SaturatedAtlasPresentation.{u, v, w} K}

/-- The actual domain inclusion preserves every restricted evaluation. -/
theorem fieldPoint_map_restrictOriginalDomain
    (S : A.presentation.atlas.OriginalChartDomain)
    (p : FieldPoint L A.presentation) (hp : p.point ∈ S) :
    (p.restrictOriginalDomain S hp).map (A.originalDomainInclusion S)
      (A.originalDomain S).hasAllLocalDomains = p := by
  let r := p.restrictOriginalDomain S hp
  refine FieldPoint.ext' rfl fun j hj hj' => ?_
  obtain ⟨c, hc, hcj⟩ := (A.originalDomainInclusion S).exists_admissible_mem
    (A.originalDomain S).hasAllLocalDomains r.point j hj
  rw [r.map_eval (A.originalDomainInclusion S)
    (A.originalDomain S).hasAllLocalDomains j hj c hc hcj]
  exact p.eval_restriction c.val j
    (fun x hx => hcj ⟨⟨x, c.property hx⟩,
      (A.presentation.atlas.range_subspaceChart S.carrier c).symm ▸ hx, rfl⟩) _

/-- Full field points map injectively along the actual domain inclusion. -/
theorem fieldPoint_map_originalDomainInclusion_injective
    (S : A.presentation.atlas.OriginalChartDomain) :
    Function.Injective (fun p : FieldPoint L (A.originalDomain S).presentation =>
      p.map (A.originalDomainInclusion S) (A.originalDomain S).hasAllLocalDomains) := by
  intro p q he
  have hpoint : p.point = q.point :=
    Subtype.ext (congrArg FieldPoint.point he)
  refine FieldPoint.ext' hpoint fun c hc hc' => ?_
  have hadm : (A.originalDomainInclusion S).baseMap ''
      range ((A.originalDomain S).presentation.atlas.chart c) ⊆
        range (A.presentation.atlas.chart c.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hp := p.map_eval (A.originalDomainInclusion S)
    (A.originalDomain S).hasAllLocalDomains c.val
    (hadm ⟨p.point, hc, rfl⟩) c hc hadm
  have hq := q.map_eval (A.originalDomainInclusion S)
    (A.originalDomain S).hasAllLocalDomains c.val
    (hadm ⟨q.point, hc', rfl⟩) c hc' hadm
  have h := FieldPoint.eval_congr he c.val
    (hadm ⟨p.point, hc, rfl⟩) (hadm ⟨q.point, hc', rfl⟩)
  rw [hp, hq] at h
  change (p.eval c hc).comp
      (A.presentation.atlas.restriction c.val c.val _).toAlgHom =
    (q.eval c hc').comp (A.presentation.atlas.restriction c.val c.val _).toAlgHom at h
  rw [A.presentation.atlas.restriction_id] at h
  exact AlgHom.ext (fun a => AlgHom.congr_fun h a)

/-- Full field points of the actual domain correspond to exactly those
ambient full field points whose ordinary point belongs to that domain. -/
def originalDomainFieldPointEquiv
    (S : A.presentation.atlas.OriginalChartDomain) :
    FieldPoint L (A.originalDomain S).presentation ≃
      {p : FieldPoint L A.presentation // p.point ∈ S} where
  toFun p := ⟨p.map (A.originalDomainInclusion S) (A.originalDomain S).hasAllLocalDomains,
    p.point.property⟩
  invFun p := p.val.restrictOriginalDomain S p.property
  left_inv p := by
    apply fieldPoint_map_originalDomainInclusion_injective S
    exact fieldPoint_map_restrictOriginalDomain S _ _
  right_inv p := Subtype.ext (fieldPoint_map_restrictOriginalDomain S p.val p.property)

end SaturatedAtlasPresentation

end Langlands.Analytic

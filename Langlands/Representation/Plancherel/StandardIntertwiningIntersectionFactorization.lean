import Langlands.Analysis.Local.IteratedFactorization
import Langlands.Representation.Plancherel.StandardIntertwiningFactorization

/-! # The intermediate intersection chart and composite normalization -/

noncomputable section

open MeasureTheory MeasureTheory.Measure

namespace Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

universe uG

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {U₀ U₁ U₂ V W : Subgroup G}
  (D : OrderedSubgroupFactorization U₀ U₁ U₂ V W)

include D in
/-- The three literal coordinate maps already force the endpoint intersection
to lie in the middle subgroup. This is not an existence theorem for the maps. -/
theorem intersection_le_middle : U₀ ⊓ U₂ ≤ U₁ := by
  intro g hg
  let g₂ : U₂ := ⟨g, hg.2⟩
  let q := D.second.symm g₂
  let j₁ : U₁ := ⟨q.1.val.val, q.1.property⟩
  let p := D.first.symm j₁
  have hp : p.1.val.val * p.2.val = q.1.val.val := by
    have he := congrArg (fun z : U₁ => z.val) (D.first.apply_symm_apply j₁)
    rw [D.first_eq] at he
    exact he
  have hi₂ : p.1.val.val ∈ U₂ := by
    apply (U₂.mul_mem_cancel_right (D.first_le_target p.2.property)).mp
    rw [hp]
    exact q.1.val.property
  let h₂ : U₀.subgroupOf U₂ := ⟨⟨p.1.val.val, hi₂⟩, p.1.property⟩
  have hq : q.1.val.val * q.2.val = g := by
    have he := congrArg (fun z : U₂ => z.val) (D.second.apply_symm_apply g₂)
    rw [D.second_eq] at he
    exact he
  have he : D.composite (h₂, (p.2, q.2)) =
      D.composite (⟨g₂, hg.1⟩, (1, 1)) := by
    apply Subtype.ext
    rw [D.composite_eq, D.composite_eq]
    change p.1.val.val * (p.2.val * q.2.val) = g * (1 * 1)
    rw [← mul_assoc, hp, hq, one_mul, mul_one]
  have hh := congrArg
    (fun z : (U₀.subgroupOf U₂) × (V × W) => z.1.val.val)
    (D.composite.injective he)
  change p.1.val.val = g at hh
  rw [← hh]
  exact p.1.val.property

private def intersectionFirstDomainHomeomorph
    (h : U₀ ⊓ U₂ ≤ U₁) :
    (U₀.subgroupOf U₂) × V ≃ₜ
      {p : (U₀.subgroupOf U₁) × V // p.1.val.val ∈ U₂} where
  toFun p :=
    ⟨(⟨⟨p.1.val.val, h ⟨p.1.property, p.1.val.property⟩⟩, p.1.property⟩, p.2),
      p.1.val.property⟩
  invFun p := (⟨⟨p.val.1.val.val, p.property⟩, p.val.1.property⟩, p.val.2)
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private def intersectionFirstTargetHomeomorph :
    {g : U₁ // g.val ∈ U₂} ≃ₜ U₁.subgroupOf U₂ where
  toFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
  invFun g := ⟨⟨g.val.val, g.property⟩, g.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Restrict the first literal chart to the intermediate intersection.
The endpoint-intersection inclusion is derived from the existing three maps. -/
def intersectionFirst :
    (U₀.subgroupOf U₂) × V ≃ₜ U₁.subgroupOf U₂ :=
  (intersectionFirstDomainHomeomorph D.intersection_le_middle).trans
    ((D.first.subtype (p := fun p => p.1.val.val ∈ U₂)
      (q := fun g => g.val ∈ U₂) (fun p => by
        rw [D.first_eq]
        exact (U₂.mul_mem_cancel_right (D.first_le_target p.2.property)).symm)).trans
      intersectionFirstTargetHomeomorph)

/-- The restricted chart retains the same literal multiplication in `U₂`. -/
theorem intersectionFirst_eq (p : (U₀.subgroupOf U₂) × V) :
    (D.intersectionFirst p : U₂) =
      p.1.val * Subgroup.inclusion D.first_le_target p.2 := by
  apply Subtype.ext
  exact congrArg (fun z : U₁ => z.val) (D.first_eq _)

/-- The inverse restriction retains the original first chart's second
coordinate, after viewing the intersection element inside `U₁`. -/
@[simp] theorem intersectionFirst_symm_snd (g : U₁.subgroupOf U₂) :
    (D.intersectionFirst.symm g).2 =
      (D.first.symm ⟨g.val.val, g.property⟩).2 := rfl

section Measures

variable [MeasurableSpace U₂]
  [MeasurableSpace (U₀.subgroupOf U₂)]
  [MeasurableSpace (U₁.subgroupOf U₂)]
  [MeasurableSpace V] [MeasurableSpace W]
  {μU₂ : Measure U₂}
  {μI₂₀ : Measure (U₀.subgroupOf U₂)}
  {μI₂₁ : Measure (U₁.subgroupOf U₂)}
  {μV : Measure V} {μW : Measure W}
  [SFinite μI₂₀] [SFinite μV] [SFinite μW]

/-- Exact normalization of the restricted first chart and the second chart
implies the composite normalization. No third product identity is supplied. -/
theorem measurePreserving_composite_of_intersection
    (haμ : MeasurePreserving D.intersectionFirst (μI₂₀.prod μV) μI₂₁)
    (hbμ : MeasurePreserving D.second (μI₂₁.prod μW) μU₂) :
    MeasurePreserving D.composite (μI₂₀.prod (μV.prod μW)) μU₂ := by
  exact QuotientIntegration.measurePreserving_factorProduct_of_iterated
    (U₀.subgroupOf U₂) (U₁.subgroupOf U₂)
    (Subgroup.inclusion D.first_le_target) (Subgroup.inclusion D.second_le)
    D.intersectionFirst D.second D.intersectionFirst_eq D.second_eq
    D.composite D.composite_eq haμ hbμ

end Measures

end Langlands.Plancherel.StandardIntertwining.OrderedSubgroupFactorization

import Langlands.Global.LeftCosetMeasure
import Mathlib.Topology.Covering.Quotient
import Mathlib.Topology.Compactness.Lindelof

/-!
# Borel fundamental domains for discrete subgroups

A discrete subgroup of a second-countable topological group has a Borel
fundamental domain for its left action. The domain works for every ambient measure.
-/

noncomputable section

universe u v

open MeasureTheory Set Topology
open scoped Pointwise

namespace Langlands.Global.LeftCosetSpace

private def firstPatch {X : Type u} {Y : Type v} (f : X → Y) (U : ℕ → Set X) : Set X :=
  ⋃ n, U n \ f ⁻¹' (⋃ m < n, f '' U m)

private theorem mem_firstPatch {X : Type u} {Y : Type v} (f : X → Y) (U : ℕ → Set X)
    (x : X) :
    x ∈ firstPatch f U ↔ ∃ n, x ∈ U n ∧ ∀ m < n, f x ∉ f '' U m := by
  simp only [firstPatch, mem_iUnion, mem_sdiff, mem_preimage, not_exists]

private theorem measurableSet_firstPatch {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [BorelSpace X]
    (f : X → Y) (hf : Continuous f) (hfo : IsOpenMap f)
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) :
    MeasurableSet (firstPatch f U) := by
  apply MeasurableSet.iUnion
  intro n
  exact (hU n).measurableSet.diff
    ((isOpen_iUnion fun m => isOpen_iUnion fun _ => hfo _ (hU m)).preimage hf).measurableSet

private theorem firstPatch_unique {X : Type u} {Y : Type v}
    (f : X → Y) (U : ℕ → Set X) (hUi : ∀ n, (U n).InjOn f)
    (hUc : ∀ x, ∃ n, x ∈ U n) (x : X) :
    ∃! y, y ∈ firstPatch f U ∧ f y = f x := by
  classical
  have hex : ∃ n, f x ∈ f '' U n := by
    obtain ⟨n, hn⟩ := hUc x
    exact ⟨n, x, hn, rfl⟩
  obtain ⟨y, hyU, hyf⟩ := Nat.find_spec hex
  have hyS : y ∈ firstPatch f U := by
    apply (mem_firstPatch f U y).mpr
    refine ⟨Nat.find hex, hyU, ?_⟩
    intro m hm
    rw [hyf]
    exact Nat.find_min hex hm
  refine ⟨y, ⟨hyS, hyf⟩, ?_⟩
  intro z hz
  obtain ⟨n, hzn, hzm⟩ := (mem_firstPatch f U z).mp hz.1
  have hn : n = Nat.find hex := by
    apply le_antisymm
    · by_contra! hlt
      exact hzm _ hlt ⟨y, hyU, hyf.trans hz.2.symm⟩
    · exact Nat.find_min' hex ⟨z, hzn, hz.2⟩
  exact hUi n hzn (hn.symm ▸ hyU) (hz.2.trans hyf.symm)

variable {H : Type u} [Group H] (Γ : Subgroup H)
  [TopologicalSpace H] [IsTopologicalGroup H]

theorem isQuotientCoveringMap_mk (hΓ : IsDiscrete (Γ : Set H)) :
    IsQuotientCoveringMap (mk Γ) Γ :=
  (isQuotientMap_mk Γ).isQuotientCoveringMap_of_subgroup Γ hΓ
    (fun {_ _} => mk_eq_mk_iff Γ _ _)

variable [SecondCountableTopology H]

omit [IsTopologicalGroup H] in
theorem countable_of_isDiscrete (hΓ : IsDiscrete (Γ : Set H)) : Countable Γ := by
  let : DiscreteTopology Γ := SetLike.isDiscrete_iff_discreteTopology.mp hΓ
  exact TopologicalSpace.separableSpace_iff_countable.mp inferInstance

variable [MeasurableSpace H] [BorelSpace H]

/-- A Borel transversal with exactly one group element carrying each point into it. -/
theorem exists_measurable_fundamentalDomain (hΓ : IsDiscrete (Γ : Set H)) :
    ∃ s : Set H, MeasurableSet s ∧ ∀ x : H, ∃! γ : Γ, (γ : H) * x ∈ s := by
  classical
  have hlocal := (isQuotientCoveringMap_mk Γ hΓ).isCoveringMap.isLocalHomeomorph.isLocallyInjective
  choose U hUo hxU hUi using hlocal
  obtain ⟨c, hc⟩ := isLindelof_univ.indexed_countable_subcover U hUo
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  let s := firstPatch (mk Γ) (fun n => U (c n))
  have hs : MeasurableSet s :=
    measurableSet_firstPatch _ (continuous_mk Γ) (isOpenQuotientMap_mk Γ).isOpenMap
      _ (fun n => hUo (c n))
  have huniq (x : H) : ∃! y, y ∈ s ∧ mk Γ y = mk Γ x :=
    firstPatch_unique _ _ (fun n => hUi (c n))
      (fun z => mem_iUnion.mp (hc (mem_univ z))) x
  refine ⟨s, hs, ?_⟩
  intro x
  obtain ⟨y, ⟨hy, hyq⟩, hunique⟩ := huniq x
  have hyΓ : y * x⁻¹ ∈ Γ := (mk_eq_mk_iff Γ x y).mp hyq.symm
  let γ : Γ := ⟨y * x⁻¹, hyΓ⟩
  have hγ : (γ : H) * x = y := by simp [γ, mul_assoc]
  refine ⟨γ, by simpa only [hγ] using hy, ?_⟩
  intro δ hδ
  apply Subtype.ext
  apply mul_right_cancel (b := x)
  rw [hγ]
  exact hunique _ ⟨hδ, mk_subgroup_mul Γ δ x⟩

/-- Choose one Borel fundamental domain, independently of the ambient measure. -/
def fundamentalDomain (hΓ : IsDiscrete (Γ : Set H)) : Set H :=
  (exists_measurable_fundamentalDomain Γ hΓ).choose

theorem measurableSet_fundamentalDomain (hΓ : IsDiscrete (Γ : Set H)) :
    MeasurableSet (fundamentalDomain Γ hΓ) :=
  (exists_measurable_fundamentalDomain Γ hΓ).choose_spec.1

theorem fundamentalDomain_unique (hΓ : IsDiscrete (Γ : Set H)) (x : H) :
    ∃! γ : Γ, (γ : H) * x ∈ fundamentalDomain Γ hΓ :=
  (exists_measurable_fundamentalDomain Γ hΓ).choose_spec.2 x

theorem isFundamentalDomain (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) :
    IsFundamentalDomain Γ (fundamentalDomain Γ hΓ) ν :=
  IsFundamentalDomain.mk' (measurableSet_fundamentalDomain Γ hΓ).nullMeasurableSet
    (fundamentalDomain_unique Γ hΓ)

theorem hasFundamentalDomain (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) :
    HasFundamentalDomain Γ H ν :=
  ⟨⟨fundamentalDomain Γ hΓ, isFundamentalDomain Γ hΓ ν⟩⟩

/-- The actual quotient measure obtained from the chosen Borel fundamental domain. -/
def discreteQuotientMeasure (hΓ : IsDiscrete (Γ : Set H)) (ν : Measure H) :
    Measure (Langlands.Global.LeftCosetSpace Γ) :=
  quotientMeasure Γ ν (fundamentalDomain Γ hΓ)

theorem discreteQuotientMeasure_eq (hΓ : IsDiscrete (Γ : Set H))
    (ν : Measure H) [SMulInvariantMeasure Γ H ν]
    {s : Set H} (hs : IsFundamentalDomain Γ s ν) :
    discreteQuotientMeasure Γ hΓ ν = quotientMeasure Γ ν s := by
  let := countable_of_isDiscrete Γ hΓ
  exact quotientMeasure_eq Γ ν (isFundamentalDomain Γ hΓ ν) hs

theorem discreteQuotientMeasure_compatible (hΓ : IsDiscrete (Γ : Set H))
    (ν : Measure H) [SMulInvariantMeasure Γ H ν] :
    QuotientMeasureEqMeasurePreimage ν (discreteQuotientMeasure Γ hΓ ν) := by
  let := countable_of_isDiscrete Γ hΓ
  exact quotientMeasure_compatible Γ ν (isFundamentalDomain Γ hΓ ν)

theorem measurePreserving_rightTranslate_discrete (hΓ : IsDiscrete (Γ : Set H))
    (ν : Measure H) [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] (g : H) :
    MeasurePreserving (rightTranslate Γ g) (discreteQuotientMeasure Γ hΓ ν)
      (discreteQuotientMeasure Γ hΓ ν) := by
  let := countable_of_isDiscrete Γ hΓ
  exact measurePreserving_rightTranslate Γ ν (isFundamentalDomain Γ hΓ ν) g

end Langlands.Global.LeftCosetSpace

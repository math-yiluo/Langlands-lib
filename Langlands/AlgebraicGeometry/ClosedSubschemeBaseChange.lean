import Langlands.AlgebraicGeometry.ClosedSubschemeFiberIncidence
import Langlands.AlgebraicGeometry.IrreducibleComponentIncidence

/-! # Actual closed-subscheme ranges after surjective and field base change -/

noncomputable section

universe u v

open Set Topology TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.GenericImagePattern

variable {X T : Scheme.{u}}

/-- The actual range of the base change of a morphism into X along p. -/
def baseChangeSubschemeRanges {ι : Type v} (p : T ⟶ X)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (i : ι) : Set T :=
  Set.range (pullback.snd (g i) p)

theorem baseChangeSubschemeRanges_eq_preimage {ι : Type v} (p : T ⟶ X)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (i : ι) :
    baseChangeSubschemeRanges p g i = p ⁻¹' Set.range (g i) :=
  Scheme.Pullback.range_snd _ _

/-- Surjective base change preserves and reflects nonempty intersections. -/
theorem baseChangeSubschemeRanges_incidence_iff {ι : Type v} (p : T ⟶ X)
    [Surjective p] {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (i j : ι) :
    (baseChangeSubschemeRanges p g i ∩ baseChangeSubschemeRanges p g j).Nonempty ↔
      (Set.range (g i) ∩ Set.range (g j)).Nonempty := by
  rw [baseChangeSubschemeRanges_eq_preimage, baseChangeSubschemeRanges_eq_preimage,
    ← Set.preimage_inter]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨p x, hx⟩
  · rintro ⟨x, hx⟩
    obtain ⟨t, rfl⟩ := p.surjective x
    exact ⟨t, hx⟩

/-- An actual cover stays a cover under arbitrary base change. -/
theorem baseChangeSubschemeRanges_cover {ι : Type v} (p : T ⟶ X)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X)
    (hcover : (⋃ i, Set.range (g i)) = Set.univ) :
    (⋃ i, baseChangeSubschemeRanges p g i) = Set.univ := by
  simp only [baseChangeSubschemeRanges_eq_preimage, ← Set.preimage_iUnion, hcover,
    Set.preimage_univ]

/-- Surjective base change also reflects coverage. -/
theorem baseChangeSubschemeRanges_cover_iff {ι : Type v} (p : T ⟶ X)
    [Surjective p] {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) :
    (⋃ i, baseChangeSubschemeRanges p g i) = Set.univ ↔
      (⋃ i, Set.range (g i)) = Set.univ := by
  refine ⟨?_, baseChangeSubschemeRanges_cover p g⟩
  intro hcover
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨t, rfl⟩ := p.surjective x
  have ht : t ∈ ⋃ i, baseChangeSubschemeRanges p g i := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp ht
  exact Set.mem_iUnion.mpr ⟨i, by
    rwa [baseChangeSubschemeRanges_eq_preimage] at hi⟩

/-- The incidence-chain condition is unchanged by surjective base change. -/
theorem baseChangeSubschemeRanges_chainConnected_iff {ι : Type v} (p : T ⟶ X)
    [Surjective p] {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) :
    ComponentIncidence.IntersectionChainConnected (baseChangeSubschemeRanges p g) ↔
      ComponentIncidence.IntersectionChainConnected (fun i => Set.range (g i)) := by
  exact ComponentIncidence.intersectionChainConnected_congr _ _ (Equiv.refl ι)
    (baseChangeSubschemeRanges_incidence_iff p g)

/-- The actual-fibre construction is the same actual base-change-range family. -/
theorem baseChangeSubschemeRanges_fiber {Y : Scheme.{u}} {ι : Type v} (f : X ⟶ Y)
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (y : Y) (i : ι) :
    baseChangeSubschemeRanges (f.fiberι y) g i = fiberSubschemeSets f g y i :=
  range_baseChange_eq_fiberSubschemeSets f g y i

section Field

variable {K L : Type u} [Field K] [Field L]

/-- Every morphism between field spectra is surjective on scheme points. -/
theorem surjective_fieldSpectrumMap (e : Spec (CommRingCat.of L) ⟶
    Spec (CommRingCat.of K)) : Surjective e :=
  ⟨Function.surjective_to_subsingleton e⟩

/-- The actual projection from an arbitrary field base change is surjective. -/
theorem surjective_fieldBaseChange (f : X ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K)) :
    Surjective (pullback.fst f e) := by
  let := surjective_fieldSpectrumMap e
  infer_instance

/-- Actual intersections persist, in both directions, under every field extension.
 No finite-type or separability hypothesis is used. -/
theorem fieldBaseChangeSubschemeRanges_incidence_iff {ι : Type v}
    (f : X ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (i j : ι) :
    (baseChangeSubschemeRanges (pullback.fst f e) g i ∩
      baseChangeSubschemeRanges (pullback.fst f e) g j).Nonempty ↔
      (Set.range (g i) ∩ Set.range (g j)).Nonempty := by
  let := surjective_fieldBaseChange f e
  exact baseChangeSubschemeRanges_incidence_iff _ g i j

/-- Actual coverage is equivalent to coverage after every fixed field extension. -/
theorem fieldBaseChangeSubschemeRanges_cover_iff {ι : Type v}
    (f : X ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) :
    (⋃ i, baseChangeSubschemeRanges (pullback.fst f e) g i) = Set.univ ↔
      (⋃ i, Set.range (g i)) = Set.univ := by
  let := surjective_fieldBaseChange f e
  exact baseChangeSubschemeRanges_cover_iff _ g

end Field

end Langlands.AlgebraicGeometry.GenericImagePattern

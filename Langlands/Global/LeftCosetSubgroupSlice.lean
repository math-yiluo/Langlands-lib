import Langlands.Global.LeftCosetFundamentalDomain

/-! # Subgroup slices of a measurable fundamental domain -/

noncomputable section

namespace Langlands.Global.LeftCosetSpace

open MeasureTheory Set
open scoped ENNReal

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]

/-- The points of a subgroup which carry `g` into `s` by left multiplication. -/
def subgroupSlice (U : Subgroup G) (s : Set G) (g : G) : Set U :=
  {u : U | (u : G) * g ∈ s}

theorem measurableSet_subgroupSlice (U : Subgroup G) {s : Set G}
    (hs : MeasurableSet s) (g : G) :
    MeasurableSet (subgroupSlice U s g) :=
  (measurable_subtype_coe.mul_const g) hs

omit [MeasurableSpace G] [MeasurableMul G] in
/-- A transversal for a subgroup contained in `U` cuts every `U`-orbit in a
transversal for the corresponding subgroup of `U`. -/
theorem subgroupSlice_unique (Γ U : Subgroup G) (hΓU : Γ ≤ U)
    {s : Set G} (hs : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s) (g : G) (u : U) :
    ∃! γ : Γ.comap U.subtype, γ • u ∈ subgroupSlice U s g := by
  obtain ⟨γ, hγ, huniq⟩ := hs ((u : G) * g)
  let δ : Γ.comap U.subtype := ⟨⟨γ, hΓU γ.property⟩, γ.property⟩
  refine ⟨δ, ?_, ?_⟩
  · change (γ : G) * (u : G) * g ∈ s
    rwa [mul_assoc]
  · intro η hη
    have he : (⟨((η : U) : G), η.property⟩ : Γ) = γ := by
      apply huniq
      change (((η : U) : G) * (u : G)) * g ∈ s at hη
      simpa only [mul_assoc] using hη
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : Γ => (z : G)) he

theorem isFundamentalDomain_subgroupSlice (Γ U : Subgroup G) (hΓU : Γ ≤ U)
    {s : Set G} (hs : MeasurableSet s)
    (huniq : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s) (g : G) (ν : Measure U) :
    IsFundamentalDomain (Γ.comap U.subtype) (subgroupSlice U s g) ν :=
  IsFundamentalDomain.mk' (measurableSet_subgroupSlice U hs g).nullMeasurableSet
    (subgroupSlice_unique Γ U hΓU huniq g)

/-- Every subgroup slice has the same mass as any fundamental domain in `U`.
This holds for any left invariant measure on `U`, without a finite-mass premise. -/
theorem measure_subgroupSlice (Γ U : Subgroup G) (hΓU : Γ ≤ U)
    [Countable (Γ.comap U.subtype)] [MeasurableMul U]
    {s : Set G} (hs : MeasurableSet s)
    (huniq : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s)
    (ν : Measure U) [ν.IsMulLeftInvariant] {t : Set U}
    (ht : IsFundamentalDomain (Γ.comap U.subtype) t ν) (g : G) :
    ν (subgroupSlice U s g) = ν t :=
  (isFundamentalDomain_subgroupSlice Γ U hΓU hs huniq g ν).measure_eq ht

/-- Integrating the indicator of an ambient transversal against a left-`U`
invariant nonnegative function gives the subgroup covolume times its value. -/
theorem lintegral_subgroupSlice_indicator (Γ U : Subgroup G) (hΓU : Γ ≤ U)
    [Countable (Γ.comap U.subtype)] [MeasurableMul U]
    {s : Set G} (hs : MeasurableSet s)
    (huniq : ∀ g : G, ∃! γ : Γ, (γ : G) * g ∈ s)
    (ν : Measure U) [ν.IsMulLeftInvariant] {t : Set U}
    (ht : IsFundamentalDomain (Γ.comap U.subtype) t ν)
    (f : G → ℝ≥0∞) (hf : ∀ (u : U) (g : G), f ((u : G) * g) = f g)
    (g : G) :
    ∫⁻ u : U, s.indicator f ((u : G) * g) ∂ν = ν t * f g := by
  have heq : (fun u : U => s.indicator f ((u : G) * g)) =
      (subgroupSlice U s g).indicator (fun _ => f g) := by
    funext u
    by_cases hu : (u : G) * g ∈ s
    · rw [indicator_of_mem hu,
        indicator_of_mem (show u ∈ subgroupSlice U s g from hu), hf]
    · rw [indicator_of_notMem hu,
        indicator_of_notMem (show u ∉ subgroupSlice U s g from hu)]
  rw [heq, lintegral_indicator (measurableSet_subgroupSlice U hs g), lintegral_const,
    Measure.restrict_apply_univ, measure_subgroupSlice Γ U hΓU hs huniq ν ht g]
  exact mul_comm _ _

end Langlands.Global.LeftCosetSpace

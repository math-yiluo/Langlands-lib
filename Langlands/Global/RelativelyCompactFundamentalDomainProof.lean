import Langlands.Global.RelativelyCompactFundamentalDomainStatement

noncomputable section

universe u v

open MeasureTheory Set Topology

namespace Langlands.Global.LeftCosetSpace

private def firstPatchIn {X : Type u} {Y : Type v} (f : X → Y)
    (U : ℕ → Set X) : Set X :=
  ⋃ n, U n \ f ⁻¹' (⋃ m < n, f '' U m)

private theorem mem_firstPatchIn {X : Type u} {Y : Type v} (f : X → Y)
    (U : ℕ → Set X) (x : X) :
    x ∈ firstPatchIn f U ↔ ∃ n, x ∈ U n ∧ ∀ m < n, f x ∉ f '' U m := by
  simp only [firstPatchIn, mem_iUnion, mem_sdiff, mem_preimage, not_exists]

private theorem measurableSet_firstPatchIn {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace X] [BorelSpace X]
    (f : X → Y) (hf : Continuous f) (hfo : IsOpenMap f)
    (U : ℕ → Set X) (hU : ∀ n, IsOpen (U n)) :
    MeasurableSet (firstPatchIn f U) := by
  apply MeasurableSet.iUnion
  intro n
  exact (hU n).measurableSet.diff
    ((isOpen_iUnion fun m => isOpen_iUnion fun _ => hfo _ (hU m)).preimage hf).measurableSet

private theorem firstPatchIn_unique {X : Type u} {Y : Type v}
    (f : X → Y) (U : ℕ → Set X) (hUi : ∀ n, (U n).InjOn f)
    (hUc : ∀ x, ∃ n, f x ∈ f '' U n) (x : X) :
    ∃! y, y ∈ firstPatchIn f U ∧ f y = f x := by
  classical
  have hex := hUc x
  obtain ⟨y, hyU, hyf⟩ := Nat.find_spec hex
  have hyS : y ∈ firstPatchIn f U := by
    apply (mem_firstPatchIn f U y).mpr
    refine ⟨Nat.find hex, hyU, ?_⟩
    intro m hm
    rw [hyf]
    exact Nat.find_min hex hm
  refine ⟨y, ⟨hyS, hyf⟩, ?_⟩
  intro z hz
  obtain ⟨n, hzn, hzm⟩ := (mem_firstPatchIn f U z).mp hz.1
  have hn : n = Nat.find hex := by
    apply le_antisymm
    · by_contra! hlt
      exact hzm _ hlt ⟨y, hyU, hyf.trans hz.2.symm⟩
    · exact Nat.find_min' hex ⟨z, hzn, hz.2⟩
  exact hUi n hzn (hn.symm ▸ hyU) (hz.2.trans hyf.symm)

/-- Choose a Borel transversal inside any open set which meets every orbit. -/
theorem exists_measurable_fundamentalDomain_subset_open
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    (Γ : Subgroup H) (hΓ : IsDiscrete (Γ : Set H))
    (V : Set H) (hVo : IsOpen V)
    (hcover : ∀ x : H, ∃ γ : Γ, (γ : H) * x ∈ V) :
    ∃ s : Set H, MeasurableSet s ∧ s ⊆ V ∧
      ∀ x : H, ∃! γ : Γ, (γ : H) * x ∈ s := by
  classical
  have hlocal := (isQuotientCoveringMap_mk Γ hΓ).isCoveringMap.isLocalHomeomorph.isLocallyInjective
  choose U hUo hxU hUi using hlocal
  obtain ⟨c, hc⟩ := isLindelof_univ.indexed_countable_subcover U hUo
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  let W : ℕ → Set H := fun n => U (c n) ∩ V
  let s := firstPatchIn (mk Γ) W
  have hs : MeasurableSet s :=
    measurableSet_firstPatchIn _ (continuous_mk Γ) (isOpenQuotientMap_mk Γ).isOpenMap
      _ (fun n => (hUo (c n)).inter hVo)
  have hsV : s ⊆ V := by
    intro x hx
    obtain ⟨n, hn, _⟩ := (mem_firstPatchIn _ W x).mp hx
    exact hn.2
  have hqcover (x : H) : ∃ n, mk Γ x ∈ mk Γ '' W n := by
    obtain ⟨γ, hγ⟩ := hcover x
    obtain ⟨n, hn⟩ := mem_iUnion.mp (hc (mem_univ ((γ : H) * x)))
    exact ⟨n, (γ : H) * x, ⟨hn, hγ⟩, mk_subgroup_mul Γ γ x⟩
  have huniq (x : H) : ∃! y, y ∈ s ∧ mk Γ y = mk Γ x :=
    firstPatchIn_unique _ W (fun n => (hUi (c n)).mono inter_subset_left) hqcover x
  refine ⟨s, hs, hsV, ?_⟩
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

theorem relativelyCompactFundamentalDomain :
    RelativelyCompactFundamentalDomainStatement.{u} := by
  intro H _ _ _ _ _ _ _ _ Γ hΓ K hK hcover
  obtain ⟨V, hVo, hKV, _, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  obtain ⟨s, hs, hsV, huniq⟩ :=
    exists_measurable_fundamentalDomain_subset_open Γ hΓ V hVo
      (fun x => by
        obtain ⟨γ, hγ⟩ := hcover x
        exact ⟨γ, hKV hγ⟩)
  have hsc : IsCompact (closure s) :=
    hVc.of_isClosed_subset isClosed_closure (closure_mono hsV)
  have hfd (ν : Measure H) : IsFundamentalDomain Γ s ν :=
    IsFundamentalDomain.mk' hs.nullMeasurableSet huniq
  have hfinite (ν : Measure H) [IsFiniteMeasureOnCompacts ν] : ν s < ⊤ :=
    lt_of_le_of_lt (measure_mono subset_closure) hsc.measure_lt_top
  refine ⟨s, hs, hsc, huniq, hfd, ?_, hfinite, ?_⟩
  · intro ν _
    rw [discreteQuotientMeasure_eq Γ hΓ ν (hfd ν)]
    exact measurePreserving_mk Γ ν s
  · intro ν _ _ hν
    let := countable_of_isDiscrete Γ hΓ
    have hzero := IsFundamentalDomain.measure_ne_zero hν (hfd ν)
    exact ⟨isProbabilityMeasure_normalizedMeasure Γ ν s hzero (hfinite ν).ne,
      normalizedMeasure_eq Γ ν (hfd ν) (isFundamentalDomain Γ hΓ ν)⟩

end Langlands.Global.LeftCosetSpace

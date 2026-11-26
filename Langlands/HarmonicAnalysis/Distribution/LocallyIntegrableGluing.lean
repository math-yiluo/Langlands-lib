import Langlands.HarmonicAnalysis.Distribution.Haar
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Order.Disjointed
import Mathlib.Topology.Separation.Regular

/-! # Gluing locally integrable densities for distributions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.Distribution

open Function Set Filter MeasureTheory TopologicalSpace
open scoped Topology

/-- A common local density for several distributions and measures on the same space can
be chosen globally. Local constancy at a prescribed set of points is preserved. -/
def LocallyIntegrableDensityGluingStatement.{u, w} : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X]
    [TotallyDisconnectedSpace X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {ι : Type w} (μ : ι → Measure X) (D : ι → Distribution X) (R : Set X),
    (∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ ∃ θ : X → ℂ,
      (∀ j, LocallyIntegrableOn θ U (μ j) ∧
        ∀ f : SchwartzBruhat X, support (f : X → ℂ) ⊆ U →
          D j f = ∫ y, f y * θ y ∂μ j) ∧
      ∀ y ∈ U ∩ R, ∀ᶠ z in 𝓝 y, θ z = θ y) →
    ∃ Θ : X → ℂ,
      (∀ j, LocallyIntegrable Θ (μ j) ∧
        ∀ f : SchwartzBruhat X, D j f = ∫ y, f y * Θ y ∂μ j) ∧
      ∀ y ∈ R, ∀ᶠ z in 𝓝 y, Θ z = Θ y

theorem exists_locallyIntegrableDensity_of_locally.{u, w} :
    LocallyIntegrableDensityGluingStatement.{u, w} := by
  intro X _ _ _ _ _ _ _ ι μ D R hlocal
  classical
  by_cases hX : Nonempty X
  · obtain ⟨x₀⟩ := hX
    choose U hU hxU θ hd hreg using hlocal
    have hclopen (x : X) : ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U x :=
      isTopologicalBasis_isClopen.mem_nhds_iff.mp ((hU x).mem_nhds (hxU x))
    choose V hV hxV hVU using hclopen
    obtain ⟨T, hTcount, hT⟩ := isOpen_iUnion_countable V (fun x => (hV x).isOpen)
    obtain ⟨p, hp⟩ := (hTcount.insert x₀).exists_eq_range ⟨x₀, mem_insert _ _⟩
    let W (i : ℕ) := V (p i)
    have hW : (⋃ i, W i) = univ := by
      apply eq_univ_of_forall
      intro x
      have hx : x ∈ ⋃ i ∈ T, V i := by rw [hT]; exact mem_iUnion_of_mem x (hxV x)
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      have hi' : i ∈ range p := by rw [← hp]; exact mem_insert_of_mem _ hi
      obtain ⟨n, rfl⟩ := hi'
      exact mem_iUnion_of_mem n hxi
    let P := disjointed W
    have hP (i : ℕ) : IsClopen (P i) := by
      exact disjointedRec (f := W) (p := IsClopen) (fun {_ j} ht => ht.diff (hV (p j)))
        (hV (p i))
    have hcover (x : X) : ∃ i, x ∈ P i := by
      rw [← mem_iUnion]
      change x ∈ ⋃ i, disjointed W i
      rw [iUnion_disjointed, hW]
      exact mem_univ x
    have hsub (i : ℕ) : P i ⊆ U (p i) := (disjointed_subset W i).trans (hVU (p i))
    let Θ (x : X) := θ (p (hcover x).choose) x
    have hΘ (i : ℕ) : EqOn Θ (θ (p i)) (P i) := by
      intro x hx
      have heq : (hcover x).choose = i := by
        by_contra hne
        exact Set.disjoint_left.mp (disjoint_disjointed W hne) (hcover x).choose_spec hx
      simp only [Θ, heq]
    have hnear (x : X) : ∃ i : ℕ, x ∈ P i ∧ Θ =ᶠ[𝓝 x] θ (p i) := by
      obtain ⟨i, hi⟩ := hcover x
      have hmem : ∀ᶠ z in 𝓝 x, z ∈ P i := (hP i).isOpen.mem_nhds hi
      exact ⟨i, hi, hmem.mono (hΘ i)⟩
    have hli (j : ι) : LocallyIntegrable Θ (μ j) := by
      intro x
      obtain ⟨i, hi⟩ := hcover x
      have hx := hsub i hi
      have hint := (hd (p i) j).1 x hx
      rw [(hU (p i)).nhdsWithin_eq hx] at hint
      obtain ⟨s, hs, hθs⟩ := hint
      obtain ⟨t, hts, ht, hxt⟩ := mem_nhds_iff.mp hs
      refine ⟨t ∩ P i, (ht.inter (hP i).isOpen).mem_nhds ⟨hxt, hi⟩, ?_⟩
      exact (hθs.mono_set (inter_subset_left.trans hts)).congr_fun
        (fun y hy => (hΘ i hy.2).symm) (ht.inter (hP i).isOpen).measurableSet
    refine ⟨Θ, fun j => ⟨hli j, ?_⟩, ?_⟩
    · intro f
      obtain ⟨s, hs⟩ := (Hecke.TestFunction.isCompact_support f).elim_finite_subcover P
        (fun i => (hP i).isOpen) (by intro x _; exact mem_iUnion.mpr (hcover x))
      let cut (i : ℕ) := multiplyTest (LocallyConstant.charFn ℂ (hP i)) f
      have hcut (i : ℕ) (x : X) : cut i x = if x ∈ P i then f x else 0 := by
        change (P i).indicator (fun _ => (1 : ℂ)) x * f x = _
        split_ifs with hx <;> simp [hx]
      have hf : (∑ i ∈ s, cut i) = f := by
        ext x
        rw [Submodule.coe_sum, Finset.sum_apply]
        by_cases hfx : f x = 0
        · simp [hcut, hfx]
        · obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp (hs hfx)
          rw [Finset.sum_eq_single_of_mem i hi, hcut, ite_eq_left hxi]
          intro j _ hji
          rw [hcut, ite_eq_right fun hxj => Set.disjoint_left.mp (disjoint_disjointed W hji) hxj hxi]
      have hvalue (i : ℕ) : D j (cut i) = ∫ x, cut i x * Θ x ∂μ j := by
        rw [(hd (p i) j).2 (cut i) (by
          intro x hx
          apply hsub i
          by_contra hnot
          exact hx (by rw [hcut, ite_eq_right hnot]))]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        change cut i x * θ (p i) x = cut i x * Θ x
        by_cases hx : x ∈ P i
        · rw [hΘ i hx]
        · simp [hcut, hx]
      calc
        D j f = ∑ i ∈ s, D j (cut i) := by rw [← map_sum, hf]
        _ = ∑ i ∈ s, ∫ x, cut i x * Θ x ∂μ j := Finset.sum_congr rfl fun i _ => hvalue i
        _ = ∫ x, f x * Θ x ∂μ j := by
          have hint (i : ℕ) : Integrable (fun x => cut i x * Θ x) (μ j) := by
            simpa only [smul_eq_mul] using
              (hli j).integrable_smul_left_of_hasCompactSupport (cut i).continuous
                (cut i).hasCompactSupport
          rw [← integral_finsetSum s (fun i _ => hint i)]
          refine integral_congr_ae (Eventually.of_forall fun x => ?_)
          change (∑ i ∈ s, cut i x * Θ x) = f x * Θ x
          rw [← Finset.sum_mul, ← Finset.sum_apply, ← Submodule.coe_sum, hf]
    · intro y hy
      obtain ⟨i, hi, heq⟩ := hnear y
      filter_upwards [heq, hreg (p i) y ⟨hsub i hi, hy⟩] with z hz hx
      rw [hz, hx, hΘ i hi]
  · have : IsEmpty X := not_nonempty_iff.mp hX
    refine ⟨0, fun j => ⟨locallyIntegrable_zero, fun f => ?_⟩, fun y => isEmptyElim y⟩
    have hf : f = 0 := by ext x; exact isEmptyElim x
    simp [hf]

end Langlands.HarmonicAnalysis.Distribution

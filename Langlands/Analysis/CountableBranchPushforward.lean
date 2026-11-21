import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Compactness.Lindelof

/-! # Pushforward through countably many measurable branches -/

namespace Langlands.Analysis

open Set MeasureTheory
open scoped ENNReal

variable {X Y : Type*}

private theorem fiberCard_eq_tsum (p : X → Y) (V : ℕ → Set X)
    (hcover : ⋃ i, V i = univ) (hd : Pairwise fun i j => Disjoint (V i) (V j))
    (hinj : ∀ i, InjOn p (V i)) (y : Y) :
    (ENat.card {x // p x = y} : ℝ≥0∞) =
      ∑' i, (p '' V i).indicator (fun _ => (1 : ℝ≥0∞)) y := by
  classical
  let I : Set ℕ := {i | y ∈ p '' V i}
  have hmem (x : X) : ∃ i, x ∈ V i := mem_iUnion.mp (hcover ▸ mem_univ x)
  let index (x : X) : ℕ := (hmem x).choose
  have hindex (x : X) : x ∈ V (index x) := (hmem x).choose_spec
  let toIndex : {x // p x = y} → I :=
    fun x => ⟨index x.val, x.val, hindex x.val, x.property⟩
  have heq (x : X) {i : ℕ} (hi : x ∈ V i) : index x = i := by
    by_contra h
    exact disjoint_left.mp (hd h) (hindex x) hi
  have hbij : Function.Bijective toIndex := by
    constructor
    · intro x z hxz
      have hi : index x.val = index z.val := congrArg Subtype.val hxz
      exact Subtype.ext (hinj (index x.val) (hindex x.val) (hi.symm ▸ hindex z.val)
        (x.property.trans z.property.symm))
    · intro i
      obtain ⟨x, hx, hp⟩ := i.property
      exact ⟨⟨x, hp⟩, Subtype.ext (heq x hx)⟩
  calc
    (ENat.card {x // p x = y} : ℝ≥0∞) = (ENat.card I : ℝ≥0∞) := by
      rw [ENat.card_congr (Equiv.ofBijective toIndex hbij)]
    _ = ∑' _ : I, (1 : ℝ≥0∞) := ENNReal.tsum_one.symm
    _ = ∑' i, (p '' V i).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      rw [tsum_subtype I (fun _ : ℕ => (1 : ℝ≥0∞))]
      apply tsum_congr
      intro i
      by_cases hi : y ∈ p '' V i
      · rw [indicator_of_mem (show i ∈ I from hi), indicator_of_mem hi]
      · rw [indicator_of_notMem (show i ∉ I from hi), indicator_of_notMem hi]

variable [MeasurableSpace X] [MeasurableSpace Y]
  (p : X → Y) (μ : Measure X) (ν : Measure Y) (U : ℕ → Set X)

private theorem measurableSet_image_of_subset_branch (i : ℕ)
    (hbranch : MeasurableEmbedding (fun x : U i => p x.val)) {s : Set X}
    (hs : MeasurableSet s) (hsub : s ⊆ U i) : MeasurableSet (p '' s) := by
  have hpre : MeasurableSet ((Subtype.val : U i → X) ⁻¹' s) := measurable_subtype_coe hs
  convert hbranch.measurableSet_image.mpr hpre using 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hsub hx⟩, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.val, hx, rfl⟩

/-- A countable cover by measure-preserving measurable branches gives a pushforward
whose density is the cardinality of the fiber. -/
theorem map_eq_withDensity_fiberCard (hp : Measurable p)
    (hcover : ⋃ i, U i = univ) (hU : ∀ i, MeasurableSet (U i))
    (hbranch : ∀ i, MeasurableEmbedding (fun x : U i => p x.val))
    (hmap : ∀ i, (μ.restrict (U i)).map p = ν.restrict (p '' U i)) :
    μ.map p = ν.withDensity (fun y => (ENat.card {x // p x = y} : ℝ≥0∞)) := by
  let V := disjointed U
  have hV i : MeasurableSet (V i) := MeasurableSet.disjointed hU i
  have hcoverV : ⋃ i, V i = univ := iUnion_disjointed.trans hcover
  have hsub (i : ℕ) : V i ⊆ U i := disjointed_subset U i
  have hinj (i : ℕ) : InjOn p (U i) := by
    intro x hx z hz heq
    have h : (⟨x, hx⟩ : U i) = ⟨z, hz⟩ := (hbranch i).injective heq
    exact congrArg Subtype.val h
  have himage i : MeasurableSet (p '' V i) :=
    measurableSet_image_of_subset_branch p U i (hbranch i) (hV i) (hsub i)
  have hmapV (i : ℕ) : (μ.restrict (V i)).map p = ν.restrict (p '' V i) := by
    have heq : p ⁻¹' (p '' V i) ∩ U i = V i := by
      ext x
      constructor
      · rintro ⟨⟨z, hz, hzx⟩, hx⟩
        exact hinj i (hsub i hz) hx hzx ▸ hz
      · intro hx
        exact ⟨⟨x, hx, rfl⟩, hsub i hx⟩
    calc
      (μ.restrict (V i)).map p = ((μ.restrict (U i)).map p).restrict (p '' V i) := by
        rw [Measure.restrict_map hp (himage i), Measure.restrict_restrict (hp (himage i)), heq]
      _ = ν.restrict (p '' V i) := by
        rw [hmap i, Measure.restrict_restrict_of_subset (image_mono (hsub i))]
  have hdensity : (fun y => (ENat.card {x // p x = y} : ℝ≥0∞)) =
      ∑' i, (p '' V i).indicator (fun _ => (1 : ℝ≥0∞)) := by
    funext y
    rw [Pi.tsum_apply (Pi.summable.2 fun _ => ENNReal.summable)]
    exact fiberCard_eq_tsum p V hcoverV (disjoint_disjointed U)
      (fun i => (hinj i).mono (hsub i)) y
  have hsum : Measure.sum (fun i => μ.restrict (V i)) = μ := by
    rw [← Measure.restrict_iUnion (disjoint_disjointed U) hV, hcoverV, Measure.restrict_univ]
  calc
    μ.map p = (Measure.sum (fun i => μ.restrict (V i))).map p := by rw [hsum]
    _ = Measure.sum (fun i => (μ.restrict (V i)).map p) := Measure.map_sum hp.aemeasurable
    _ = Measure.sum (fun i => ν.restrict (p '' V i)) := by simp only [hmapV]
    _ = ν.withDensity (fun y => (ENat.card {x // p x = y} : ℝ≥0∞)) := by
      rw [hdensity, withDensity_tsum (fun i => measurable_const.indicator (himage i))]
      congr 1
      funext i
      exact (withDensity_indicator_one (himage i)).symm

/-- A map of constant positive finite multiplicity pushes the measure forward to
the corresponding multiple of the target measure on its image. -/
theorem map_eq_smul_restrict_range (hp : Measurable p)
    (hcover : ⋃ i, U i = univ) (hU : ∀ i, MeasurableSet (U i))
    (hbranch : ∀ i, MeasurableEmbedding (fun x : U i => p x.val))
    (hmap : ∀ i, (μ.restrict (U i)).map p = ν.restrict (p '' U i))
    {d : ℕ} (hd : 0 < d) (hfiber : ∀ y ∈ range p, Nat.card {x // p x = y} = d) :
    μ.map p = (d : ℝ≥0∞) • ν.restrict (range p) := by
  have hrange : MeasurableSet (range p) := by
    have h : (⋃ i, p '' U i) = range p := by rw [← image_iUnion, hcover, image_univ]
    rw [← h]
    exact MeasurableSet.iUnion fun i =>
      measurableSet_image_of_subset_branch p U i (hbranch i) (hU i) Subset.rfl
  have hcard : (fun y => (ENat.card {x // p x = y} : ℝ≥0∞)) =
      (range p).indicator (fun _ => (d : ℝ≥0∞)) := by
    funext y
    by_cases hy : y ∈ range p
    · have : Finite {x // p x = y} :=
        (Nat.card_pos_iff.mp (hfiber y hy ▸ hd)).2
      rw [indicator_of_mem hy, ENat.card_eq_coe_natCard, hfiber y hy]
      rfl
    · have hzero : ENat.card {x // p x = y} = 0 :=
        (ENat.card_eq_zero_iff_empty _).mpr ⟨fun x => hy ⟨x.val, x.property⟩⟩
      simp [hy, hzero]
  rw [map_eq_withDensity_fiberCard p μ ν U hp hcover hU hbranch hmap, hcard,
    withDensity_indicator hrange, withDensity_const]

/-- An open cover on which the pushforward identities hold can be reduced to
countably many branches when the source is Lindelöf. -/
theorem map_eq_smul_restrict_range_of_locally [TopologicalSpace X] [OpensMeasurableSpace X]
    [LindelofSpace X] (hp : Measurable p)
    (hlocal : ∀ x : X, ∃ s : Set X, x ∈ s ∧ IsOpen s ∧
      MeasurableEmbedding (fun z : s => p z.val) ∧
      (μ.restrict s).map p = ν.restrict (p '' s))
    {d : ℕ} (hd : 0 < d) (hfiber : ∀ y ∈ range p, Nat.card {x // p x = y} = d) :
    μ.map p = (d : ℝ≥0∞) • ν.restrict (range p) := by
  classical
  rcases isEmpty_or_nonempty X with hX | ⟨⟨x₀⟩⟩
  · simp [Measure.eq_zero_of_isEmpty μ, Set.range_eq_empty p]
  choose s hmem hopen hbranch hmap using hlocal
  have hcover : univ ⊆ ⋃ x, s x := fun x _ => mem_iUnion.mpr ⟨x, hmem x⟩
  obtain ⟨r, hr, hsub⟩ := isLindelof_univ.elim_countable_subcover s hopen hcover
  have hr' : (insert x₀ r).Countable := hr.insert x₀
  obtain ⟨a, ha⟩ := Set.Countable.exists_eq_range hr' (insert_nonempty x₀ r)
  have hcover' : ⋃ i, s (a i) = univ := by
    refine eq_univ_of_univ_subset fun x hx => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (hsub hx)
    obtain ⟨hir, hxs⟩ := mem_iUnion.mp hi
    obtain ⟨j, rfl⟩ := show i ∈ range a from ha ▸ mem_insert_of_mem x₀ hir
    exact mem_iUnion.mpr ⟨j, hxs⟩
  exact map_eq_smul_restrict_range p μ ν (s ∘ a) hp hcover'
    (fun i => (hopen (a i)).measurableSet) (fun i => hbranch (a i))
    (fun i => hmap (a i)) hd hfiber

/-- The fiber-density formula for a countable cover by measurable embeddings
with the indicated local pushforward identities. -/
def CountableBranchPushforwardStatement.{u, v} : Prop :=
  ∀ {X : Type u} {Y : Type v} [MeasurableSpace X] [MeasurableSpace Y]
    (p : X → Y) (μ : Measure X) (ν : Measure Y) (U : ℕ → Set X),
    Measurable p →
    (⋃ i, U i = univ) →
    (∀ i, MeasurableSet (U i)) →
    (∀ i, MeasurableEmbedding (fun x : U i => p x.val)) →
    (∀ i, (μ.restrict (U i)).map p = ν.restrict (p '' U i)) →
    μ.map p = ν.withDensity (fun y => (ENat.card {x // p x = y} : ℝ≥0∞))

/-- The general fiber-density statement follows by disjointifying the cover. -/
theorem countableBranchPushforward : CountableBranchPushforwardStatement.{u, v} := by
  intro X Y mX mY p μ ν U
  exact map_eq_withDensity_fiberCard p μ ν U

end Langlands.Analysis

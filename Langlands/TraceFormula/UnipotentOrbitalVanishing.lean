import Langlands.TraceFormula.TwistedOrbital
import Langlands.BaseChange.RegularTransferMeasures
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Twisted orbital integrals that vanish along a unipotent subgroup

For a Hausdorff σ-compact topological group `G` with a compact open subgroup, a continuous
twist `θ`, a point `δ` with twisted centralizer `H`, and a closed subgroup `U` normalized by
`H`, the twisted orbital integral of a continuous compactly supported `f` vanishes as soon as
`∫_U f(x⁻¹ u⁻¹ δ θ(u) θ(x)) du = 0` for every `x`, provided `u ↦ u⁻¹ δ θ(u)` is proper on `U`
and the elements of `H` lying in `U · C` lie in a compact set, for every compact `C`
(`twistedOrbitalIntegral_eq_zero_of_unipotent`).

The proof uses only the defining properties of a compatible quotient measure
(`QuotientIntegration.IsCompatible`). It goes through:

* `integral_eq_zero_of_integral_subgroup_eq_zero`: a continuous compactly supported function
  on `G` whose integrals over all left `U`-cosets vanish has integral `0` (Fubini against a
  cutoff `β` with `∫_U β(u⁻¹ x) du = 1` on the support);
* cutoffs `α_W = 1_{U W} / μ_H {t | t x ∈ U W}` for compact open `W`, left `U`-invariant, with
  `H`-averages the indicator of `H U W`;
* `h = α_W · f(x⁻¹ δ θ x)` is continuous with compact support, its integrals over left
  `U`-cosets vanish, and its `H`-average is the indicator of `H U W` times the orbit function;
* the Weil formula gives `∫ 1_{H U W} · F dν = 0` with `F` the twisted orbit function of `f`,
  and dominated convergence along an exhaustion of `G` by such `W` gives `∫ F dν = 0`.

See the paired Markdown for the origin of the argument.
-/

noncomputable section

namespace Langlands.TraceFormula

open MeasureTheory MeasureTheory.Measure Filter Topology Set
open scoped Pointwise ENNReal
open Langlands.QuotientIntegration

universe uG uΘ

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section LocallyConstant

/-- A function on `G` that is invariant under right translation by an open subgroup is
continuous: it is constant on the open neighbourhood `x K` of every point `x`. -/
theorem continuous_of_forall_mul_mem_eq {X : Type*} [TopologicalSpace X] (K : OpenSubgroup G)
    {a : G → X} (ha : ∀ x, ∀ k ∈ K, a (x * k) = a x) : Continuous a := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hmem : (fun k : G => x * k) '' (K : Set G) ∈ 𝓝 x :=
    ((isOpenMap_mul_left x) _ K.isOpen).mem_nhds ⟨1, K.one_mem, mul_one x⟩
  refine (continuousAt_const (y := a x)).congr ?_
  filter_upwards [hmem] with y hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact (ha x k hk).symm

end LocallyConstant

section Sets

omit [IsTopologicalGroup G] in
/-- Right multiplication by an element of `K` preserves `C * K`. -/
theorem mul_mem_mul_openSubgroup_iff (C : Set G) (K : OpenSubgroup G) (y : G) {k : G}
    (hk : k ∈ K) : y * k ∈ C * (K : Set G) ↔ y ∈ C * (K : Set G) := by
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨c, hc, k', hk', hck⟩
    refine ⟨c, hc, k' * k⁻¹, K.mul_mem hk' (K.inv_mem hk), ?_⟩
    rw [← mul_assoc, hck, mul_inv_cancel_right]
  · rintro ⟨c, hc, k', hk', rfl⟩
    exact ⟨c, hc, k' * k, K.mul_mem hk' hk, (mul_assoc c k' k).symm⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Left multiplication by an element of `U` preserves `U * W`. -/
theorem mul_mem_subgroup_mul_iff (U : Subgroup G) (W : Set G) {u : G} (hu : u ∈ U) (y : G) :
    u * y ∈ (U : Set G) * W ↔ y ∈ (U : Set G) * W := by
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨v, hv, w, hw, hvw⟩
    refine ⟨u⁻¹ * v, U.mul_mem (U.inv_mem hu) hv, w, hw, ?_⟩
    rw [mul_assoc, hvw, inv_mul_cancel_left]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨u * v, U.mul_mem hu hv, w, hw, mul_assoc u v w⟩

omit [IsTopologicalGroup G] in
/-- Right multiplication by an element of `K` preserves `U * W` when it preserves `W`. -/
theorem mul_mem_subgroup_mul_of_right {U : Subgroup G} {W : Set G} (K : OpenSubgroup G)
    (hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W) (y : G) {k : G} (hk : k ∈ K) :
    y * k ∈ (U : Set G) * W ↔ y ∈ (U : Set G) * W := by
  simp only [Set.mem_mul]
  constructor
  · rintro ⟨v, hv, w, hw, hvw⟩
    refine ⟨v, hv, w * k⁻¹, ?_, ?_⟩
    · rw [← hWK (w * k⁻¹) k hk, inv_mul_cancel_right]
      exact hw
    · rw [← mul_assoc, hvw, mul_inv_cancel_right]
  · rintro ⟨v, hv, w, hw, rfl⟩
    exact ⟨v, hv, w * k, (hWK w k hk).2 hw, (mul_assoc v w k).symm⟩

end Sets

variable [T2Space G] [MeasurableSpace G] [BorelSpace G]

section Fibre

variable (U : Subgroup G) (μU : Measure U)

/-- The `μU`-mass of the `u ∈ U` with `u⁻¹ x ∈ W`, as a real number. -/
def fibreMass (W : Set G) (x : G) : ℝ :=
  μU.real {u : U | (u : G)⁻¹ * x ∈ W}

/-- The cutoff `β = 1_W / fibreMass W`, whose integrals `∫_U β(u⁻¹ x) du` equal `1` on `W`. -/
def fibreCutoff (W : Set G) (x : G) : ℂ :=
  W.indicator (fun y => ((fibreMass U μU W y)⁻¹ : ℝ)) x

variable {U}

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The `u ∈ U` with `u⁻¹ x ∈ W` form an open set when `W` is open. -/
theorem isOpen_fibre {W : Set G} (hW : IsOpen W) (x : G) :
    IsOpen {u : U | (u : G)⁻¹ * x ∈ W} :=
  hW.preimage ((continuous_subtype_val.inv).mul continuous_const)

omit [MeasurableSpace G] [BorelSpace G] in
/-- The `u ∈ U` with `u⁻¹ x ∈ W` form a compact set when `U` is closed and `W` compact. -/
theorem isCompact_fibre (hU : IsClosed (U : Set G)) {W : Set G} (hW : IsCompact W) (x : G) :
    IsCompact {u : U | (u : G)⁻¹ * x ∈ W} := by
  have hD : IsCompact ((fun w => x * w⁻¹) '' W) :=
    hW.image (continuous_const.mul continuous_inv)
  refine (hU.isClosedEmbedding_subtypeVal.isCompact_preimage hD).of_isClosed_subset ?_ ?_
  · exact (hW.isClosed).preimage ((continuous_subtype_val.inv).mul continuous_const)
  · intro u hu
    refine ⟨(u : G)⁻¹ * x, hu, ?_⟩
    simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]

omit [T2Space G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] in
/-- Replacing `x` by `u⁻¹ x` left-translates the fibre by `u`. -/
theorem fibre_mul_left (u : U) (W : Set G) (x : G) :
    {v : U | (v : G)⁻¹ * ((u : G)⁻¹ * x) ∈ W} =
      (fun v : U => u * v) ⁻¹' {v : U | (v : G)⁻¹ * x ∈ W} := by
  ext v
  simp only [mem_ofPred_eq, mem_preimage, Subgroup.coe_mul, mul_inv_rev, mul_assoc]

omit [T2Space G] in
/-- The fibre mass is invariant under `x ↦ u⁻¹ x` for `u ∈ U`. -/
theorem fibreMass_inv_mul [IsMulLeftInvariant μU] (u : U) (W : Set G) (x : G) :
    fibreMass U μU W ((u : G)⁻¹ * x) = fibreMass U μU W x := by
  unfold fibreMass Measure.real
  rw [fibre_mul_left, measure_preimage_mul]

omit [T2Space G] [IsTopologicalGroup G] [BorelSpace G] in
/-- The fibre mass is invariant under right translation by `K` when `W` is. -/
theorem fibreMass_mul_right {W : Set G} (K : OpenSubgroup G)
    (hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W) (x : G) {k : G} (hk : k ∈ K) :
    fibreMass U μU W (x * k) = fibreMass U μU W x := by
  unfold fibreMass
  congr 1
  ext v
  simp only [mem_ofPred_eq, ← mul_assoc]
  exact hWK _ k hk

omit [BorelSpace G] in
/-- The fibre mass is positive on `W` for `W` compact open. -/
theorem fibreMass_pos (hU : IsClosed (U : Set G)) [IsFiniteMeasureOnCompacts μU]
    [μU.IsOpenPosMeasure] {W : Set G} (hWo : IsOpen W) (hWc : IsCompact W) {x : G}
    (hx : x ∈ W) : 0 < fibreMass U μU W x := by
  unfold fibreMass Measure.real
  apply ENNReal.toReal_pos
  · exact ((isOpen_fibre hWo x).measure_pos μU ⟨1, by simpa using hx⟩).ne'
  · exact (isCompact_fibre hU hWc x).measure_lt_top.ne

omit [T2Space G] [BorelSpace G] in
/-- The cutoff `β` is continuous when `W` is invariant under right translation by `K`. -/
theorem continuous_fibreCutoff {W : Set G} (K : OpenSubgroup G)
    (hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W) : Continuous (fibreCutoff U μU W) := by
  refine continuous_of_forall_mul_mem_eq K fun x k hk => ?_
  unfold fibreCutoff
  by_cases hx : x ∈ W
  · rw [indicator_of_mem ((hWK x k hk).2 hx), indicator_of_mem hx,
      fibreMass_mul_right μU K hWK x hk]
  · rw [indicator_of_notMem (fun h => hx ((hWK x k hk).1 h)), indicator_of_notMem hx]

/-- For `x ∈ W`, `∫_U β(u⁻¹ x) du = 1`. -/
theorem integral_fibreCutoff (hU : IsClosed (U : Set G)) [IsMulLeftInvariant μU]
    [IsFiniteMeasureOnCompacts μU] [μU.IsOpenPosMeasure] {W : Set G} (hWo : IsOpen W)
    (hWc : IsCompact W) {x : G} (hx : x ∈ W) :
    ∫ u : U, fibreCutoff U μU W ((u : G)⁻¹ * x) ∂μU = 1 := by
  have hfun : (fun u : U => fibreCutoff U μU W ((u : G)⁻¹ * x)) =
      {u : U | (u : G)⁻¹ * x ∈ W}.indicator (fun _ => (((fibreMass U μU W x)⁻¹ : ℝ) : ℂ)) := by
    funext u
    unfold fibreCutoff
    by_cases hu : (u : G)⁻¹ * x ∈ W
    · rw [indicator_of_mem hu, indicator_of_mem (show u ∈ {u : U | (u : G)⁻¹ * x ∈ W} from hu),
        fibreMass_inv_mul]
    · rw [indicator_of_notMem hu,
        indicator_of_notMem (show u ∉ {u : U | (u : G)⁻¹ * x ∈ W} from hu)]
  rw [hfun, integral_indicator_const _ (isOpen_fibre hWo x).measurableSet]
  have hpos := fibreMass_pos μU hU hWo hWc hx
  change ((fibreMass U μU W x : ℝ) : ℂ) * (((fibreMass U μU W x)⁻¹ : ℝ) : ℂ) = 1
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

/-- **Fibre vanishing.** Let `U` be a closed subgroup with a left Haar measure. A continuous
compactly supported `h` on `G` whose integrals over all left cosets `U x` vanish has integral
`0` for every left-invariant measure on `G` that is finite on compact sets. -/
theorem integral_eq_zero_of_integral_subgroup_eq_zero (hU : IsClosed (U : Set G))
    [IsMulLeftInvariant μU] [IsFiniteMeasureOnCompacts μU] [μU.IsOpenPosMeasure]
    (μG : Measure G) [IsMulLeftInvariant μG] [IsFiniteMeasureOnCompacts μG]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {h : G → ℂ} (hc : Continuous h) (hs : HasCompactSupport h)
    (h0 : ∀ x, ∫ u : U, h ((u : G) * x) ∂μU = 0) :
    ∫ x, h x ∂μG = 0 := by
  set W : Set G := tsupport h * (K : Set G) with hW
  have hWc : IsCompact W := hs.mul hK
  have hWo : IsOpen W := K.isOpen.mul_left
  have hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W := fun y k hk =>
    mul_mem_mul_openSubgroup_iff _ K y hk
  have hsW : tsupport h ⊆ W := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
  set β := fibreCutoff U μU W with hβ
  have hβc : Continuous β := continuous_fibreCutoff μU K hWK
  have hβW : ∀ y, β y ≠ 0 → y ∈ W := by
    intro y hy
    by_contra hyW
    exact hy (indicator_of_notMem hyW _)
  have hval : Continuous (fun u : U => (u : G)) := continuous_subtype_val
  -- compact set of `u ∈ U` with `u ∈ tsupport h * W⁻¹`
  have hDc : IsCompact ((fun u : U => (u : G)) ⁻¹' (tsupport h * W⁻¹)) :=
    hU.isClosedEmbedding_subtypeVal.isCompact_preimage (hs.mul hWc.inv)
  -- step 1: insert the cutoff
  have step1 : ∫ x, h x ∂μG = ∫ x, ∫ u : U, h x * β ((u : G)⁻¹ * x) ∂μU ∂μG := by
    congr 1
    funext x
    rw [integral_const_mul]
    by_cases hx : x ∈ tsupport h
    · rw [integral_fibreCutoff μU hU hWo hWc (hsW hx), mul_one]
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  -- step 2: Fubini
  have step2 : ∫ x, ∫ u : U, h x * β ((u : G)⁻¹ * x) ∂μU ∂μG =
      ∫ u : U, ∫ x, h x * β ((u : G)⁻¹ * x) ∂μG ∂μU := by
    apply integral_integral_swap_of_hasCompactSupport
    · exact (hc.comp continuous_fst).mul
        (hβc.comp ((hval.comp continuous_snd).inv.mul continuous_fst))
    · refine HasCompactSupport.intro (hs.prod hDc) fun p hp => ?_
      by_contra hne
      apply hp
      have h1 : h p.1 ≠ 0 := left_ne_zero_of_mul hne
      have h2 : β ((p.2 : G)⁻¹ * p.1) ≠ 0 := right_ne_zero_of_mul hne
      refine ⟨subset_tsupport _ h1, ?_⟩
      refine ⟨p.1, subset_tsupport _ h1, ((p.2 : G)⁻¹ * p.1)⁻¹, ?_, ?_⟩
      · exact Set.inv_mem_inv.2 (hβW _ h2)
      · simp only [mul_inv_rev, inv_inv, mul_inv_cancel_left]
  -- step 3: left invariance of `μG`
  have step3 : ∫ u : U, ∫ x, h x * β ((u : G)⁻¹ * x) ∂μG ∂μU =
      ∫ u : U, ∫ y, h ((u : G) * y) * β y ∂μG ∂μU := by
    congr 1
    funext u
    rw [← integral_mul_left_eq_self (fun x => h x * β ((u : G)⁻¹ * x)) (u : G)]
    simp only [inv_mul_cancel_left]
  -- step 4: Fubini again
  have step4 : ∫ u : U, ∫ y, h ((u : G) * y) * β y ∂μG ∂μU =
      ∫ y, ∫ u : U, h ((u : G) * y) * β y ∂μU ∂μG := by
    apply integral_integral_swap_of_hasCompactSupport
    · exact (hc.comp ((hval.comp continuous_fst).mul continuous_snd)).mul
        (hβc.comp continuous_snd)
    · refine HasCompactSupport.intro (hDc.prod hWc) fun p hp => ?_
      by_contra hne
      apply hp
      have h1 : h ((p.1 : G) * p.2) ≠ 0 := left_ne_zero_of_mul hne
      have h2 : β p.2 ≠ 0 := right_ne_zero_of_mul hne
      refine ⟨?_, hβW _ h2⟩
      refine ⟨(p.1 : G) * p.2, subset_tsupport _ h1, (p.2)⁻¹, Set.inv_mem_inv.2 (hβW _ h2), ?_⟩
      simp only [mul_inv_cancel_right]
  rw [step1, step2, step3, step4]
  have hzero : ∀ y, ∫ u : U, h ((u : G) * y) * β y ∂μU = 0 := by
    intro y
    rw [integral_mul_const, h0 y, zero_mul]
  simp only [hzero, integral_zero]

end Fibre

section Cutoff

variable (H U : Subgroup G) (μH : Measure H)

/-- The `μH`-mass of the `t ∈ H` with `t x ∈ U W`. -/
def cosetMass (W : Set G) (x : G) : ℝ :=
  μH.real {t : H | (t : G) * x ∈ (U : Set G) * W}

/-- The left `U`-invariant cutoff `α_W = 1_{U W} / cosetMass W`. -/
def cosetCutoff (W : Set G) (x : G) : ℂ :=
  ((U : Set G) * W).indicator (fun y => ((cosetMass H U μH W y)⁻¹ : ℝ)) x

variable {H U}

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The `t ∈ H` with `t x ∈ U W` form an open set when `W` is open. -/
theorem isOpen_cosetFibre {W : Set G} (hW : IsOpen W) (x : G) :
    IsOpen {t : H | (t : G) * x ∈ (U : Set G) * W} :=
  (hW.mul_left).preimage (continuous_subtype_val.mul continuous_const)

omit [T2Space G] [MeasurableSpace G] [BorelSpace G] in
/-- The `t ∈ H` with `t x ∈ U W` lie in a compact set, under the compactness hypothesis
on `H ∩ U C`. -/
theorem isCompact_cosetFibre (hH : IsClosed (H : Set G))
    (hHU : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ t ∈ H, t ∈ (U : Set G) * C → t ∈ D)
    {W : Set G} (hW : IsCompact W) (x : G) :
    ∃ D : Set H, IsCompact D ∧ {t : H | (t : G) * x ∈ (U : Set G) * W} ⊆ D := by
  obtain ⟨D, hD, hsub⟩ := hHU ((fun w => w * x⁻¹) '' W)
    (hW.image (continuous_id.mul continuous_const))
  refine ⟨(fun t : H => (t : G)) ⁻¹' D, hH.isClosedEmbedding_subtypeVal.isCompact_preimage hD,
    fun t ht => ?_⟩
  obtain ⟨u, hu, w, hw, huw⟩ := Set.mem_mul.mp ht
  refine hsub t t.property (Set.mem_mul.mpr ⟨u, hu, w * x⁻¹, ⟨w, hw, rfl⟩, ?_⟩)
  rw [← mul_assoc, huw, mul_inv_cancel_right]

omit [T2Space G] in
/-- The coset mass is invariant under left translation by `H`. -/
theorem cosetMass_mul_left [IsMulRightInvariant μH] (s : H) (W : Set G) (x : G) :
    cosetMass H U μH W ((s : G) * x) = cosetMass H U μH W x := by
  unfold cosetMass Measure.real
  have : {t : H | (t : G) * ((s : G) * x) ∈ (U : Set G) * W} =
      (fun t : H => t * s) ⁻¹' {t : H | (t : G) * x ∈ (U : Set G) * W} := by
    ext t
    simp only [mem_ofPred_eq, mem_preimage, Subgroup.coe_mul, mul_assoc]
  rw [this, measure_preimage_mul_right]

omit [T2Space G] [BorelSpace G] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The coset mass is invariant under left translation by `U` when `H` normalizes `U`. -/
theorem cosetMass_subgroup_mul (hnorm : ∀ t ∈ H, ∀ u ∈ U, t * u * t⁻¹ ∈ U) (W : Set G) (x : G)
    {u : G} (hu : u ∈ U) : cosetMass H U μH W (u * x) = cosetMass H U μH W x := by
  unfold cosetMass
  congr 1
  ext t
  simp only [mem_ofPred_eq]
  have h := mul_mem_subgroup_mul_iff U W (hnorm t t.property u hu) ((t : G) * x)
  rw [show (t : G) * u * (t : G)⁻¹ * ((t : G) * x) = (t : G) * (u * x) by group] at h
  exact h

omit [T2Space G] [BorelSpace G] [IsTopologicalGroup G] in
/-- The coset mass is invariant under right translation by `K` when `W` is. -/
theorem cosetMass_mul_right {W : Set G} (K : OpenSubgroup G)
    (hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W) (x : G) {k : G} (hk : k ∈ K) :
    cosetMass H U μH W (x * k) = cosetMass H U μH W x := by
  unfold cosetMass
  congr 1
  ext t
  simp only [mem_ofPred_eq, ← mul_assoc]
  exact mul_mem_subgroup_mul_of_right K hWK _ hk

omit [T2Space G] [BorelSpace G] [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The cutoff `α_W` is invariant under left translation by `U` when `H` normalizes `U`. -/
theorem cosetCutoff_subgroup_mul (hnorm : ∀ t ∈ H, ∀ u ∈ U, t * u * t⁻¹ ∈ U) (W : Set G)
    (x : G) {u : G} (hu : u ∈ U) : cosetCutoff H U μH W (u * x) = cosetCutoff H U μH W x := by
  unfold cosetCutoff
  by_cases hx : x ∈ (U : Set G) * W
  · rw [indicator_of_mem ((mul_mem_subgroup_mul_iff U W hu x).2 hx), indicator_of_mem hx,
      cosetMass_subgroup_mul μH hnorm W x hu]
  · rw [indicator_of_notMem (fun h => hx ((mul_mem_subgroup_mul_iff U W hu x).1 h)),
      indicator_of_notMem hx]

omit [T2Space G] [BorelSpace G] in
/-- The cutoff `α_W` is continuous when `W` is invariant under right translation by `K`. -/
theorem continuous_cosetCutoff {W : Set G} (K : OpenSubgroup G)
    (hWK : ∀ y, ∀ k ∈ K, y * k ∈ W ↔ y ∈ W) : Continuous (cosetCutoff H U μH W) := by
  refine continuous_of_forall_mul_mem_eq K fun x k hk => ?_
  unfold cosetCutoff
  by_cases hx : x ∈ (U : Set G) * W
  · rw [indicator_of_mem ((mul_mem_subgroup_mul_of_right K hWK x hk).2 hx),
      indicator_of_mem hx, cosetMass_mul_right μH K hWK x hk]
  · rw [indicator_of_notMem (fun h => hx ((mul_mem_subgroup_mul_of_right K hWK x hk).1 h)),
      indicator_of_notMem hx]

omit [T2Space G] in
/-- The `H`-average of `α_W` at `x` is the coset mass at `x` times its inverse. -/
theorem integral_cosetCutoff_eq_mul {W : Set G} (hWo : IsOpen W) [IsMulRightInvariant μH] (x : G) :
    ∫ t : H, cosetCutoff H U μH W ((t : G) * x) ∂μH =
      ((cosetMass H U μH W x : ℝ) : ℂ) * (((cosetMass H U μH W x)⁻¹ : ℝ) : ℂ) := by
  set S := {t : H | (t : G) * x ∈ (U : Set G) * W} with hS
  have hfun : (fun t : H => cosetCutoff H U μH W ((t : G) * x)) =
      S.indicator (fun _ => (((cosetMass H U μH W x)⁻¹ : ℝ) : ℂ)) := by
    funext t
    unfold cosetCutoff
    by_cases ht : (t : G) * x ∈ (U : Set G) * W
    · rw [indicator_of_mem ht, indicator_of_mem (show t ∈ S from ht), cosetMass_mul_left]
    · rw [indicator_of_notMem ht, indicator_of_notMem (show t ∉ S from ht)]
  rw [hfun, integral_indicator_const _ (isOpen_cosetFibre hWo x).measurableSet]
  rfl

omit [T2Space G] in
/-- The `H`-average of the cutoff `α_W` at `x` is `1` when some `t ∈ H` has `t x ∈ U W`. -/
theorem integral_cosetCutoff_of_exists (hH : IsClosed (H : Set G)) [IsMulRightInvariant μH]
    [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hHU : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ t ∈ H, t ∈ (U : Set G) * C → t ∈ D)
    {W : Set G} (hWo : IsOpen W) (hWc : IsCompact W) {x : G}
    (hex : ∃ t : H, (t : G) * x ∈ (U : Set G) * W) :
    ∫ t : H, cosetCutoff H U μH W ((t : G) * x) ∂μH = 1 := by
  rw [integral_cosetCutoff_eq_mul μH hWo x]
  obtain ⟨D, hD, hSD⟩ := isCompact_cosetFibre hH hHU hWc x
  have hpos : 0 < cosetMass H U μH W x := by
    unfold cosetMass Measure.real
    apply ENNReal.toReal_pos
    · obtain ⟨t, ht⟩ := hex
      exact ((isOpen_cosetFibre hWo x).measure_pos μH ⟨t, ht⟩).ne'
    · exact (measure_mono hSD).trans_lt hD.measure_lt_top |>.ne
  rw [← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one]

omit [T2Space G] in
/-- The `H`-average of the cutoff `α_W` at `x` is `0` when no `t ∈ H` has `t x ∈ U W`. -/
theorem integral_cosetCutoff_of_not_exists [IsMulRightInvariant μH] {W : Set G}
    (hWo : IsOpen W) {x : G} (hex : ¬ ∃ t : H, (t : G) * x ∈ (U : Set G) * W) :
    ∫ t : H, cosetCutoff H U μH W ((t : G) * x) ∂μH = 0 := by
  rw [integral_cosetCutoff_eq_mul μH hWo x]
  have hempty : {t : H | (t : G) * x ∈ (U : Set G) * W} = ∅ := by
    ext t
    simp only [mem_empty_iff_false, iff_false]
    exact fun ht => hex ⟨t, ht⟩
  have h0 : cosetMass H U μH W x = 0 := by
    unfold cosetMass
    rw [hempty, measureReal_empty]
  rw [h0, Complex.ofReal_zero, zero_mul]

omit [T2Space G] in
/-- The `H`-averages of the cutoff `α_W` have norm at most `1`. -/
theorem norm_integral_cosetCutoff_le (hH : IsClosed (H : Set G)) [IsMulRightInvariant μH]
    [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (hHU : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ t ∈ H, t ∈ (U : Set G) * C → t ∈ D)
    {W : Set G} (hWo : IsOpen W) (hWc : IsCompact W) (x : G) :
    ‖∫ t : H, cosetCutoff H U μH W ((t : G) * x) ∂μH‖ ≤ 1 := by
  by_cases hex : ∃ t : H, (t : G) * x ∈ (U : Set G) * W
  · rw [integral_cosetCutoff_of_exists μH hH hHU hWo hWc hex, norm_one]
  · rw [integral_cosetCutoff_of_not_exists μH hWo hex, norm_zero]
    exact zero_le_one

end Cutoff

section Main

variable {Θ : Type uΘ} [FunLike Θ G G] [MonoidHomClass Θ G G]

/-- The test function `h_W = α_W · f(x⁻¹ δ θ x)`. -/
def orbitCutoffFunction (θ : Θ) (δ : G) (U : Subgroup G)
    (μH : Measure (twistedCentralizer θ δ)) (W : Set G) (f : G → ℂ) (x : G) : ℂ :=
  cosetCutoff (twistedCentralizer θ δ) U μH W x * f (x⁻¹ * δ * θ x)

/-- **Vanishing along a unipotent subgroup.** Let `θ` be a continuous twist of `G`, `δ ∈ G`,
`H` its twisted centralizer with a right-invariant measure `μH` (finite on compact sets,
positive on open sets), and `ν` a quotient measure compatible with `μG` and `μH`. Let `U` be a
closed subgroup with a left Haar measure `μU`, normalized by `H`, such that for every compact
`C` the elements of `H` in `U C` and the `u ∈ U` with `u⁻¹ δ θ(u) ∈ C` lie in compact sets.
If `∫_U f(x⁻¹ u⁻¹ δ θ(u) θ(x)) du = 0` for every `x`, the twisted orbital integral of the
continuous compactly supported `f` at `δ` vanishes. -/
theorem twistedOrbitalIntegral_eq_zero_of_unipotent [SigmaCompactSpace G]
    (θ : Θ) (hθ : Continuous θ) (δ : G)
    [MeasurableSpace (LeftQuotient (twistedCentralizer θ δ))]
    (μG : Measure G) [IsMulLeftInvariant μG] [IsFiniteMeasureOnCompacts μG]
    (μH : Measure (twistedCentralizer θ δ)) [IsMulRightInvariant μH]
    [IsFiniteMeasureOnCompacts μH] [μH.IsOpenPosMeasure]
    (ν : Measure (LeftQuotient (twistedCentralizer θ δ)))
    (hν : IsCompatible (twistedCentralizer θ δ) μG μH ν)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (U : Subgroup G) (hU : IsClosed (U : Set G)) (μU : Measure U) [IsMulLeftInvariant μU]
    [IsFiniteMeasureOnCompacts μU] [μU.IsOpenPosMeasure]
    (hnorm : ∀ t ∈ twistedCentralizer θ δ, ∀ u ∈ U, t * u * t⁻¹ ∈ U)
    (hHU : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ t ∈ twistedCentralizer θ δ, t ∈ (U : Set G) * C → t ∈ D)
    (hprop : ∀ C : Set G, IsCompact C → ∃ D : Set G, IsCompact D ∧
      ∀ u ∈ U, u⁻¹ * δ * θ u ∈ C → u ∈ D)
    {f : G → ℂ} (hf : Continuous f) (hfs : HasCompactSupport f)
    (hcusp : ∀ x : G, ∫ u : U, f (x⁻¹ * ((u : G)⁻¹ * δ * θ u) * θ x) ∂μU = 0) :
    twistedOrbitalIntegral θ δ ν f = 0 := by
  have hH : IsClosed (twistedCentralizer θ δ : Set G) := isClosed_twistedCentralizer θ hθ δ
  -- the exhaustion `W j = compactCovering G j * K`
  let W : ℕ → Set G := fun j => compactCovering G j * (K : Set G)
  have hWc : ∀ j, IsCompact (W j) := fun j => (isCompact_compactCovering G j).mul hK
  have hWo : ∀ j, IsOpen (W j) := fun j => K.isOpen.mul_left
  have hWK : ∀ j, ∀ y, ∀ k ∈ K, y * k ∈ W j ↔ y ∈ W j := fun j y k hk =>
    mul_mem_mul_openSubgroup_iff _ K y hk
  -- the test functions
  let h : ℕ → G → ℂ := fun j => orbitCutoffFunction θ δ U μH (W j) f
  have hcont : ∀ j, Continuous (h j) := fun j =>
    (continuous_cosetCutoff μH K (hWK j)).mul
      (hf.comp ((continuous_inv.mul continuous_const).mul hθ))
  have hsupp : ∀ j, HasCompactSupport (h j) := by
    intro j
    obtain ⟨D, hD, hDsub⟩ := hprop (W j * tsupport f * (θ '' W j)⁻¹)
      (((hWc j).mul hfs).mul ((hWc j).image hθ).inv)
    refine HasCompactSupport.intro (hD.mul (hWc j)) fun x hx => ?_
    by_contra hne
    apply hx
    have h1 : cosetCutoff (twistedCentralizer θ δ) U μH (W j) x ≠ 0 := left_ne_zero_of_mul hne
    have h2 : f (x⁻¹ * δ * θ x) ≠ 0 := right_ne_zero_of_mul hne
    have hxUW : x ∈ (U : Set G) * W j := by
      by_contra hxn
      exact h1 (indicator_of_notMem hxn _)
    obtain ⟨u, hu, w, hw, rfl⟩ := hxUW
    refine ⟨u, hDsub u hu ?_, w, hw, rfl⟩
    refine ⟨w * ((u * w)⁻¹ * δ * θ (u * w)), ⟨w, hw, _, subset_tsupport _ h2, rfl⟩,
      (θ w)⁻¹, Set.inv_mem_inv.2 ⟨w, hw, rfl⟩, ?_⟩
    simp only [map_mul, mul_inv_rev, mul_assoc, mul_inv_cancel_left, mul_inv_cancel,
      mul_one]
  -- integrals over left `U`-cosets vanish
  have hfibre : ∀ j, ∀ x, ∫ u : U, h j ((u : G) * x) ∂μU = 0 := by
    intro j x
    have : (fun u : U => h j ((u : G) * x)) = fun u : U =>
        cosetCutoff (twistedCentralizer θ δ) U μH (W j) x *
          f (x⁻¹ * ((u : G)⁻¹ * δ * θ u) * θ x) := by
      funext u
      change cosetCutoff (twistedCentralizer θ δ) U μH (W j) ((u : G) * x) *
        f (((u : G) * x)⁻¹ * δ * θ ((u : G) * x)) = _
      rw [cosetCutoff_subgroup_mul μH hnorm (W j) x u.property]
      congr 2
      simp only [map_mul, mul_inv_rev, mul_assoc]
    rw [this, integral_const_mul, hcusp x, mul_zero]
  have hint : ∀ j, ∫ x, h j x ∂μG = 0 := fun j =>
    integral_eq_zero_of_integral_subgroup_eq_zero μU hU μG K hK (hcont j) (hsupp j)
      (hfibre j)
  -- the `H`-averages
  have havg : ∀ j, ∀ x : G, quotientAverage (twistedCentralizer θ δ) μH (h j) (Quotient.mk _ x) =
      (∫ t : twistedCentralizer θ δ, cosetCutoff (twistedCentralizer θ δ) U μH (W j)
        ((t : G) * x) ∂μH) * twistedOrbitFunction θ δ f (Quotient.mk _ x) := by
    intro j x
    rw [quotientAverage_mk, twistedOrbitFunction_mk, ← integral_mul_const]
    congr 1
    funext t
    change cosetCutoff (twistedCentralizer θ δ) U μH (W j) ((t : G) * x) *
      f (((t : G) * x)⁻¹ * δ * θ ((t : G) * x)) = _
    rw [twistedConj_left_mul θ δ t x]
  have hzero : ∀ j, ∫ q, quotientAverage (twistedCentralizer θ δ) μH (h j) q ∂ν = 0 := fun j =>
    (hν.integral_formula (h j) (hcont j) (hsupp j)).trans (hint j)
  -- dominated convergence
  by_cases hFi : Integrable (twistedOrbitFunction θ δ f) ν
  · have hlim : Tendsto (fun j => ∫ q, quotientAverage (twistedCentralizer θ δ) μH (h j) q ∂ν)
        atTop (𝓝 (∫ q, twistedOrbitFunction θ δ f q ∂ν)) := by
      refine tendsto_integral_of_dominated_convergence (fun q => ‖twistedOrbitFunction θ δ f q‖)
        (fun j => (hν.averaging_integrable (h j) (hcont j) (hsupp j)).aestronglyMeasurable)
        hFi.norm (fun j => Eventually.of_forall fun q => ?_) (Eventually.of_forall fun q => ?_)
      · induction q using Quotient.inductionOn with
        | h x =>
          rw [havg j x, norm_mul]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (norm_integral_cosetCutoff_le μH hH hHU (hWo j) (hWc j) x)
      · induction q using Quotient.inductionOn with
        | h x =>
          obtain ⟨j₀, hj₀⟩ := exists_mem_compactCovering x
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [eventually_ge_atTop j₀] with j hj
          rw [havg j x, integral_cosetCutoff_of_exists μH hH hHU (hWo j) (hWc j), one_mul]
          exact ⟨1, Set.mem_mul.mpr ⟨1, U.one_mem, x,
            Set.mem_mul.mpr ⟨x, compactCovering_subset G hj hj₀, 1, K.one_mem, mul_one x⟩,
            by simp⟩⟩
    have h0 : Tendsto (fun j => ∫ q, quotientAverage (twistedCentralizer θ δ) μH (h j) q ∂ν)
        atTop (𝓝 0) := by
      simp only [hzero]
      exact tendsto_const_nhds
    exact tendsto_nhds_unique hlim h0
  · exact integral_undef hFi

end Main

end Langlands.TraceFormula

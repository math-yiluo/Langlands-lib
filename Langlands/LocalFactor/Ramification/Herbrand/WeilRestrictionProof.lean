import Langlands.LocalFactor.Ramification.Herbrand.ConvexityProof
import Langlands.LocalFactor.Ramification.Herbrand.WeilInertiaProof
import Langlands.Weil.Representation.InductionContinuity

/-!
# Breaks of restrictions to finite intermediate fields

Restriction from the Weil group of `F` to that of a finite intermediate field `E`
moves the last break by at most the relative inverse Herbrand function `ψ_{E/F}`.
A representation of the Weil group of `E` that is trivial on the images of the upper
groups of `F` above `a > 0`, but not on the image of the upper group of index `a`,
has last break exactly `ψ_{E/F}(a)`. Combined with the star-shapedness of `ψ_{E/F}`
this gives the inequality chain of Deligne--Henniart 4.8.
-/

noncomputable section

namespace Langlands.Ramification.HerbrandBridge

open _root_.Langlands.Ramification.Padic Weil.Local LocalClassField
open VirtualRepresentation.LocalWeil.Ramification

universe u v

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (E : FiniteIntermediateExtension F.Carrier)

/-- Restriction to the Weil group of the intermediate field along its actual inclusion. -/
abbrev weilRestrict (A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)) :
    FiniteRepresentation.{0, u, v} ℂ (localWeilGroup (E.asPadicField (p := p))) :=
  FiniteRepresentation.restrict (intermediateWeilMap F E).toMonoidHom A

theorem weilRestrict_isContinuous {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    (hA : A.IsContinuous) : (weilRestrict E A).IsContinuous :=
  FiniteRepresentation.isContinuous_restrict _ (intermediateWeilMap F E).continuous hA

/-- The image of an upper group of `E` of index `ψ_{E/F}(r)` lies in the upper group of `F`
of index `r`. -/
theorem intermediateWeilMap_mem_upperGroup_iff {r : ℝ} (hr : -1 ≤ r)
    (w : localWeilGroup (E.asPadicField (p := p))) :
    intermediateWeilMap F E w ∈ upperGroup F r ↔
      w ∈ upperGroup (E.asPadicField (p := p)) (relativeHerbrandPsi E r) :=
  intermediateWeilEquiv_mem_upperGroup_iff E hr w

/-- Triviality at `r ≥ 0` passes to the restriction at `ψ_{E/F}(r)`. -/
theorem isTrivialAt_weilRestrict {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    {r : ℝ} (hr : 0 ≤ r) (h : IsTrivialAt F A r) :
    IsTrivialAt (E.asPadicField (p := p)) (weilRestrict E A) (relativeHerbrandPsi E r) := by
  intro w hw
  exact h _ ((intermediateWeilMap_mem_upperGroup_iff E (by linarith) w).mpr hw)

/-- If the last break of `A` lies below `b`, that of its restriction lies below
`ψ_{E/F}(b)`. -/
theorem lastBreak_weilRestrict_lt {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    (hA : A.IsContinuous) {b : ℝ} (h : lastBreak F A < b) :
    lastBreak (E.asPadicField (p := p)) (weilRestrict E A) < relativeHerbrandPsi E b := by
  obtain ⟨r, hr1, hr2⟩ := exists_between h
  have hr0 : 0 < r := lt_of_le_of_lt (lastBreak_nonneg F A) hr1
  have htriv := (lastBreak_lt_iff_isTrivialAt F A hA hr0).mp hr1
  have hres := isTrivialAt_weilRestrict E hr0.le htriv
  exact lt_of_le_of_lt (lastBreak_le_of_mem _ _ ⟨relativeHerbrandPsi_nonneg E hr0.le, hres⟩)
    (relativeHerbrandPsi_strictMono E hr2)

/-- The last break of the restriction is at most `ψ_{E/F}` of the last break. -/
theorem lastBreak_weilRestrict_le {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)}
    (hA : A.IsContinuous) :
    lastBreak (E.asPadicField (p := p)) (weilRestrict E A) ≤
      relativeHerbrandPsi E (lastBreak F A) := by
  apply le_of_forall_pos_lt_add
  intro ε hε
  have hcont := (relativeHerbrandPsi_continuous E).tendsto (lastBreak F A)
  have hev : ∀ᶠ b in nhds (lastBreak F A),
      relativeHerbrandPsi E b < relativeHerbrandPsi E (lastBreak F A) + ε :=
    hcont.eventually (gt_mem_nhds (by linarith))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  set b := lastBreak F A + δ / 2
  have hlt : lastBreak F A < b := by simp only [b]; linarith
  have h1 := lastBreak_weilRestrict_lt E hA hlt
  have h2 : relativeHerbrandPsi E b < relativeHerbrandPsi E (lastBreak F A) + ε := by
    apply hball
    rw [Real.dist_eq, abs_lt]
    constructor <;> simp only [b] <;> linarith
  linarith

/-- A representation of the Weil group of `E` trivial on the images of the upper groups
of index above `a > 0`, but not on the image of the upper group of index `a`, has last break
`ψ_{E/F}(a)`. -/
theorem lastBreak_eq_relativeHerbrandPsi
    {B : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup (E.asPadicField (p := p)))}
    (hB : B.IsContinuous) {a : ℝ} (ha : 0 < a)
    (htriv : ∀ w : ℝ, a < w → ∀ x, intermediateWeilMap F E x ∈ upperGroup F w →
      B.representation x = 1)
    (hnon : ¬ ∀ x, intermediateWeilMap F E x ∈ upperGroup F a → B.representation x = 1) :
    lastBreak (E.asPadicField (p := p)) B = relativeHerbrandPsi E a := by
  have hψa : 0 < relativeHerbrandPsi E a := by
    have h := relativeHerbrandPsi_strictMono E ha
    rwa [relativeHerbrandPsi_zero] at h
  have htrivE : ∀ w : ℝ, a < w →
      IsTrivialAt (E.asPadicField (p := p)) B (relativeHerbrandPsi E w) := by
    intro w hw x hx
    exact htriv w hw x ((intermediateWeilMap_mem_upperGroup_iff E (by linarith) x).mpr hx)
  apply le_antisymm
  · apply le_of_forall_pos_lt_add
    intro ε hε
    have hcont := (relativeHerbrandPsi_continuous E).tendsto a
    have hev : ∀ᶠ w in nhds a, relativeHerbrandPsi E w < relativeHerbrandPsi E a + ε :=
      hcont.eventually (gt_mem_nhds (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
    have hw : a < a + δ / 2 := by linarith
    have h1 := lastBreak_le_of_mem (E.asPadicField (p := p)) B
      ⟨relativeHerbrandPsi_nonneg E (by linarith), htrivE _ hw⟩
    have h2 : relativeHerbrandPsi E (a + δ / 2) < relativeHerbrandPsi E a + ε := by
      apply hball
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    apply hnon
    intro x hx
    have := (lastBreak_lt_iff_isTrivialAt (E.asPadicField (p := p)) B hB hψa).mp hlt
    exact this x ((intermediateWeilMap_mem_upperGroup_iff E (by linarith) x).mp hx)

/-- The inequality chain of Deligne--Henniart 4.8: if the last break of `A` lies below `a/2`
with `a > 0`, the last break of its restriction lies below `ψ_{E/F}(a)/2`. -/
theorem lastBreak_weilRestrict_lt_half
    {A : FiniteRepresentation.{0, u, v} ℂ (localWeilGroup F)} (hA : A.IsContinuous)
    {a : ℝ} (ha : 0 < a) (h : lastBreak F A < a / 2) :
    lastBreak (E.asPadicField (p := p)) (weilRestrict E A) < relativeHerbrandPsi E a / 2 :=
  lt_of_lt_of_le (lastBreak_weilRestrict_lt E hA h)
    (relativeHerbrandPsi_half_le E ha.le)

end Langlands.Ramification.HerbrandBridge

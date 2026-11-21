import Langlands.Representation.Plancherel.NormalizedIwasawaPush
import Langlands.Analysis.Local.QuotientWeilKernel
import Langlands.Analysis.Local.SubgroupCompactOpenHaar

/-! # A compact test averaged over a Levi and a common radical -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

namespace Langlands.Plancherel.LeviInvariantIwasawaExchange

open Aubert.General Langlands.QuotientIntegration

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {M : Subgroup G} [MeasurableSpace M] [BorelSpace M]
  {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
  (ι : H →* G) (hι : Continuous ι)
  (Q : OpenSubgroup G) (μM : Measure M) (μH : Measure H)

/-- Average an open subgroup indicator over the Levi and the embedded
intersection radical in Levi-then-radical order. -/
def compactLeviRadicalAverage (g : G) : ℝ≥0∞ :=
  ∫⁻ m : M, ∫⁻ h : H, (Q : Set G).indicator 1 ((m : G) * ι h * g) ∂μH ∂μM

omit [IsTopologicalGroup G] in
private theorem measurable_compactIndicator : Measurable ((Q : Set G).indicator (1 : G → ℝ≥0∞)) :=
  measurable_one.indicator Q.isOpen.measurableSet

include hι in
omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Open subgroup indicator averages are measurable. -/
theorem measurable_compactLeviRadicalAverage [MeasurableMul₂ G] [SFinite μH] [SFinite μM] :
    Measurable (compactLeviRadicalAverage ι Q μM μH) := by
  let f (p : (G × M) × H) :=
    (Q : Set G).indicator (1 : G → ℝ≥0∞) ((p.1.2 : G) * ι p.2 * p.1.1)
  have hf : Measurable f := (measurable_compactIndicator Q).comp
    (((continuous_subtype_val.measurable.comp (measurable_snd.comp measurable_fst)).mul
      (hι.measurable.comp measurable_snd)).mul (measurable_fst.comp measurable_fst))
  exact hf.lintegral_prod_right'.lintegral_prod_right'

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [BorelSpace M]
  [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H] in
/-- The average vanishes outside the product of the Levi, the radical and
the open test subgroup. -/
theorem compactLeviRadicalAverage_eq_zero
    (hMH : ∀ (m : M) (h : H), ∃ h' : H, ι h * (m : G) = (m : G) * ι h')
    {g : G} (hg : ¬∃ (m : M) (h : H) (q : Q), g = (m : G) * ι h * (q : G)) :
    compactLeviRadicalAverage ι Q μM μH g = 0 := by
  unfold compactLeviRadicalAverage
  have hz (m : M) (h : H) : (Q : Set G).indicator (1 : G → ℝ≥0∞) ((m : G) * ι h * g) = 0 := by
    apply Set.indicator_of_notMem
    intro hx
    let q : Q := ⟨_, hx⟩
    obtain ⟨r, hr⟩ := hMH m⁻¹ h⁻¹
    apply hg
    refine ⟨m⁻¹, r, q, ?_⟩
    calc
      g = (ι h⁻¹ * (m⁻¹ : M).val) * ((m : G) * ι h * g) := by rw [map_inv, Subgroup.coe_inv]; group
      _ = _ := by rw [hr]
  simp only [hz, lintegral_zero]

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] [BorelSpace M]
  [TopologicalSpace H] [IsTopologicalGroup H] [BorelSpace H] in
/-- The average is right invariant under the test subgroup. -/
theorem compactLeviRadicalAverage_mul_right {q : G} (hq : q ∈ Q) (g : G) :
    compactLeviRadicalAverage ι Q μM μH (g * q) = compactLeviRadicalAverage ι Q μM μH g := by
  unfold compactLeviRadicalAverage
  refine lintegral_congr (fun m => lintegral_congr (fun h => ?_))
  rw [← mul_assoc]
  have hmem : (m : G) * ι h * g * q ∈ (Q : Set G) ↔ (m : G) * ι h * g ∈ (Q : Set G) :=
    Q.toSubgroup.mul_mem_cancel_right hq
  by_cases ht : (m : G) * ι h * g ∈ (Q : Set G)
  · rw [Set.indicator_of_mem (hmem.mpr ht), Set.indicator_of_mem ht]
    rfl
  · rw [Set.indicator_of_notMem (fun h => ht (hmem.mp h)), Set.indicator_of_notMem ht]

include hι in
omit [BorelSpace M] in
/-- The average is left invariant under the intersection radical. -/
theorem compactLeviRadicalAverage_radical_mul [μH.IsMulRightInvariant] (h : H) (g : G) :
    compactLeviRadicalAverage ι Q μM μH (ι h * g) = compactLeviRadicalAverage ι Q μM μH g := by
  unfold compactLeviRadicalAverage
  refine lintegral_congr (fun m => ?_)
  have hf : Measurable
      (fun a : H => (Q : Set G).indicator (1 : G → ℝ≥0∞) ((m : G) * ι a * g)) :=
    (measurable_compactIndicator Q).comp ((hι.const_mul _).mul_const _).measurable
  calc
    _ = ∫⁻ a : H, (Q : Set G).indicator 1 ((m : G) * ι (a * h) * g) ∂μH := by
      refine lintegral_congr (fun a => ?_)
      rw [map_mul, mul_assoc, mul_assoc, mul_assoc]
    _ = _ := by rw [← lintegral_map hf (measurable_mul_const h), map_mul_right_eq_self]

include hι in
/-- Left multiplication by a Levi point multiplies the average by the actual
Haar modulus of its conjugation on the intersection radical. -/
theorem compactLeviRadicalAverage_levi_mul [LocallyCompactSpace H] [MeasurableMul₂ G]
    [μH.IsHaarMeasure] [μH.Regular] [μM.IsMulRightInvariant] [SFinite μH]
    (m : M) (φ : H ≃ₜ* H)
    (hφ : ∀ h, ι (φ.symm h) = (m : G)⁻¹ * ι h * m) (g : G) :
    compactLeviRadicalAverage ι Q μM μH ((m : G) * g) =
      (mulEquivHaarChar φ : ℝ≥0∞) * compactLeviRadicalAverage ι Q μM μH g := by
  have hcs : Measurable (φ.symm : H → H) := φ.symm.continuous.measurable
  have hmap : μH.map φ.symm = (mulEquivHaarChar φ : ℝ≥0∞) • μH := by
    let e := φ.toHomeomorph.toMeasurableEquiv
    change μH.map e.symm = _
    rw [e.map_symm]
    exact (mulEquivHaarChar_smul_eq_comap μH φ).symm
  let f (x : M) (h : H) := (Q : Set G).indicator (1 : G → ℝ≥0∞) ((x : G) * ι h * g)
  have hfm : Measurable (fun p : M × H => f p.1 p.2) :=
    (measurable_compactIndicator Q).comp
      (((continuous_subtype_val.measurable.comp measurable_fst).mul
        (hι.measurable.comp measurable_snd)).mul_const g)
  have hf (x : M) : Measurable (f x) := (measurable_compactIndicator Q).comp
    ((hι.const_mul _).mul_const _).measurable
  have hA : Measurable (fun x : M => ∫⁻ h, f x h ∂μH) := hfm.lintegral_prod_right'
  have hAm : Measurable (fun x : M => ∫⁻ h, f (x * m) h ∂μH) :=
    hA.comp (measurable_mul_const m)
  unfold compactLeviRadicalAverage
  calc
    _ = ∫⁻ x : M, ∫⁻ h : H, f (x * m) (φ.symm h) ∂μH ∂μM := by
      refine lintegral_congr (fun x => lintegral_congr (fun h => ?_))
      unfold f
      congr 1
      rw [Subgroup.coe_mul, hφ]
      group
    _ = ∫⁻ x : M, (mulEquivHaarChar φ : ℝ≥0∞) * (∫⁻ h : H, f (x * m) h ∂μH) ∂μM := by
      refine lintegral_congr (fun x => ?_)
      rw [← lintegral_map (hf (x * m)) hcs, hmap, lintegral_smul_measure, smul_eq_mul]
    _ = _ := by
      change (∫⁻ x : M, (mulEquivHaarChar φ : ℝ≥0∞) * (∫⁻ h : H, f (x * m) h ∂μH) ∂μM) =
        (mulEquivHaarChar φ : ℝ≥0∞) * ∫⁻ x : M, ∫⁻ h : H, f x h ∂μH ∂μM
      rw [lintegral_const_mul _ hAm]
      congr 1
      exact (lintegral_map hA (measurable_mul_const m)).symm.trans
        (by rw [map_mul_right_eq_self])

include hι in
omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The identity value is the product measure of the coordinate preimage
of the open test subgroup. -/
theorem compactLeviRadicalAverage_one_eq_measure [MeasurableMul₂ G] [SFinite μH] :
    compactLeviRadicalAverage ι Q μM μH 1 =
      (μM.prod μH) ((fun p : M × H => (p.1 : G) * ι p.2) ⁻¹' (Q : Set G)) := by
  let p : M × H → G := fun w => (w.1 : G) * ι w.2
  have hp : Measurable p :=
    (continuous_subtype_val.measurable.comp measurable_fst).mul (hι.measurable.comp measurable_snd)
  have hf : Measurable (fun x => (Q : Set G).indicator (1 : G → ℝ≥0∞) (p x)) :=
    (measurable_compactIndicator Q).comp hp
  unfold compactLeviRadicalAverage
  simp only [mul_one]
  rw [← lintegral_prod _ hf.aemeasurable]
  change ∫⁻ x, (Q : Set G).indicator 1 (p x) ∂μM.prod μH = _
  calc
    _ = ∫⁻ x, (p ⁻¹' (Q : Set G)).indicator 1 x ∂μM.prod μH := by
      refine lintegral_congr (fun x => ?_)
      by_cases hx : p x ∈ (Q : Set G)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (show x ∈ p ⁻¹' (Q : Set G) from hx)]
        rfl
      · rw [Set.indicator_of_notMem hx,
          Set.indicator_of_notMem (show x ∉ p ⁻¹' (Q : Set G) from hx)]
    _ = _ := lintegral_indicator_one (Q.isOpen.measurableSet.preimage hp)

section Unfolding

variable [SecondCountableTopology G]
  {P U : Subgroup G} (h : IsSemidirectDecomposition P M U) (S : Subgroup U)
  (hS : IsClosed (S : Set U))
  [T2Space U] [LocallyCompactSpace U] [SecondCountableTopology U]
  [MeasurableSpace U] [BorelSpace U] [MeasurableSpace S] [BorelSpace S]
  [MeasurableSpace (LeftQuotient S)] [BorelSpace (LeftQuotient S)]
  (K : OpenSubgroup G) (ambientMeasure : Measure G)
  (radicalMeasure : Measure U) (intersectionMeasure : Measure S)
  [SFinite intersectionMeasure] [intersectionMeasure.IsMulRightInvariant]

local notation "incl" => U.subtype.comp S.subtype

/-- The compact average through the actual left quotient of the radical. -/
def compactLeviRadicalQuotientAverage (k : G) : LeftQuotient S → ℝ≥0∞ :=
  descend S (fun u => compactLeviRadicalAverage incl Q μM intersectionMeasure ((u : G) * k))
    (fun s u => by
      change compactLeviRadicalAverage incl Q μM intersectionMeasure (((incl s) * (u : G)) * k) =
        compactLeviRadicalAverage incl Q μM intersectionMeasure ((u : G) * k)
      rw [mul_assoc]
      exact compactLeviRadicalAverage_radical_mul incl
        (continuous_subtype_val.comp continuous_subtype_val) Q μM intersectionMeasure s _)

include hS h in
/-- The compatible intersection quotient unfolds the compact average. The
result is the exact ambient Iwasawa factor times the mass of the test subgroup. -/
theorem lintegral_compactLeviRadicalQuotientAverage [SFinite ambientMeasure]
    [ambientMeasure.IsMulLeftInvariant] [radicalMeasure.IsHaarMeasure] [SFinite radicalMeasure]
    [intersectionMeasure.IsHaarMeasure] [μM.IsHaarMeasure] [SFinite μM]
    (ν : Measure (LeftQuotient S)) (hν : IsCompatible S radicalMeasure intersectionMeasure ν)
    (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k) :
    ∫⁻ k in (K : Set G), ∫⁻ q, compactLeviRadicalQuotientAverage Q μM S intersectionMeasure k q
        ∂ν ∂ambientMeasure =
      iwasawaCompactMass K μM radicalMeasure * ambientMeasure (Q : Set G) := by
  let F := (Q : Set G).indicator (1 : G → ℝ≥0∞)
  have hF : Measurable F := measurable_compactIndicator Q
  rw [← lintegral_indicator_one Q.isOpen.measurableSet,
    ← lintegral_iwasawa_eq_mass h K μM radicalMeasure hfac F hF]
  refine lintegral_congr (fun k => ?_)
  let f (u : U) := ∫⁻ m : M, F ((m : G) * (u : G) * k) ∂μM
  have hfun : Measurable (fun w : U × M => F ((w.2 : G) * (w.1 : G) * k)) :=
    hF.comp (((continuous_subtype_val.measurable.comp measurable_snd).mul
      (continuous_subtype_val.measurable.comp measurable_fst)).mul_const k)
  have hf : Measurable f := hfun.lintegral_prod_right'
  calc
    _ = ∫⁻ q, ∫⁻ u, f u ∂orbitKernel S hS intersectionMeasure q ∂ν := by
      refine lintegral_congr (fun q => ?_)
      obtain ⟨u, rfl⟩ := Quotient.exists_rep q
      rw [orbitKernel_mk, lintegral_map hf (continuous_subtype_val.mul_const u).measurable]
      change (∫⁻ m : M, ∫⁻ s : S, F ((m : G) * incl s * ((u : G) * k))
        ∂intersectionMeasure ∂μM) = ∫⁻ s : S, f (s.val * u) ∂intersectionMeasure
      have hprod : Measurable (fun p : M × S => F ((p.1 : G) * incl p.2 * ((u : G) * k))) :=
        hF.comp (((continuous_subtype_val.measurable.comp measurable_fst).mul
          (continuous_subtype_val.measurable.comp
            (continuous_subtype_val.measurable.comp measurable_snd))).mul_const _)
      rw [lintegral_lintegral_swap hprod.aemeasurable]
      refine lintegral_congr (fun s => lintegral_congr (fun m => ?_))
      dsimp only [f, MonoidHom.comp_apply, Subgroup.coe_subtype, Subgroup.coe_mul]
      simp only [mul_assoc]
    _ = ∫⁻ u : U, f u ∂radicalMeasure :=
      lintegral_orbitKernel S hS intersectionMeasure radicalMeasure ν hν f hf
    _ = _ := lintegral_lintegral_swap hfun.aemeasurable

end Unfolding

end Langlands.Plancherel.LeviInvariantIwasawaExchange

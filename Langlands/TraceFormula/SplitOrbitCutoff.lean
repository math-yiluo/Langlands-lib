import Langlands.BaseChange.SplitMatching
import Langlands.JacquetLanglands.LocalCharacter
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Split-place test functions with prescribed neighbourhoods -/

noncomputable section

open MeasureTheory Topology
open scoped BigOperators ComplexOrder

namespace Langlands.TraceFormula

open BaseChange JacquetLanglands HarmonicAnalysis

universe u

private theorem exists_splitProductTests
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
    {m : ℕ} (a : Fin (m + 1) → G) {A : Set (Fin (m + 1) → G)} {U : Set G}
    (hA : IsOpen A) (ha : a ∈ A) (hU : IsOpen U) (haU : (List.ofFn a).prod ∈ U) :
    ∃ ψ : Fin (m + 1) → SchwartzBruhat G,
      (∏ i, ψ i (a i)) = 1 ∧
      tsupport (fun x : Fin (m + 1) → G ↦ ∏ i, ψ i (x i)) ⊆ A ∧
      tsupport (convolutionProduct μ ψ : G → ℂ) ⊆ U ∧
      (∀ g, 0 ≤ convolutionProduct μ ψ g) ∧
      0 < convolutionProduct μ ψ (List.ofFn a).prod := by
  classical
  let prod : (Fin (m + 1) → G) → G := fun x ↦ (List.ofFn x).prod
  have hprod : Continuous prod := (splitProductFiberChart (G := G) m).symm.continuous.fst
  obtain ⟨V, hV, hVsub⟩ :=
    isOpen_pi_iff'.mp (hA.inter (hU.preimage hprod)) a ⟨ha, haU⟩
  choose K hKc hKo haK hKV using fun i ↦
    exists_isCompact_isClopen_subset (hV i).1 (hV i).2
  let S := Set.pi Set.univ K
  have hSsub : S ⊆ A ∩ prod ⁻¹' U :=
    (Set.pi_mono fun i _ ↦ hKV i).trans hVsub
  have hSclopen : IsClopen S :=
    ⟨isClosed_set_pi fun i _ ↦ (hKo i).isClosed,
      isOpen_set_pi Set.finite_univ fun i _ ↦ (hKo i).isOpen⟩
  have hScompact : IsCompact S := isCompact_univ_pi hKc
  have haS : a ∈ S := Set.mem_pi.mpr fun i _ ↦ haK i
  let ψ (i : Fin (m + 1)) := Hecke.TestFunction.characteristic (hKo i) (hKc i)
  have htensor (x : Fin (m + 1) → G) :
      (∏ i, ψ i (x i)) = S.indicator (fun _ ↦ (1 : ℂ)) x := by
    by_cases hx : x ∈ S
    · have hvalue (i : Fin (m + 1)) : ψ i (x i) = 1 :=
        Set.indicator_of_mem (Set.mem_pi.mp hx i (Set.mem_univ i)) _
      simp only [hvalue, Finset.prod_const_one, Set.indicator_of_mem hx]
    · have hmissing : ∃ i, x i ∉ K i := by
        simpa only [S, Set.mem_pi, Set.mem_univ, true_implies, not_forall] using hx
      obtain ⟨i, hi⟩ := hmissing
      have hzero : ψ i (x i) = 0 := Set.indicator_of_notMem hi _
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, Set.indicator_of_notMem hx]
  let ρ : Measure (Fin m → G) := Measure.pi fun _ ↦ μ
  let P (g : G) := fun w : Fin m → G ↦ splitProductFiberChart m (g, w)
  have hP (g : G) : IsClosedEmbedding (P g) := by
    apply (splitProductFiberChart (G := G) m).isClosedEmbedding.comp
    refine ⟨isEmbedding_prodMkRight g, ?_⟩
    have he : Set.range (Prod.mk g : (Fin m → G) → _) = Prod.fst ⁻¹' {g} := by
      ext p
      rcases p with ⟨x, w⟩
      simp [eq_comm]
    rw [he]
    exact isClosed_singleton.preimage continuous_fst
  have htotal (g : G) (w : Fin m → G) : prod (P g w) = g :=
    congrArg Prod.fst ((splitProductFiberChart (G := G) m).symm_apply_apply (g, w))
  have hformula (g : G) :
      convolutionProduct μ ψ g = ((ρ (P g ⁻¹' S)).toReal : ℂ) := by
    rw [← integral_splitProductFiber μ ψ g]
    simp_rw [htensor]
    change (∫ w, (P g ⁻¹' S).indicator (fun _ ↦ (1 : ℂ)) w ∂ρ) = _
    rw [integral_indicator_const _ ((hSclopen.isOpen.preimage (hP g).continuous).measurableSet)]
    simp [Measure.real, Complex.real_smul]
  refine ⟨ψ, by rw [htensor, Set.indicator_of_mem haS], ?_, ?_, ?_, ?_⟩
  · have hsupp : tsupport (fun x : Fin (m + 1) → G ↦ ∏ i, ψ i (x i)) ⊆ S := by
      apply closure_minimal _ hSclopen.isClosed
      intro x hx
      by_contra hn
      exact hx ((htensor x).trans (Set.indicator_of_notMem hn _))
    exact hsupp.trans (hSsub.trans Set.inter_subset_left)
  · rw [Hecke.TestFunction.tsupport_eq_support]
    intro g hg
    by_contra hgu
    have hempty : P g ⁻¹' S = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro w hw
      exact hgu (htotal g w ▸ (hSsub hw).2)
    exact hg (by rw [hformula, hempty, measure_empty, ENNReal.toReal_zero, Complex.ofReal_zero])
  · intro g
    rw [hformula]
    exact Complex.zero_le_real.mpr ENNReal.toReal_nonneg
  · have hmem : Fin.init a ∈ P (prod a) ⁻¹' S := by
      change splitProductFiberChart m (prod a, Fin.init a) ∈ S
      have he : splitProductFiberChart m (prod a, Fin.init a) = a :=
        (splitProductFiberChart (G := G) m).apply_symm_apply a
      rwa [he]
    rw [hformula, Complex.zero_lt_real]
    have hopen := hSclopen.isOpen.preimage (hP (prod a)).continuous
    have hcompact := (hP (prod a)).isCompact_preimage hScompact
    have hpos : 0 < ρ (P (prod a) ⁻¹' S) := hopen.measure_pos ρ ⟨_, hmem⟩
    exact ENNReal.toReal_pos hpos.ne' hcompact.measure_lt_top.ne

/-- At a completely split place, a split tensor and its matching convolution
can be supported within prescribed neighbourhoods of a tuple and of its
ordered product, while the convolution is positive at that product. -/
def SplitOrbitCutoffStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n m : ℕ),
    let G := GeneralLinear n F
    let E := GeneralLinear n (Fin (m + 1) → F)
    let κ := splitGLCoordinates F n (m + 1)
    letI : MeasurableSpace G := borel _
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace E := borel _
    letI : BorelSpace E := ⟨rfl⟩
    ∀ (μF : Measure G) [μF.IsHaarMeasure] (μE : Measure E) [μE.IsHaarMeasure],
      IsSplitProductHaar μF μE →
      ∀ (δ : E) (A : Set (Fin (m + 1) → G)) (U : Set G),
        IsOpen A → κ δ ∈ A → IsOpen U → (List.ofFn (κ δ)).prod ∈ U →
        ∃ ψ : Fin (m + 1) → SchwartzBruhat G,
          let φ := splitTensor fun i ↦ (ψ i : G → ℂ)
          let f := convolutionProduct μF ψ
          AreConcordant (splitCyclicShift F (m + 1)) (m + 1) μF μE φ (f : G → ℂ) ∧
          φ δ = 1 ∧ tsupport φ ⊆ κ ⁻¹' A ∧ tsupport (f : G → ℂ) ⊆ U ∧
          (∀ g, 0 ≤ f g) ∧ 0 < f (List.ofFn (κ δ)).prod

theorem splitOrbitCutoff : SplitOrbitCutoffStatement.{u} := by
  intro F _ _ _ _ n m
  dsimp only
  intro μF _ μE _ hμ δ A U hA hδ hU hδU
  let := LocalFieldTopology.t2Space F
  let := LocalFieldTopology.generalLinear_t2Space F n
  let := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let := LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let := LocalFieldTopology.generalLinear_secondCountableTopology F n
  let : MeasurableSpace (GeneralLinear n F) := borel _
  let : BorelSpace (GeneralLinear n F) := ⟨rfl⟩
  let : MeasurableSpace (GeneralLinear n (Fin (m + 1) → F)) := borel _
  let : BorelSpace (GeneralLinear n (Fin (m + 1) → F)) := ⟨rfl⟩
  let κ := splitGLCoordinates F n (m + 1)
  obtain ⟨ψ, hone, hts, hfs, hnonneg, hpos⟩ := exists_splitProductTests μF (κ δ) hA hδ hU hδU
  refine ⟨ψ, (splitMatching F n m μF).2 μE inferInstance hμ ψ, hone, ?_, hfs, hnonneg, hpos⟩
  let p : (Fin (m + 1) → GeneralLinear n F) → ℂ := fun x ↦ ∏ i, ψ i (x i)
  have hsupp : tsupport (p ∘ κ) ⊆ κ ⁻¹' tsupport p := by
    apply closure_minimal _ ((isClosed_tsupport p).preimage κ.continuous)
    intro x hx
    exact subset_tsupport p hx
  exact hsupp.trans (Set.preimage_mono hts)

end Langlands.TraceFormula

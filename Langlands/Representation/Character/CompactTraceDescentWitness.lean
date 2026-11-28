import Langlands.Representation.Character.CompactTraceDescentPairing

/-! # Compact trace witnesses from a smoothed conjugation pushforward -/

noncomputable section

namespace Langlands.Character

open Function HarmonicAnalysis MeasureTheory MeasureTheory.Measure
open Hecke.TestFunction (leftTranslate leftTranslate_apply pullback pullback_apply)

variable {G M X Y : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]
  [MeasurableSpace G] [BorelSpace G]
  [Group M] [TopologicalSpace M]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]

/-- Conjugating a slice point and using an element of the compact test subgroup. -/
def compactSliceConjugation (K : OpenSubgroup G) (i : M →* G) (y : G) (z : K × M) : G :=
  z.1.val * (y * i z.2) * z.1.val⁻¹

variable (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The constant test on the compact conjugator subgroup tensored with the slice trace. -/
def compactSliceTraceTest [IsTopologicalGroup M] [CompactSpace M] [FiniteDimensional ℂ Y]
    (σ : Representation ℂ M Y) (hσ : IsSmooth σ) : SchwartzBruhat (K × M) :=
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  SchwartzBruhat.tensor (⟨fun _ => 1, IsLocallyConstant.const 1, HasCompactSupport.of_compactSpace _⟩ :
    SchwartzBruhat K) (compactTraceTest σ hσ)

omit [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [MeasurableSpace G] [BorelSpace G] in
private theorem eval_conj_compactTraceCoset [FiniteDimensional ℂ X]
    (τ : Representation ℂ K X) (hτ : IsSmooth τ) (D : Distribution G)
    (hD : Distribution.IsConjugationInvariant D) (k : K) (g : G) :
    D (compactTraceCosetTest K hK τ hτ (k.val * g * k.val⁻¹)) =
      D (compactTraceCosetTest K hK τ hτ g) := by
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let t := compactTraceTest τ hτ
  let f := SchwartzBruhat.extendZero K.isOpen t
  have hf (z : G) : f (k.val * z * k.val⁻¹) = f z := by
    by_cases hz : z ∈ K
    · let w : K := ⟨z, hz⟩
      change f ((k * w * k⁻¹ : K) : G) = f (w : G)
      simp only [f, SchwartzBruhat.extendZero_apply_subtype, t, compactTraceTest_apply]
      exact Representation.char_conj τ w k
    · have hnot : k.val * z * k.val⁻¹ ∉ K := by
        change k.val * z * k.val⁻¹ ∉ K.toSubgroup
        rwa [K.toSubgroup.mul_mem_cancel_right (K.inv_mem k.property),
          K.toSubgroup.mul_mem_cancel_left k.property]
      rw [show f _ = 0 from SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen t hnot,
        show f z = 0 from SchwartzBruhat.extendZero_apply_of_not_mem K.isOpen t hz]
  let g' := k.val * g * k.val⁻¹
  have htest : pullback (Distribution.conjugationHomeomorph k.val) (leftTranslate g' f) =
      leftTranslate g f := by
    apply Hecke.TestFunction.ext
    intro z
    simp only [pullback_apply, leftTranslate_apply, Distribution.conjugationHomeomorph_apply]
    have heq : g'⁻¹ * (k.val * z * k.val⁻¹) = k.val * (g⁻¹ * z) * k.val⁻¹ := by
      dsimp only [g']
      group
    rw [heq, hf]
  change D (leftTranslate g' f) = D (leftTranslate g f)
  rw [← htest]
  exact ((Distribution.isConjugationInvariant_iff D).mp hD k.val (leftTranslate g' f)).symm

/-- A nonzero evaluation on the conjugation pushforward smoothed by a compact
trace detects the compact interaction and a nonzero translated trace on the slice. -/
def CompactTraceDescentWitnessStatement
    [IsTopologicalGroup M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]
    [MeasurableSpace M] [BorelSpace M] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]
    (ν : Measure G) [ν.IsHaarMeasure]
    (μ : Measure M) [μ.IsHaarMeasure] (i : M →* G) (hi : Continuous i) (y : G)
    (P : SchwartzBruhat (K × M) →ₗ[ℂ] SchwartzBruhat G)
    (D : Distribution G) (τ : Representation ℂ K X) (hτ : IsSmooth τ)
    (σ : Representation ℂ M Y) (hσ : IsSmooth σ) : Prop :=
  SchwartzBruhat.IsTestPushforward ((ν.comap K.toSubgroup.subtype).prod μ) ν
    (compactSliceConjugation K i y) P →
  Distribution.IsConjugationInvariant D →
  D (Hecke.TestFunction.convolution ν (P (compactSliceTraceTest K hK σ hσ))
    (compactTraceCosetTest K hK τ hτ 1)) ≠ 0 →
  let J := K.comap i hi
  (∃ T : Representation.IntertwiningMap (τ.comp (compactSliceRestriction K i hi))
    (σ.comp J.toSubgroup.subtype), T ≠ 0) ∧
  ∃ m, D (compactTraceCosetTest K hK τ hτ (y * i m)) ≠ 0

variable [IsTopologicalGroup M] [CompactSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] [FiniteDimensional ℂ X] [FiniteDimensional ℂ Y]

theorem compactTraceDescentWitness (ν : Measure G) [ν.IsHaarMeasure]
    (μ : Measure M) [μ.IsHaarMeasure] (i : M →* G) (hi : Continuous i) (y : G)
    (P : SchwartzBruhat (K × M) →ₗ[ℂ] SchwartzBruhat G)
    (D : Distribution G) (τ : Representation ℂ K X) (hτ : IsSmooth τ)
    (σ : Representation ℂ M Y) (hσ : IsSmooth σ) :
    CompactTraceDescentWitnessStatement K hK ν μ i hi y P D τ hτ σ hσ := by
  intro hP hD hNZ
  let : IsTopologicalGroup K := inferInstanceAs (IsTopologicalGroup K.toSubgroup)
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let νK := ν.comap K.toSubgroup.subtype
  let : νK.IsHaarMeasure :=
    IsHaarMeasure.comap (mH := inferInstance) ν K.isOpen.isOpenEmbedding_subtypeVal
  let p := compactSliceConjugation K i y
  have hp : Continuous p :=
    (continuous_subtype_val.comp continuous_fst).mul (continuous_const.mul (hi.comp continuous_snd))
      |>.mul (continuous_subtype_val.comp continuous_fst).inv
  let f := compactSliceTraceTest K hK σ hσ
  let g := SchwartzBruhat.extendZero K.isOpen (compactTraceTest τ hτ)
  have hCompact (z : G) : compactTraceCosetTest K hK τ hτ z = leftTranslate z g := rfl
  have h₀ : compactTraceCosetTest K hK τ hτ 1 = g := by rw [hCompact, Hecke.TestFunction.leftTranslate_one]
  rw [h₀, Distribution.smoothedPushforwardEvaluation (νK.prod μ) ν p P hp hP D f g] at hNZ
  let h (m : M) := σ.character m * D (compactTraceCosetTest K hK τ hτ (y * i m))
  have heq (z : K × M) : f z * D (leftTranslate (p z) g) = h z.2 := by
    have hf : f z = σ.character z.2 := by
      change (1 : ℂ) * compactTraceTest σ hσ z.2 = _
      rw [one_mul, compactTraceTest_apply]
      rfl
    rw [hf, ← hCompact]
    exact congrArg (σ.character z.2 * ·) (eval_conj_compactTraceCoset K hK τ hτ D hD z.1 (y * i z.2))
  have hc : Continuous (h ∘ (Prod.snd : K × M → M)) := by
    have hd := (Distribution.isLocallyConstant_eval_leftTranslate D g).comp_continuous hp
    exact (f.continuous.mul hd.continuous).congr heq
  have hint : Integrable (fun z : K × M => h z.2) (νK.prod μ) :=
    hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hNonzero : (∫ m, h m ∂μ) ≠ 0 := by
    intro hzero
    apply hNZ
    calc
      _ = ∫ z : K × M, h z.2 ∂νK.prod μ :=
        integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = _ := by
        rw [integral_prod _ hint]
        change (∫ _ : K, (∫ m, h m ∂μ) ∂νK) = 0
        rw [hzero]
        exact integral_zero K ℂ
  exact compactTraceDescentPairing μ K hK τ hτ σ D i hi y hσ hNonzero

omit [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] in
/-- When the pushforward test is fixed by a finite sum of compact character
smoothing operators, one of its types gives the two descent witnesses. -/
theorem compactTraceDescentWitness_of_finiteSmoothing
    (ν : Measure G) [ν.IsHaarMeasure] (μ : Measure M) [μ.IsHaarMeasure]
    (i : M →* G) (hi : Continuous i) (y : G)
    (P : SchwartzBruhat (K × M) →ₗ[ℂ] SchwartzBruhat G) (D : Distribution G)
    (σ : Representation ℂ M Y) (hσ : IsSmooth σ)
    {I : Type*} (S : Finset I) (V : I → Type*) [∀ r, AddCommGroup (V r)]
    [∀ r, Module ℂ (V r)] [∀ r, FiniteDimensional ℂ (V r)]
    (τ : ∀ r, Representation ℂ K (V r)) (hτ : ∀ r, IsSmooth (τ r)) (c : I → ℂ)
    (hP : SchwartzBruhat.IsTestPushforward ((ν.comap K.toSubgroup.subtype).prod μ) ν
      (compactSliceConjugation K i y) P)
    (hD : Distribution.IsConjugationInvariant D)
    (hFixed : Hecke.TestFunction.convolution ν (P (compactSliceTraceTest K hK σ hσ))
      (∑ r ∈ S, c r • compactTraceCosetTest K hK (τ r) (hτ r) 1) =
        P (compactSliceTraceTest K hK σ hσ))
    (hNZ : D (P (compactSliceTraceTest K hK σ hσ)) ≠ 0) :
    let J := K.comap i hi
    ∃ r ∈ S, (∃ T : Representation.IntertwiningMap ((τ r).comp (compactSliceRestriction K i hi))
      (σ.comp J.toSubgroup.subtype), T ≠ 0) ∧
      ∃ m, D (compactTraceCosetTest K hK (τ r) (hτ r) (y * i m)) ≠ 0 := by
  let h := P (compactSliceTraceTest K hK σ hσ)
  let C := D.comp (Hecke.TestFunction.convolutionBilinear ν h)
  have hNZ' : C (∑ r ∈ S, c r • compactTraceCosetTest K hK (τ r) (hτ r) 1) ≠ 0 := by
    change D (Hecke.TestFunction.convolution ν h _) ≠ 0
    rwa [hFixed]
  simp only [_root_.map_sum, map_smul, smul_eq_mul] at hNZ'
  obtain ⟨r, hr, hrNZ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hNZ'
  exact ⟨r, hr, compactTraceDescentWitness K hK ν μ i hi y P D (τ r) (hτ r) σ hσ hP hD
    (right_ne_zero_of_mul hrNZ)⟩

end Langlands.Character

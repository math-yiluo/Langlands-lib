import Langlands.Representation.Hecke.NormalizedIndicator
import Langlands.HarmonicAnalysis.Distribution.CharacterAverageSurjectiveStatement
import Langlands.Representation.Twist.ContinuousCharacterProof
import Langlands.Topology.CompactOpen.NeighborhoodBasis

/-!
# Proof that character-weighted product averaging is surjective

Proves `SchwartzBruhat.CharacterAverageSurjectiveStatement`. A compact open subgroup `K`
lies in the kernel of `χ`; for `f` a test function on `Y`, the tensor
`(g₁, (y, g₂)) ↦ c⁻¹ 1_K(g₁) * f y * c⁻¹ 1_K(g₂)` with `c = μ K` averages to `f`.
See the paired Markdown.
-/

noncomputable section

open MeasureTheory Function Topology

namespace Langlands.HarmonicAnalysis.SchwartzBruhat

universe uG uY

section Helpers

variable {G : Type uG} {Y : Type uY} [TopologicalSpace G] [TopologicalSpace Y]

/-- The tensor `(g₁, (y, g₂)) ↦ φ g₁ * f y * ψ g₂` of test functions on `G`, `Y`, `G`,
on the right-associated product `G × (Y × G)`. Its support lies in the compact closed set
`support φ ×ˢ (support f ×ˢ support ψ)`; no separation property of `Y` is used. -/
def tripleTensor (φ : SchwartzBruhat G) (f : SchwartzBruhat Y) (ψ : SchwartzBruhat G) :
    SchwartzBruhat (G × (Y × G)) :=
  ⟨fun q => φ q.1 * f q.2.1 * ψ q.2.2,
    ((φ.locallyConstant.comp_continuous continuous_fst).comp₂
        (f.locallyConstant.comp_continuous (continuous_fst.comp continuous_snd)) (· * ·)).comp₂
      (ψ.locallyConstant.comp_continuous (continuous_snd.comp continuous_snd)) (· * ·),
    HasCompactSupport.intro'
      ((Hecke.TestFunction.isCompact_support φ).prod
        ((Hecke.TestFunction.isCompact_support f).prod (Hecke.TestFunction.isCompact_support ψ)))
      ((Hecke.TestFunction.isClopen_support φ).isClosed.prod
        ((Hecke.TestFunction.isClopen_support f).isClosed.prod
          (Hecke.TestFunction.isClopen_support ψ).isClosed))
      (fun q hq => by
        by_contra h
        simp only [mul_eq_zero, not_or] at h
        exact hq (Set.mem_prod.mpr ⟨h.1.1, Set.mem_prod.mpr ⟨h.1.2, h.2⟩⟩))⟩

@[simp]
theorem tripleTensor_apply (φ : SchwartzBruhat G) (f : SchwartzBruhat Y) (ψ : SchwartzBruhat G)
    (q : G × (Y × G)) : tripleTensor φ f ψ q = φ q.1 * f q.2.1 * ψ q.2.2 := rfl

variable [Group G] [IsTopologicalGroup G] [MeasurableSpace G]

theorem normalizedCharacteristic_apply (μ : Measure G) (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (g : G) :
    Hecke.HeckeAlgebra.normalizedIndicator μ K hK g =
      (K : Set G).indicator (fun _ => ((μ.real (K : Set G) : ℂ)⁻¹)) g := by
  change ((μ.real (K : Set G) : ℂ)⁻¹) * Hecke.TestFunction.characteristic K.isClopen hK g = _
  rw [Hecke.TestFunction.characteristic_apply]
  by_cases hg : g ∈ (K : Set G)
  · simp [Set.indicator_of_mem hg]
  · simp [Set.indicator_of_notMem hg]

variable [BorelSpace G]

/-- If `χ` is trivial on a compact open subgroup `K`, the average of the tensor of
`f` with the normalized characteristic function of `K` on both outer factors is `f`. -/
theorem characterAverage_tripleTensor_normalizedCharacteristic (χ : ContinuousMonoidHom G ℂˣ)
    (μ : Measure G) [μ.IsHaarMeasure] [SFinite μ] (K : OpenSubgroup G)
    (hK : IsCompact (K : Set G)) (hχ : ∀ g ∈ K, χ g = 1) (f : SchwartzBruhat Y) :
    characterAverage χ μ
        (tripleTensor (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)) =
      f := by
  set c : ℂ := (μ.real (K : Set G) : ℂ) with hc_def
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Hecke.HeckeAlgebra.compactOpen_mass_pos μ K hK).ne'
  have hKm : MeasurableSet (K : Set G) := K.isOpen.measurableSet
  refine Hecke.TestFunction.ext fun y => ?_
  rw [characterAverage_apply]
  have hint : (fun z : G × G =>
      tripleTensor (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f (Hecke.HeckeAlgebra.normalizedIndicator μ K hK)
          (z.1, (y, z.2)) * ((χ z.1 : ℂ) * (χ z.2 : ℂ))⁻¹) =
      ((K : Set G) ×ˢ (K : Set G)).indicator (fun _ => c⁻¹ * f y * c⁻¹) := by
    funext z
    erw [tripleTensor_apply, normalizedCharacteristic_apply, normalizedCharacteristic_apply]
    by_cases h₁ : z.1 ∈ (K : Set G) <;> by_cases h₂ : z.2 ∈ (K : Set G)
    · rw [Set.indicator_of_mem h₁, Set.indicator_of_mem h₂,
        Set.indicator_of_mem (Set.mem_prod.mpr ⟨h₁, h₂⟩), hχ _ h₁, hχ _ h₂]
      simp [hc_def]
    · rw [Set.indicator_of_notMem h₂, Set.indicator_of_notMem
        (fun h => h₂ (Set.mem_prod.mp h).2)]
      simp
    · rw [Set.indicator_of_notMem h₁, Set.indicator_of_notMem
        (fun h => h₁ (Set.mem_prod.mp h).1)]
      simp
    · rw [Set.indicator_of_notMem h₁, Set.indicator_of_notMem
        (fun h => h₁ (Set.mem_prod.mp h).1)]
      simp
  rw [hint, integral_indicator_const _ (hKm.prod hKm)]
  have hmass : (μ.prod μ).real ((K : Set G) ×ˢ (K : Set G)) =
      μ.real (K : Set G) * μ.real (K : Set G) := by
    simp only [Measure.real, Measure.prod_prod, ENNReal.toReal_mul]
  rw [hmass, Complex.real_smul, Complex.ofReal_mul, ← hc_def]
  field_simp

end Helpers

/-- **Surjectivity of character-weighted product averaging.** For every Hausdorff, locally
compact, nonarchimedean group `G` with its Borel σ-algebra, every topological space `Y`,
every continuous character `χ` and every s-finite Haar measure `μ`, the map
`characterAverage χ μ` is surjective. -/
theorem characterAverageSurjective : CharacterAverageSurjectiveStatement.{uG, uY} := by
  intro G Y _ _ _ _ _ _ _ _ _ χ μ _ _ f
  have hker : IsOpen ((χ : G →* ℂˣ).ker : Set G) :=
    Langlands.isOpen_ker_of_continuous_complex_character (χ : G →* ℂˣ) χ.continuous
  obtain ⟨K, hK, hKker⟩ :=
    Langlands.compactOpenSubgroupBasis G _ (hker.mem_nhds (χ : G →* ℂˣ).ker.one_mem)
  exact ⟨tripleTensor (Hecke.HeckeAlgebra.normalizedIndicator μ K hK) f (Hecke.HeckeAlgebra.normalizedIndicator μ K hK),
    characterAverage_tripleTensor_normalizedCharacteristic χ μ K hK
      (fun g hg => (χ : G →* ℂˣ).mem_ker.mp (hKker hg)) f⟩

end Langlands.HarmonicAnalysis.SchwartzBruhat

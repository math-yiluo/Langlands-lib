import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical
import Langlands.Analysis.Local.ModularCompactAverage

/-! # The pairing on `I_P^G 1` and `Ξ(g⁻¹) = Ξ(g)`

Waldspurger 2003, I.1, I.3, II.1 and II.1.4. For `G = P K` with `K` compact, the functional
`∫_{P\G}` of I.1 on functions `φ(p x) = δ_P(p) φ(x)` is written as the average
`compactAverage K φ = ∫_K φ(k) dk`, and the bilinear form of I.3 on `I_P^G 1` as
`inducedPairing K f₁ f₂ = ∫_K f₁(k) f₂(k) dk`. For a unimodular group with `P` closed,
`K` compact open, and `δ_P` the modular character of `P`, both are invariant under right
translation. The spherical function satisfies `Ξ(g) = ⟨ρ(g) e, e⟩`, and hence
`Ξ(g⁻¹) = Ξ(g)` (Lemma II.1.4).
-/

noncomputable section

open MeasureTheory Measure TopologicalSpace
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]

section Haar

/-- On a group with trivial modular character, the Haar measure is right invariant. -/
theorem isMulRightInvariant_haar (hG : ∀ g : G, modularCharacter g = 1) :
    (haar : Measure G).IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  rw [ModularCompactAverage.map_mul_right_eq_modularCharacter_smul, hG, one_smul]

variable {K : Subgroup G} [CompactSpace K]

omit [LocallyCompactSpace G] in
/-- On a compact open subgroup `K`, a Haar measure `μ` of `G` restricts to `μ(K)` times the
Haar measure of `K` of total mass one. -/
theorem comap_subtype_eq_smul_normalizedHaar (hK : IsOpen (K : Set G)) (μ : Measure G)
    [IsHaarMeasure μ] :
    μ.comap ((↑) : K → G) = μ K • normalizedHaar K := by
  have : SecondCountableTopology K :=
    TopologicalSpace.Subtype.secondCountableTopology (K : Set G)
  have : IsHaarMeasure (μ.comap ((↑) : K → G)) :=
    IsHaarMeasure.comap (mH := inferInstance) μ (f := K.subtype) hK.isOpenEmbedding_subtypeVal
  have hu : μ.comap ((↑) : K → G) Set.univ = μ K := by
    have h' := comap_subtype_coe_apply hK.measurableSet μ (Set.univ : Set (K : Set G))
    rw [Set.image_univ, Subtype.range_coe] at h'
    exact h'
  have h := haarMeasure_unique (μ.comap ((↑) : K → G)) ⊤
  rw [PositiveCompacts.coe_top, hu] at h
  exact h

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- The modular character of a closed subgroup `P` is trivial on `P ∩ K` for every compact
open subgroup `K` of `G`. -/
theorem modularCharacter_eq_one_of_mem_compactOpen {P : Subgroup G}
    (hP : IsClosed (P : Set G)) [LocallyCompactSpace P] (hK : IsOpen (K : Set G))
    (p : P) (hp : (p : G) ∈ K) : modularCharacter p = 1 := by
  have : SecondCountableTopology P :=
    TopologicalSpace.Subtype.secondCountableTopology (P : Set G)
  have hKc : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  exact ModularCompactAverage.modularCharacter_eq_one_of_mem (K.comap P.subtype)
    (hK.preimage continuous_subtype_val)
    (hP.isClosedEmbedding_subtypeVal.isCompact_preimage hKc) hp

end Haar

section Average

variable (K : Subgroup G) [CompactSpace K]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The functional `∫_{P\G}` of Waldspurger I.1 on functions `φ` with
`φ(p x) = δ_P(p) φ(x)`, written as the average of `φ` over `K` for the Haar measure of `K`
of total mass one (`G = P K`). -/
def compactAverage (φ : G → ℂ) : ℂ :=
  ∫ k : K, φ k ∂(normalizedHaar K)

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
/-- The bilinear form `⟨f₁, f₂⟩ = ∫_{P\G} f₁(g) f₂(g) dg` of Waldspurger I.3 on `I_P^G 1`,
written as the average over `K`. -/
def inducedPairing (f₁ f₂ : G → ℂ) : ℂ :=
  compactAverage K fun x => f₁ x * f₂ x

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
theorem inducedPairing_comm (f₁ f₂ : G → ℂ) :
    inducedPairing K f₁ f₂ = inducedPairing K f₂ f₁ := by
  simp only [inducedPairing, mul_comm]

variable {K} {P : Subgroup G} [LocallyCompactSpace P]

/-- **Invariance of the compact average.** Let `G` be unimodular, `P` closed, `K` compact
open and `G = P K`. If `φ` is continuous and `φ(q x) = Δ_P(q) φ(x)` for the modular
character `Δ_P` of `P`, then `∫_K φ(k g) dk = ∫_K φ(k) dk`. -/
theorem compactAverage_mul_right (hG : ∀ g : G, modularCharacter g = 1)
    (hP : IsClosed (P : Set G)) (hK : IsOpen (K : Set G)) (hPK : IsIwasawaPair P K)
    (φ : G → ℂ) (hφ : Continuous φ)
    (hcov : ∀ (q : P) (x : G),
      φ ((q : G) * x) = (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * φ x)
    (g : G) :
    compactAverage K (fun x => φ (x * g)) = compactAverage K φ := by
  have := isMulRightInvariant_haar hG
  set μ : Measure G := haar
  have hKc : IsCompact (K : Set G) := isCompact_iff_compactSpace.mpr ‹_›
  have h := ModularCompactAverage.setIntegral_mul_right_eq μ P hP K hK hKc hPK φ hφ hcov g
  have h1 := integral_subtype_comap (μ := μ) hK.measurableSet (fun x => φ (x * g))
  have h2 := integral_subtype_comap (μ := μ) hK.measurableSet φ
  have h3 := h1.trans (h.trans h2.symm)
  change ∫ k : K, φ ((k : G) * g) ∂(μ.comap ((↑) : K → G)) =
    ∫ k : K, φ k ∂(μ.comap ((↑) : K → G)) at h3
  rw [comap_subtype_eq_smul_normalizedHaar hK μ, integral_smul_measure,
    integral_smul_measure] at h3
  have hpos : (μ K).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.mpr ⟨(hK.measure_pos μ ⟨1, K.one_mem⟩).ne', hKc.measure_lt_top.ne⟩
  exact (smul_right_inj hpos).mp h3

/-- **Invariance of the pairing** (Waldspurger I.3, for the trivial representation of the
Levi factor). If `f₁` and `f₂` are continuous and `f(q x) = Δ_P(q)^{1/2} f(x)`, then
`⟨ρ(g) f₁, ρ(g) f₂⟩ = ⟨f₁, f₂⟩` for the right translation `ρ(g) f = f(· g)`. -/
theorem inducedPairing_mul_right (hG : ∀ g : G, modularCharacter g = 1)
    (hP : IsClosed (P : Set G)) (hK : IsOpen (K : Set G)) (hPK : IsIwasawaPair P K)
    (f₁ f₂ : G → ℂ) (hf₁ : Continuous f₁) (hf₂ : Continuous f₂)
    (hcov₁ : ∀ (q : P) (x : G),
      f₁ ((q : G) * x) = ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ) * f₁ x)
    (hcov₂ : ∀ (q : P) (x : G),
      f₂ ((q : G) * x) = ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ) * f₂ x)
    (g : G) :
    inducedPairing K (fun x => f₁ (x * g)) (fun x => f₂ (x * g)) = inducedPairing K f₁ f₂ := by
  refine compactAverage_mul_right hG hP hK hPK (fun x => f₁ x * f₂ x)
    (hf₁.mul hf₂) (fun q x => ?_) g
  have hsq : ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ) *
      ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ) =
      (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← NNReal.coe_mul, NNReal.mul_self_sqrt]
  show f₁ ((q : G) * x) * f₂ ((q : G) * x) =
    (((modularCharacter q : ℝ≥0) : ℝ) : ℂ) * (f₁ x * f₂ x)
  rw [hcov₁, hcov₂, ← hsq]
  ring

end Average

section Spherical

variable {P K : Subgroup G} [LocallyCompactSpace P] [CompactSpace K]
  {hPK : IsIwasawaPair P K} {δ : P →* ℝ≥0ˣ}

omit [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] in
/-- A character equal to the modular character of a closed subgroup `P` is trivial on
`P ∩ K`. -/
theorem modular_eq_one_of_mem (hP : IsClosed (P : Set G)) (hK : IsOpen (K : Set G))
    (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p) (p : P) (hp : (p : G) ∈ K) :
    δ p = 1 := by
  apply Units.ext
  rw [hδ p, modularCharacter_eq_one_of_mem_compactOpen hP hK p hp, Units.val_one]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [LocallyCompactSpace P] in
/-- `Ξ(g) = ⟨ρ(g) e, e⟩` (Waldspurger II.1), for the pairing `inducedPairing` and the
function `e(p k) = δ(p)^{1/2}`. -/
theorem xi_eq_inducedPairing (hδ : ∀ p : P, (p : G) ∈ K → δ p = 1) (g : G) :
    (xi hPK δ g : ℂ) = inducedPairing K (fun x => (iwasawaWeight hPK δ (x * g) : ℂ))
      (fun x => (iwasawaWeight hPK δ x : ℂ)) := by
  unfold xi inducedPairing compactAverage
  rw [← integral_complex_ofReal]
  congr 1
  funext k
  simp only [iwasawaWeight_of_mem hδ k.2, Complex.ofReal_one, mul_one]

/-- **Waldspurger, Lemma II.1.4**: `Ξ(g⁻¹) = Ξ(g)`, for `Ξ` built from the modular
character of `P` on a unimodular group. -/
theorem xi_inv (hG : ∀ g : G, modularCharacter g = 1) (hP : IsClosed (P : Set G))
    (hK : IsOpen (K : Set G)) (hδ : ∀ p : P, (δ p : ℝ≥0) = modularCharacter p) (g : G) :
    xi hPK δ g⁻¹ = xi hPK δ g := by
  have hδK := modular_eq_one_of_mem hP hK hδ
  have hw : Continuous (iwasawaWeight hPK δ) := continuous_iwasawaWeight hδK hK
  have hcont : ∀ h : G, Continuous fun x => ((iwasawaWeight hPK δ (x * h) : ℝ) : ℂ) :=
    fun h => Complex.continuous_ofReal.comp (hw.comp (continuous_id.mul continuous_const))
  have hcov : ∀ (h : G) (q : P) (x : G), ((iwasawaWeight hPK δ ((q : G) * x * h) : ℝ) : ℂ) =
      ((NNReal.sqrt (modularCharacter q) : ℝ) : ℂ) * ((iwasawaWeight hPK δ (x * h) : ℝ) : ℂ) := by
    intro h q x
    rw [mul_assoc, iwasawaWeight_mul_left hδK q, hδ q, Complex.ofReal_mul]
  have h := inducedPairing_mul_right hG hP hK hPK
    (fun x => ((iwasawaWeight hPK δ (x * g) : ℝ) : ℂ)) (fun x => ((iwasawaWeight hPK δ x : ℝ) : ℂ))
    (hcont g) (Complex.continuous_ofReal.comp hw) (hcov g)
    (fun q x => by simpa using hcov 1 q x) g⁻¹
  simp only [inv_mul_cancel_right] at h
  apply Complex.ofReal_injective
  rw [xi_eq_inducedPairing hδK g⁻¹, xi_eq_inducedPairing hδK g, ← h, inducedPairing_comm]

end Spherical

end Langlands.HarishChandraSchwartz

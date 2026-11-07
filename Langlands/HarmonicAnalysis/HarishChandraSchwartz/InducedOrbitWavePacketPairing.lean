import Langlands.HarmonicAnalysis.HarishChandraSchwartz.OrbitWavePacket
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierCoherence
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientConvergence
import Langlands.Representation.Plancherel.ProductInducedOrbitForm

/-! # The pairing of a wave packet with `C(G)` (Waldspurger, proof of Proposition VII.2.2)

Waldspurger, proof of Proposition VII.2.2 (printed p. 319): for `ψ' ∈ C^∞(O', P')`,
`(f_{ψ'}, f)_G = ∫_G ∫_{O'} µ(ω') conj((E^G_{P'} ψ'_{ω'})(g)) dω' f(g) dg`; by Lemma VI.2.2 the
double integral converges absolutely, so
`(f_{ψ'}, f)_G = ∫_{O'} µ(ω') (E^G_{P'} ψ'_{ω'}, f)_G dω'`, and by Lemma VII.1.1 (ii) this is
formula (1), `(f_{ψ'}, f)_G = ∫_{O'} µ(ω') (ψ'_{ω'}, f̂(ω', P')) dω'`.
Waldspurger takes `f = f_ψ`; the argument holds for every `f ∈ C(G)`.

Here the wave packet is `inducedOrbitWavePacket` (`OrbitWavePacket`), with an arbitrary weight
`w` on the orbit in place of `µ`, `(φ₁, φ₂)_G = ∫_G conj(φ₁(g)) φ₂(g) dg` is `pairing`, `f̂(ω, P)`
at the representatives of the classes of the orbit is `fourierOrbitSection`, and `( , )` on
`L(ω, P)` is `unitaryOrbitRepresentativeProductForm` at a representative and
`unitaryOrbitProductPairing` on the orbit; `unitaryOrbitWeightedProductPairing` is
`∫_O w(ω) (ψ'_ω, ψ_ω) dω`. The weight `Ξ` of `C(G)` is the function `xi` of the
Iwasawa data, the weight of Lemma VI.2.2. The weight `w` enters conjugated, because
`( , )_G` is conjugate-linear in its first argument; for the real density `µ` the conjugation
disappears.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

/-- The factorization `G = P K` in subtype form gives the form with subgroup membership used by
`fourierOrbitSection`. -/
theorem factorization_mem_of_subtype {G : Type uG} [Group G] [TopologicalSpace G]
    {P : Subgroup G} {K : OpenSubgroup G} (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G)) :
    ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k := fun g => by
  obtain ⟨p, k, hg⟩ := hPK g
  exact ⟨p, p.2, k, k.2, hg⟩

/-- `(φ₂, φ₁)_G = conj (φ₁, φ₂)_G` for all functions `φ₁ φ₂ : G → ℂ`. -/
theorem pairing_conj_symm {G : Type uG} [MeasurableSpace G] (μ : Measure G) (φ₁ φ₂ : G → ℂ) :
    pairing μ φ₂ φ₁ = conj (pairing μ φ₁ φ₂) := by
  rw [pairing, pairing, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  simp only [map_mul, Complex.conj_conj]
  ring

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ p : P, ∃ k : K, g = (p : G) * (k : G))
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ p : P, Measure.modularCharacter p =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer p : ℝ≥0))
  {I : Type uI} (ν : I → (M →* ℝ≥0ˣ))
  (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := M))
  (hν : ∀ i, Continuous (ν i)) (hr : Continuous h.projection)
  {J : Type uJ} [Fintype J] (e : unitaryUnramifiedCharacters ν ≃* (J → Circle))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]
  (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  [μ.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)
  (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  {μG : Measure G} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [MeasurableInv G]
  [μG.IsInvInvariant] {σ : G → ℝ} (hwt : L2Weights μG (xi hP₀K δ₀) σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π, HasTemperedCoefficients (xi hP₀K δ₀) σ
    ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)

omit [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))] in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Lemma VII.1.1 (ii) at a representative of the orbit**: for a smooth section `ψ = q` over
the orbit of `π`, a representative `A` of a class `ω` of the orbit and `f ∈ C(G)`,
`(E^G_P ψ_ω, f)_G = (ψ_A, f̂(A, P))`, for the product of V.2 on `L(A, P)`. -/
theorem pairing_unitaryOrbitCoefficientMap_representative
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ) (A : UnitaryOrbitRepresentative ν π) :
    pairing μG (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)) f =
      (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A).inner
        (q.val A)
        (fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof C
          hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f A) := by
  rw [pairing, unitaryOrbitCoefficientMap_representative]
  exact integral_conj_coefficientMap_mul_eq_inner h hU hP hr K hK
    (factorization_mem_of_subtype hPK) hG hδ A.val.obj hcof C hC μ
    (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq A) A.val.property.1 hwt (hT A)
    hΞ hσ (q.val A) f

omit [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))] in
/-- **Lemma VII.1.1 (ii) on the orbit**: if the section `ψ_f[O, P] = (f̂(ω, P))_ω` is given by a
smooth section `r`, then `(E^G_P ψ_ω, f)_G = (ψ_ω, f̂(ω, P))` at every class `ω` of the
orbit, for the scalar pairing `unitaryOrbitProductPairing` of `ψ = q` and `r`. -/
theorem pairing_unitaryOrbitCoefficientMap_eq_productPairing
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ)
    (hrf : r.val = fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν
      π hcof C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    pairing μG (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω) f =
      unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω := by
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [pairing_unitaryOrbitCoefficientMap_representative h hU hP K hK hPK hG hδ ν π hν hr e hcof C
    hC μ hsq hP₀K hwt hT hΞ hσ q f A, unitaryOrbitProductPairing_representative, hrf]

omit [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [MeasurableInv G] [μG.IsInvInvariant] in
include hwt in
/-- **Absolute convergence of the double integral** (Waldspurger, proof of Proposition VII.2.2,
from Lemma VI.2.2): for a finite character measure, a bounded almost everywhere strongly
measurable weight `w` and continuous Laurent torus coordinates, the function
`(g, ω) ↦ conj(w(ω)) conj((E^G_P ψ_ω)(g)) f(g)` is integrable on `G × O`. -/
theorem integrable_pairing_inducedOrbitWavePacket_integrand [SFinite μG] [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ) :
    Integrable (Function.uncurry fun (g : G)
        (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) =>
        conj (w ω) *
          (conj (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g) *
            f g))
      (μG.prod (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ)) := by
  have := isFiniteMeasure_discreteSeriesOrbitMeasure ν π C hC μ hsq ρ
  obtain ⟨c, hc, hbd⟩ := exists_norm_unitaryOrbitCoefficientMap_le_xi h hU hP K hK hPK hG hδ ν π
    hν hr e C hC μ hsq hδU hL hP₀K hMK hδ₀ hcoeff q
  have hfi : Integrable (fun g => f g * ((xi hP₀K δ₀ g : ℝ) : ℂ)) μG :=
    Space.integrable_mul hwt (Complex.continuous_ofReal.comp (continuous_xi hδ₀ K.isOpen))
      (r := 0) ((nu_zero_ofReal_le_one hwt.pos).trans_lt ENNReal.one_lt_top).ne f
  have hmE : Measurable (Function.uncurry fun (g : G)
      (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) =>
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun ω => (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
        ω).continuous)
      (fun g => (continuous_unitaryOrbitCoefficient h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq
        hLaurent he q g).measurable)
  refine Integrable.mono' ((hfi.norm.const_mul (|b| * c)).comp_fst _) ?_
    (Filter.Eventually.of_forall fun x => ?_)
  · exact ((Complex.continuous_conj.comp_aestronglyMeasurable hwm).comp_snd).mul
      ((Complex.continuous_conj.measurable.comp hmE).aestronglyMeasurable.mul
        (Space.continuous f).aestronglyMeasurable.comp_fst)
  · have hxi : 0 < xi hP₀K δ₀ x.1 := hwt.pos x.1
    have hE := hbd x.2 x.1
    change ‖conj (w x.2) *
        (conj (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q x.2 x.1) *
          f x.1)‖ ≤ |b| * c * ‖f x.1 * ((xi hP₀K δ₀ x.1 : ℝ) : ℂ)‖
    rw [norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, norm_mul,
      Complex.norm_of_nonneg hxi.le]
    calc ‖w x.2‖ *
          (‖unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q x.2 x.1‖ *
            ‖f x.1‖)
        ≤ |b| * (c * xi hP₀K δ₀ x.1 * ‖f x.1‖) := by
          refine mul_le_mul ((hwb x.2).trans (le_abs_self b)) ?_ (by positivity)
            (abs_nonneg b)
          exact mul_le_mul_of_nonneg_right hE (norm_nonneg _)
      _ = |b| * c * (‖f x.1‖ * xi hP₀K δ₀ x.1) := by ring

omit [BorelSpace (M ⧸ C)] [μ.IsInvInvariant] [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant]
  [MeasurableInv G] [μG.IsInvInvariant] in
include hwt in
/-- **The first step of formula (1)** (Waldspurger, proof of Proposition VII.2.2): by Fubini,
`(f_ψ, f)_G = ∫_O conj(w(ω)) (E^G_P ψ_ω, f)_G dω`. -/
theorem pairing_inducedOrbitWavePacket_eq_integral [SFinite μG] [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ) :
    pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f =
      ∫ ω, conj (w ω) * pairing μG
          (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω) f
        ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ := by
  have := isFiniteMeasure_discreteSeriesOrbitMeasure ν π C hC μ hsq ρ
  have hint := integrable_pairing_inducedOrbitWavePacket_integrand h hU hP K hK hPK hG hδ ν π hν
    hr e C hC μ hsq ρ w hP₀K hwt hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q f
  have hl : ∀ g, conj (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w
      q g) * f g =
      ∫ ω, conj (w ω) *
        (conj (unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g) *
          f g) ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ :=
    fun g => by
      rw [inducedOrbitWavePacket, ← integral_conj, ← integral_mul_const]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      simp only [map_mul]
      ring
  rw [pairing, integral_congr_ae (Filter.Eventually.of_forall hl), integral_integral_swap hint]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [pairing, ← integral_const_mul]

include hwt in
/-- **Formula (1) with chosen representatives** (Waldspurger, proof of Proposition VII.2.2): for
any choice `s` of a representative of each class of the orbit,
`(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_{s(ω)}, f̂(s(ω), P)) dω`. -/
theorem pairing_inducedOrbitWavePacket_eq_integral_inner [SFinite μG] [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ)
    (s : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) →
      UnitaryOrbitRepresentative ν π)
    (hs : ∀ ω, unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq (s ω) = ω) :
    pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f =
      ∫ ω, conj (w ω) *
          (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
            (s ω)).inner (q.val (s ω))
            (fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof
              C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f
              (s ω))
        ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ := by
  rw [pairing_inducedOrbitWavePacket_eq_integral h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
    w hP₀K hwt hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  have h1 := pairing_unitaryOrbitCoefficientMap_representative h hU hP K hK hPK hG hδ ν π hν hr e
    hcof C hC μ hsq hP₀K hwt hT hΞ hσ q f (s ω)
  rw [hs ω] at h1
  rw [h1]

/-- **The weighted product of two sections over the orbit** (Waldspurger, VII.2, printed p. 319):
`∫_O w(ω) (ψ'_ω, ψ_ω) dω` for the scalar pairing `unitaryOrbitProductPairing` of `ψ' = q` and
`ψ = r` and the orbit measure `discreteSeriesOrbitMeasure` of the character measure `ρ`, with an
arbitrary weight `w` in place of the Plancherel density `µ`. Waldspurger's hermitian product on
`C^∞(Θ)_inv` is a weighted sum of these integrals over the pairs `(O, P)` of `Θ`. -/
def unitaryOrbitWeightedProductPairing
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) : ℂ :=
  ∫ ω, w ω * unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω
    ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ

include hwt in
/-- **Formula (1)** (Waldspurger, proof of Proposition VII.2.2, printed p. 319): if the section
`ψ_f[O, P]` is given by a smooth section `r`, then
`(f_ψ, f)_G = ∫_O conj(w(ω)) (ψ_ω, f̂(ω, P)) dω`. -/
theorem pairing_inducedOrbitWavePacket_eq_integral_productPairing [SFinite μG]
    [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ)
    (hrf : r.val = fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν
      π hcof C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f) :
    pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f =
      unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        (fun ω => conj (w ω)) q r := by
  rw [unitaryOrbitWeightedProductPairing, pairing_inducedOrbitWavePacket_eq_integral h hU hP K hK
    hPK hG hδ ν π hν hr e C hC μ hsq ρ w hP₀K hwt hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q f]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  rw [pairing_unitaryOrbitCoefficientMap_eq_productPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof
    C hC μ hsq hP₀K hwt hT hΞ hσ q r f hrf ω]

include hwt in
/-- **Formula (1) in the other order**: if `ψ_f[O, P]` is given by a smooth section `r`, then
`(f, f_ψ)_G = ∫_O w(ω) (f̂(ω, P), ψ_ω) dω`. -/
theorem pairing_inducedOrbitWavePacket_right_eq_integral_productPairing [SFinite μG]
    [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ)
    (hrf : r.val = fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν
      π hcof C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f) :
    pairing μG f (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) =
      unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ w r
        q := by
  rw [pairing_conj_symm, pairing_inducedOrbitWavePacket_eq_integral_productPairing h hU hP K hK
    hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ w hP₀K hwt hT hΞ hσ hLaurent he hwm hwb hδU hL hMK hδ₀
    hcoeff q r f hrf, unitaryOrbitWeightedProductPairing, unitaryOrbitWeightedProductPairing,
    ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  dsimp only
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [map_mul, Complex.conj_conj, unitaryOrbitProductPairing_representative,
    unitaryOrbitProductPairing_representative,
    (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
      A).conj_inner_symm]

include hwt in
/-- **Orthogonality to the wave packets**: if `f̂(ω, P) = 0` at every representative of every
class of the orbit, then `(f_ψ, f)_G = 0` for every wave packet `f_ψ` on the orbit. -/
theorem pairing_inducedOrbitWavePacket_eq_zero [SFinite μG] [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hwb : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (f : Space (xi hP₀K δ₀) σ)
    (hf : fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof C
      hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f = 0) :
    pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q) f =
      0 := by
  rw [pairing_inducedOrbitWavePacket_eq_integral h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
    w hP₀K hwt hLaurent he hwm hwb hδU hL hMK hδ₀ hcoeff q f]
  refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans (integral_zero _ _)
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [pairing_unitaryOrbitCoefficientMap_representative h hU hP K hK hPK hG hδ ν π hν hr e hcof C
    hC μ hsq hP₀K hwt hT hΞ hσ q f A, hf]
  let B := unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A
  let := B.toInnerProductCore
  change conj (w _) * B.inner (q.val A) 0 = 0
  rw [InnerProductSpace.Core.inner_zero_right, mul_zero]

end Pairing

end Langlands.HarishChandraSchwartz

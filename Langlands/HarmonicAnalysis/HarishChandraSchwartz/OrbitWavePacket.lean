import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientTwistXi
import Langlands.Representation.Plancherel.ProductInducedOrbitCoefficientSmoothness
import Langlands.Representation.Plancherel.DiscreteSeriesOrbitMeasure

/-! # Lemma VI.2.2 on `C^∞(O, P)` and the wave packets `f_ψ` (Waldspurger, VI.2–VI.3)

Waldspurger, Lemma VI.2.2 (printed p. 298): for `ψ ∈ C^∞(O, P)` there is `C > 0` with
`|(E^G_P ψ_ω)(g)| ≤ C Ξ(g)` for all `ω ∈ O` and `g ∈ G`. Waldspurger, VI.3 (printed p. 302):
for `ψ ∈ C^∞(O, P)`, `f_ψ(g) = ∫_O µ(ω) (E^G_P ψ_ω)(g) dω`, for the measure on `O` such that
`Im X(M) → O`, `χ ↦ ω ⊗ χ`, preserves measures locally.

Here `C^∞(O, P)` is Worker 200's `productInducedSmoothOrbitSections` and `E^G_P ψ_ω` is
Worker 200's `unitaryOrbitCoefficientMap` (at every class of the orbit) and
`unitaryOrbitRepresentativeCoefficientMap` (at every representative). The module proves the
bound of Lemma VI.2.2 for both, from the uniform bound for smooth families in the compact picture
(`norm_family_coefficientMap_le_xi`, `InducedCoefficientTwistXi`). It then defines the wave packet
`inducedOrbitWavePacket` with the orbit measure `discreteSeriesOrbitMeasure` and an arbitrary
weight `w` on `O` in place of `µ`, and proves its first properties: the bound
`|f_ψ(g)| ≤ C Ξ(g)` for bounded `w` and a finite character measure, bi-invariance under a compact
open subgroup, integrability of the integrand, linearity in `ψ`, and the expression as an
integral over the characters.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] {P M U : Subgroup G} [LocallyCompactSpace P]
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

section Bound

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Fintype J] in
/-- The torus parameters of the unitary unramified characters are injective. -/
theorem unitaryTorusParameter_injective : Function.Injective (unitaryTorusParameter ν e) :=
  fun _ _ hzw => e.symm.injective (Subgroup.inclusion_injective _ hzw)

omit [LocallyCompactSpace G] [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Fintype J] in
/-- The character of a torus parameter is unitary. -/
theorem norm_unitaryTorusParameter_apply (z : J → Circle) (m : M) :
    ‖((unitaryTorusParameter ν e z).val m : ℂ)‖ = 1 :=
  (e.symm z).2.2 m

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
/-- **Lemma VI.2.2 on `C^∞(O, P)`, at every representative** (Waldspurger, printed p. 298): for
a smooth section `q` over the orbit of `π` there is `c > 0` such that for every representative
`A` of a class of the orbit and every `g ∈ G`, the coefficient `E^G_P(q_A)(g)` is at most
`c Ξ(g)` in absolute value. -/
theorem exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : UnitaryOrbitRepresentative ν π) (g : G),
      ‖unitaryOrbitRepresentativeCoefficientMap h hU hP K hK hPK hG hδ ν π hr A (q.val A) g‖ ≤
        c * xi hP₀K δ₀ g := by
  have hPK' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, k, hg⟩ := hPK g
    exact ⟨p, p.2, k, k.2, hg⟩
  let R := productInducedFamilyRestriction ν e h K hP hK hν hr hU hPK π.obj
    (productInducedOrbitPullback ν π e h hU q.val)
  have hR : R ∈ finiteSmoothFamilies J (ProductInducedCompactPicture h K π.obj) := q.property.2
  obtain ⟨c, hc, hb⟩ := norm_family_coefficientMap_le_xi h hU π.obj K hK ν hν hP hr hPK' hG hδ
    π.property.2 hδU hL hP₀K hMK hδ₀ hcoeff R hR (Function.invFun (unitaryTorusParameter ν e))
  refine ⟨c, hc, fun A g => ?_⟩
  let z := unitaryOrbitRepresentativeParameter ν π e A
  let B := unitaryOrbitParameterRepresentative ν π e z
  have hq : q.val A = productInducedCoefficientTransport h hU
      (unitaryOrbitRepresentativeEquiv ν π e A) (q.val B) := q.property.1 B A _
  rw [hq, unitaryOrbitRepresentativeCoefficientMap_transport]
  have hz : Function.invFun (unitaryTorusParameter ν e) (unitaryTorusParameter ν e z) = z :=
    Function.leftInverse_invFun (unitaryTorusParameter_injective ν e) z
  have hbz := hb (unitaryTorusParameter ν e z) (norm_unitaryTorusParameter_apply ν e z) g
  rw [hz] at hbz
  have hts : twistedSection h hU π.obj K ν hP hK hν hr (factorization_subtype hPK')
      (unitaryTorusParameter ν e z) (R z) = q.val B :=
    (productInducedCompactEquiv ν h K hP hK hν hr hU (factorization_subtype hPK')
      (unitaryTorusParameter ν e z) π.obj).symm_apply_apply (q.val B)
  rw [hts] at hbz
  exact hbz

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)

/-- **Lemma VI.2.2 on `C^∞(O, P)`** (Waldspurger, printed p. 298): for a smooth section `ψ = q`
over the orbit `O` of `π` there is `c > 0` with `|(E^G_P ψ_ω)(g)| ≤ c Ξ(g)` for all `ω ∈ O` and
`g ∈ G`. -/
theorem exists_norm_unitaryOrbitCoefficientMap_le_xi
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ c : ℝ, 0 < c ∧
      ∀ (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) (g : G),
        ‖unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g‖ ≤
          c * xi hP₀K δ₀ g := by
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitRepresentativeCoefficientMap_le_xi h hU hP K hK
    hPK hG hδ ν π hν hr e hδU hL hP₀K hMK hδ₀ hcoeff q
  refine ⟨c, hc, fun ω g => ?_⟩
  obtain ⟨A, rfl⟩ := unitaryOrbitRepresentativeDiscreteSeriesOrbit_surjective ν π C hC μ hsq ω
  rw [unitaryOrbitCoefficientMap_representative]
  exact hb A g

end Bound

section WavePacket

variable (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] (μ : Measure (M ⧸ C)) [μ.IsHaarMeasure]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC π.obj.representation μ)
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (w : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℂ)

/-- **The wave packet** of Waldspurger VI.3 (printed p. 302), with an arbitrary weight `w` on the
orbit `O` in place of the Plancherel density `µ`: for `ψ = q ∈ C^∞(O, P)`,
`f_ψ(g) = ∫_O w(ω) (E^G_P ψ_ω)(g) dω`, for the measure `discreteSeriesOrbitMeasure` on `O`
attached to a measure `ρ` on the unitary unramified characters. -/
def inducedOrbitWavePacket (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (g : G) : ℂ :=
  ∫ ω, w ω * unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g
    ∂discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G]
  [BorelSpace G] [Fintype J] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The orbit measure of a finite character measure is finite. -/
theorem isFiniteMeasure_discreteSeriesOrbitMeasure [IsFiniteMeasure ρ] :
    IsFiniteMeasure (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ) :=
  ⟨by
    rw [discreteSeriesOrbitMeasure_univ]
    refine ENNReal.mul_lt_top (ENNReal.inv_lt_top.mpr ?_) (measure_lt_top ρ _)
    exact_mod_cast Nat.card_pos⟩

/-- **The first bound for the wave packet**: for a finite measure `ρ` on the characters and a
bounded weight `w`, there is `c > 0` with `|f_ψ(g)| ≤ c Ξ(g)` for all `g ∈ G`. -/
theorem exists_norm_inducedOrbitWavePacket_le_xi [IsFiniteMeasure ρ] {b : ℝ}
    (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ c : ℝ, 0 < c ∧ ∀ g : G,
      ‖inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g‖ ≤
        c * xi hP₀K δ₀ g := by
  have := isFiniteMeasure_discreteSeriesOrbitMeasure ν π C hC μ hsq ρ
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitCoefficientMap_le_xi h hU hP K hK hPK hG hδ ν π
    hν hr e C hC μ hsq hδU hL hP₀K hMK hδ₀ hcoeff q
  set r := (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ).real
    Set.univ
  have hr0 : 0 ≤ r := measureReal_nonneg
  refine ⟨1 + |b| * c * r, by positivity, fun g => ?_⟩
  have hxi : 0 ≤ xi hP₀K δ₀ g := integral_nonneg fun k => iwasawaWeight_nonneg _
  have hle : ∀ ω, ‖w ω * unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ
      hsq e q ω g‖ ≤ |b| * (c * xi hP₀K δ₀ g) := fun ω => by
    rw [norm_mul]
    exact mul_le_mul ((hw ω).trans (le_abs_self b)) (hb ω g) (norm_nonneg _) (abs_nonneg b)
  refine (norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hle)).trans ?_
  have : |b| * (c * xi hP₀K δ₀ g) * r = (|b| * c * r) * xi hP₀K δ₀ g := by ring
  rw [this]
  nlinarith

omit [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- One compact open subgroup `H ≤ K` makes every wave packet `f_ψ` bi-invariant. -/
theorem exists_inducedOrbitWavePacket_biInvariant
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    ∃ H : OpenSubgroup G, H ≤ K ∧ IsCompact (H : Set G) ∧ ∀ (k l : H) (g : G),
      inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q
          ((k : G) * g * (l : G)) =
        inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g := by
  obtain ⟨H, hHK, hHc, hH⟩ := unitaryOrbitCoefficientMap_biInvariant h hU hP K hK hPK hG hδ ν π
    hν hr C hC μ hsq e q
  refine ⟨H, hHK, hHc, fun k l g => ?_⟩
  unfold inducedOrbitWavePacket
  simp only [hH]

/-- The integrand of the wave packet is integrable over `O` when the forward torus coordinates
are continuous and Laurent, `ρ` is finite and `w` is bounded and almost everywhere strongly
measurable. -/
theorem integrable_inducedOrbitWavePacket_integrand [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    Integrable (fun ω => w ω *
        unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g)
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ) := by
  have := isFiniteMeasure_discreteSeriesOrbitMeasure ν π C hC μ hsq ρ
  obtain ⟨c, hc, hb⟩ := exists_norm_unitaryOrbitCoefficientMap_le_xi h hU hP K hK hPK hG hδ ν π
    hν hr e C hC μ hsq hδU hL hP₀K hMK hδ₀ hcoeff q
  refine Integrable.of_bound (hwm.mul (continuous_unitaryOrbitCoefficient h hU hP K hK hPK hG hδ
    ν π hν hr e C hC μ hsq hLaurent he q g).aestronglyMeasurable) (|b| * (c * xi hP₀K δ₀ g))
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  exact mul_le_mul ((hw ω).trans (le_abs_self b)) (hb ω g) (norm_nonneg _) (abs_nonneg b)

omit [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The wave packet is homogeneous in the section. -/
theorem inducedOrbitWavePacket_smul (c : ℂ)
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w (c • q) g =
      c * inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g := by
  unfold inducedOrbitWavePacket
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [map_smul, Pi.smul_apply, LocallyConstant.coe_smul, smul_eq_mul]
  ring

/-- The wave packet is additive in the section when the integrands are integrable. -/
theorem inducedOrbitWavePacket_add [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w (q + r) g =
      inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g +
        inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w r g := by
  unfold inducedOrbitWavePacket
  rw [← integral_add
    (integrable_inducedOrbitWavePacket_integrand h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
      w hLaurent he hwm hw hδU hL hP₀K hMK hδ₀ hcoeff q g)
    (integrable_inducedOrbitWavePacket_integrand h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
      w hLaurent he hwm hw hδU hL hP₀K hMK hδ₀ hcoeff r g)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [map_add, Pi.add_apply, LocallyConstant.coe_add]
  ring

/-- **The wave packet as a linear map** `ψ ↦ f_ψ` on `C^∞(O, P)`, for continuous Laurent torus
coordinates, a finite character measure and a bounded almost everywhere strongly measurable
weight. -/
def inducedOrbitWavePacketLinear [IsFiniteMeasure ρ]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    {b : ℝ} (hw : ∀ ω, ‖w ω‖ ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m) :
    productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK →ₗ[ℂ] (G → ℂ) where
  toFun q := inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q
  map_add' q r := funext fun g => inducedOrbitWavePacket_add h hU hP K hK hPK hG hδ ν π hν hr e
    C hC μ hsq ρ w hLaurent he hwm hw hδU hL hP₀K hMK hδ₀ hcoeff q r g
  map_smul' c q := funext fun g => inducedOrbitWavePacket_smul h hU hP K hK hPK hG hδ ν π hν hr
    e C hC μ hsq ρ w c q g

omit [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- **The wave packet as an integral over the characters**: `f_ψ(g)` is `|S|⁻¹` times the
integral over `ρ` of `w(ω ⊗ χ) (E^G_P ψ_{ω ⊗ χ})(g)`, where `S` is the finite stabilizer of
the class of `π`. -/
theorem inducedOrbitWavePacket_eq_parameterIntegral
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hwm : AEStronglyMeasurable w
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ))
    (q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) (g : G) :
    inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ w q g =
      (Nat.card (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq)) : ℝ)⁻¹ •
        ∫ χ, w (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) *
          unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q
            (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq) χ) g ∂ρ := by
  have hc : (Nat.card (discreteSeriesStabilizer C hC μ ν
      (discreteSeriesClass C hC μ π hsq)) : ℝ≥0∞)⁻¹ ≠ 0 :=
    ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hwm' : AEStronglyMeasurable w (Measure.map
      (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)) ρ) :=
    ⟨hwm.mk w, hwm.stronglyMeasurable_mk, (Measure.ae_ennreal_smul_measure_iff hc).1 hwm.ae_eq_mk⟩
  have hfm : AEStronglyMeasurable (fun ω => w ω *
      unitaryOrbitCoefficientMap h hU hP K hK hPK hG hδ ν π hν hr C hC μ hsq e q ω g)
      (Measure.map (discreteSeriesOrbitMap C hC μ ν (discreteSeriesClass C hC μ π hsq)) ρ) :=
    hwm'.mul (continuous_unitaryOrbitCoefficient h hU hP K hK hPK hG hδ ν π hν hr e C
      hC μ hsq hLaurent he q g).aestronglyMeasurable
  unfold inducedOrbitWavePacket
  rw [discreteSeriesOrbitMeasure, integral_smul_measure, integral_map
    (continuous_discreteSeriesOrbitMap C hC μ ν _).aemeasurable hfm, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]

end WavePacket

end Langlands.HarishChandraSchwartz

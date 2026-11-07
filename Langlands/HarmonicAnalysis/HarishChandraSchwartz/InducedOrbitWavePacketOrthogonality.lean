import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketPairing

/-! # Pairings with wave packets detect `f̂(ω, P)` (Waldspurger, Corollary VII.2.3)

Waldspurger, proof of Corollary VII.2.3 (printed p. 319): from Proposition VII.2.2 (i) and
formula (1) of its proof, `∫_{O'} µ(ω'') (ψ'_{ω''}, f̂_ψ(ω'', P')) dω'' = 0` for every
`ψ' ∈ C^∞(O'; P')`; "Cette égalité valant pour tout `ψ'`, elle entraîne `f̂_ψ(ω'', P') = 0` pour
tout `ω'' ∈ O'`."

This module proves that deduction for a single orbit `O` and parabolic `P`, for any `f ∈ C(G)`
whose section `ψ_f[O, P]` is smooth (Proposition VII.1.3), with a bounded continuous positive
weight `u` in place of `µ`: the weighted product `∫_O u(ω) (r_ω, r_ω) dω` of a smooth section `r`
vanishes only for `r = 0` (`unitaryOrbitWeightedProductPairing_self_eq_zero_iff`), so it is a
positive definite hermitian product on `C^∞(O, P)` (`unitaryOrbitWeightedProductCore`), and if
`(f_ψ, f)_G = 0` for every wave packet `f_ψ` of weight `u` on the orbit, then `f̂(ω, P) = 0` at
every representative.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

/-- The orbit measure of a measure positive on nonempty open sets is positive on nonempty open
sets: the orbit map is continuous and surjective, and the factor `|S|⁻¹` is nonzero. -/
theorem isOpenPosMeasure_discreteSeriesOrbitMeasure {G : Type uG} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] {I : Type uI} (ν : I → (G →* ℝ≥0ˣ)) (A : Subgroup G) [A.Normal]
    (hA : A ≤ Subgroup.center G) [MeasurableSpace (G ⧸ A)] (mu : Measure (G ⧸ A))
    [mu.IsHaarMeasure] (omega : DiscreteSeriesClass A hA mu)
    [Finite (discreteSeriesStabilizer A hA mu ν omega)]
    (ρ : Measure (unitaryUnramifiedCharacters ν)) [ρ.IsOpenPosMeasure] :
    (discreteSeriesOrbitMeasure ν A hA mu omega ρ).IsOpenPosMeasure := by
  have := (continuous_discreteSeriesOrbitMap A hA mu ν omega).isOpenPosMeasure_map (μ := ρ)
    (isOpenQuotientMap_discreteSeriesOrbitMap A hA mu ν omega).surjective
  exact Measure.isOpenPosMeasure_smul (μ := Measure.map _ ρ) (by simp)

section Orthogonality

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
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))]
  (ρ : Measure (unitaryUnramifiedCharacters ν))
  (u : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq) → ℝ)

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- The orbit pairing is additive in its first section. -/
theorem unitaryOrbitProductPairing_add_left
    (q q' r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e (q + q') r ω =
      unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω +
        unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q' r ω := by
  simp only [unitaryOrbitProductPairing, Submodule.coe_add, Pi.add_apply]
  exact (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
    _).add_left _ _ _

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- The orbit pairing is conjugate-linear for scalars in its first section. -/
theorem unitaryOrbitProductPairing_smul_left (c : ℂ)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e (c • q) r ω =
      conj c *
        unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω := by
  simp only [unitaryOrbitProductPairing, Submodule.coe_smul, Pi.smul_apply]
  exact (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
    _).smul_left _ _ _

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- The orbit pairing is hermitian: `conj (r_ω, q_ω) = (q_ω, r_ω)`. -/
theorem unitaryOrbitProductPairing_conj_symm
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    conj (unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e r q ω) =
      unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω :=
  (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
    _).conj_inner_symm _ _

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)]
  [Finite (discreteSeriesStabilizer C hC μ ν (discreteSeriesClass C hC μ π hsq))]
  [Finite (M ⧸ (commonNormKernel ν ⊔ C))] in
/-- The orbit pairing of a section with itself has nonnegative real part. -/
theorem re_unitaryOrbitProductPairing_self_nonneg
    (r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (ω : discreteSeriesOrbit C hC μ ν (discreteSeriesClass C hC μ π hsq)) :
    0 ≤ (unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e r r
      ω).re :=
  (unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν
    _).re_inner_nonneg _

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- For a finite measure `ρ` and a bounded continuous real weight `u`, the function
`ω ↦ u(ω) (q_ω, r_ω)` is integrable on the orbit. -/
theorem integrable_ofReal_mul_unitaryOrbitProductPairing [IsFiniteMeasure ρ] (he : Continuous e)
    (hu : Continuous u) {b : ℝ} (hub : ∀ ω, |u ω| ≤ b)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    Integrable (fun ω => (u ω : ℂ) *
        unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e q r ω)
      (discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ) :=
  (integrable_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he
    ρ q r).bdd_mul (Complex.continuous_ofReal.comp hu).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact hub ω)

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- **Definiteness of the weighted product on one orbit**: for a finite measure `ρ` positive on
nonempty open sets and a bounded continuous positive weight `u`, `∫_O u(ω) (r_ω, r_ω) dω = 0`
only for `r = 0`. -/
theorem unitaryOrbitWeightedProductPairing_self_eq_zero_iff [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (he : Continuous e) (hu : Continuous u) (hupos : ∀ ω, 0 < u ω)
    {b : ℝ} (hub : ∀ ω, u ω ≤ b)
    (r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        (fun ω => (u ω : ℂ)) r r = 0 ↔ r = 0 := by
  let m := discreteSeriesOrbitMeasure ν C hC μ (discreteSeriesClass C hC μ π hsq) ρ
  have := isOpenPosMeasure_discreteSeriesOrbitMeasure ν C hC μ
    (discreteSeriesClass C hC μ π hsq) ρ
  let p := unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e r r
  have hpc : Continuous p := continuous_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof
    C hC μ hsq ν hν hr e he r r
  have hpi : Integrable (fun ω => (u ω : ℂ) * p ω) m :=
    integrable_ofReal_mul_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC
      μ hsq ρ u he hu (fun ω => (abs_of_pos (hupos ω)).symm ▸ hub ω) r r
  constructor
  · intro h0
    have h1 : ∫ ω, u ω * (p ω).re ∂m = 0 := by
      have h2 : (∫ ω, (u ω : ℂ) * p ω ∂m).re = 0 := by
        have h0' : (∫ ω, (u ω : ℂ) * p ω ∂m) = 0 := h0
        rw [h0', Complex.zero_re]
      have h3 := integral_re hpi
      simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
      rw [h3, h2]
    have hFc : Continuous fun ω => u ω * (p ω).re := hu.mul (Complex.continuous_re.comp hpc)
    have hF0 : (fun ω => u ω * (p ω).re) = 0 := by
      refine (hFc.ae_eq_iff_eq m continuous_const).mp ?_
      refine (integral_eq_zero_iff_of_nonneg (fun ω => ?_) ?_).mp h1
      · exact mul_nonneg (hupos ω).le
          (re_unitaryOrbitProductPairing_self_nonneg h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC
            μ hsq r ω)
      · simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul] using hpi.re
    refine Subtype.ext (funext fun A => ?_)
    have hA := congrFun hF0 (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)
    rw [Pi.zero_apply, mul_eq_zero] at hA
    have hre := hA.resolve_left (hupos _).ne'
    change (unitaryOrbitProductPairing h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e r r
      (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)).re = 0 at hre
    rw [unitaryOrbitProductPairing_representative] at hre
    let B := unitaryOrbitRepresentativeProductForm h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν A
    have h3 : B.inner (r.val A) (r.val A) = 0 :=
      Complex.ext hre (Complex.conj_eq_iff_im.mp (B.conj_inner_symm _ _))
    rw [ZeroMemClass.coe_zero, Pi.zero_apply]
    exact B.definite _ h3
  · rintro rfl
    rw [unitaryOrbitWeightedProductPairing]
    refine (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).trans
      (integral_zero _ _)
    have h0 := unitaryOrbitProductPairing_smul_left h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ
      hsq 0 (0 : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) 0 ω
    rw [zero_smul, map_zero, zero_mul] at h0
    change (u ω : ℂ) * _ = 0
    rw [h0, mul_zero]

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- **The weighted product on `C^∞(O, P)`** (Waldspurger, VII.2, printed p. 319, for a single
pair `(O, P)`): for a finite measure `ρ` positive on nonempty open sets and a bounded continuous
positive weight `u`, `(q, r) ↦ ∫_O u(ω) (q_ω, r_ω) dω` is a positive definite hermitian product
on the smooth sections over the orbit, conjugate-linear in its first argument. -/
@[instance_reducible]
def unitaryOrbitWeightedProductCore [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (he : Continuous e) (hu : Continuous u) (hupos : ∀ ω, 0 < u ω) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b) :
    InnerProductSpace.Core ℂ (productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) where
  inner q r := unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ
    hsq ρ (fun ω => (u ω : ℂ)) q r
  conj_inner_symm q r := by
    rw [unitaryOrbitWeightedProductPairing, unitaryOrbitWeightedProductPairing, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [map_mul, Complex.conj_ofReal, unitaryOrbitProductPairing_conj_symm]
  re_inner_nonneg r := by
    have hpi := integrable_ofReal_mul_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ ν π hν hr
      e hcof C hC μ hsq ρ u he hu (fun ω => (abs_of_pos (hupos ω)).symm ▸ hub ω) r r
    have h3 := integral_re hpi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    change 0 ≤ RCLike.re (unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e
      hcof C hC μ hsq ρ (fun ω => (u ω : ℂ)) r r)
    rw [RCLike.re_to_complex, unitaryOrbitWeightedProductPairing, ← h3]
    exact integral_nonneg fun ω => mul_nonneg (hupos ω).le
      (re_unitaryOrbitProductPairing_self_nonneg h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ
        hsq r ω)
  add_left q q' r := by
    have hb : ∀ ω, |u ω| ≤ b := fun ω => (abs_of_pos (hupos ω)).symm ▸ hub ω
    rw [unitaryOrbitWeightedProductPairing, unitaryOrbitWeightedProductPairing,
      unitaryOrbitWeightedProductPairing, ← integral_add
        (integrable_ofReal_mul_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof
          C hC μ hsq ρ u he hu hb q r)
        (integrable_ofReal_mul_unitaryOrbitProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof
          C hC μ hsq ρ u he hu hb q' r)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [unitaryOrbitProductPairing_add_left, mul_add]
  smul_left q r c := by
    rw [unitaryOrbitWeightedProductPairing, unitaryOrbitWeightedProductPairing,
      ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [unitaryOrbitProductPairing_smul_left]
    ring
  definite r hr0 := (unitaryOrbitWeightedProductPairing_self_eq_zero_iff h hU hP K hK hPK hG hδ ν
    π hν hr e hcof C hC μ hsq ρ u he hu hupos hub r).mp hr0

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The inner product of `unitaryOrbitWeightedProductCore` is the weighted orbit product. -/
theorem unitaryOrbitWeightedProductCore_inner [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (he : Continuous e) (hu : Continuous u) (hupos : ∀ ω, 0 < u ω) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b) (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (unitaryOrbitWeightedProductCore h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ u he hu
        hupos hub).inner q r =
      unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        (fun ω => (u ω : ℂ)) q r :=
  rfl

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- For the constant weight `1`, `unitaryOrbitWeightedProductCore` has the same inner product as
the unweighted orbit core `productInducedSmoothOrbitCore`. -/
theorem unitaryOrbitWeightedProductCore_one_inner [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (he : Continuous e) (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (unitaryOrbitWeightedProductCore h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        (fun _ => 1) he continuous_const (fun _ => one_pos) (b := 1) (fun _ => le_rfl)).inner q r =
      (productInducedSmoothOrbitCore h hU hP K hK hPK hG hδ π hcof C hC μ hsq ν hν hr e he
        ρ).inner q r := by
  rw [unitaryOrbitWeightedProductCore_inner, productInducedSmoothOrbitCore_inner_integral,
    unitaryOrbitWeightedProductPairing]
  simp only [Complex.ofReal_one, one_mul]

section Corollary

variable (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  {μG : Measure G} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [MeasurableInv G]
  [μG.IsInvInvariant] {σ : G → ℝ} (hwt : L2Weights μG (xi hP₀K δ₀) σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π, HasTemperedCoefficients (xi hP₀K δ₀) σ
    ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hwt in
/-- **Orthogonality to all wave packets on an orbit** (Waldspurger, proof of Corollary VII.2.3,
printed p. 319): if the section `ψ_f[O, P]` is smooth (Proposition VII.1.3) and
`(f_ψ, f)_G = 0` for every wave packet `f_ψ`, `ψ ∈ C^∞(O, P)`, of a bounded continuous positive
weight `u`, then `f̂(ω, P) = 0` at every representative of every class of the orbit. -/
theorem fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero
    [SFinite μG] [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hu : Continuous u) (hupos : ∀ ω, 0 < u ω) {b : ℝ} (hub : ∀ ω, u ω ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (f : Space (xi hP₀K δ₀) σ)
    (hsm : fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof
      C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f ∈
        productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK)
    (h0 : ∀ q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
      pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
        (fun ω => (u ω : ℂ)) q) f = 0) :
    fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof C hC μ
      (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f = 0 := by
  let r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK := ⟨_, hsm⟩
  have h1 := pairing_inducedOrbitWavePacket_eq_integral_productPairing h hU hP K hK hPK hG hδ ν π
    hν hr e hcof C hC μ hsq ρ (fun ω => (u ω : ℂ)) hP₀K hwt hT hΞ hσ hLaurent he
    (Complex.continuous_ofReal.comp hu).aestronglyMeasurable
    (fun ω => by rw [Complex.norm_real, Real.norm_of_nonneg (hupos ω).le]; exact hub ω)
    hδU hL hMK hδ₀ hcoeff r r f rfl
  have hconj : (fun ω => conj ((u ω : ℂ))) = fun ω => (u ω : ℂ) :=
    funext fun ω => Complex.conj_ofReal _
  rw [h0 r, hconj] at h1
  exact congrArg Subtype.val ((unitaryOrbitWeightedProductPairing_self_eq_zero_iff h hU hP K hK
    hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ u he hu hupos hub r).mp h1.symm)

include hwt in
/-- **Wave packets detect `f̂(ω, P)` on an orbit**: if `ψ_f[O, P]` is smooth, then
`f̂(ω, P) = 0` at every representative of every class of the orbit if and only if
`(f_ψ, f)_G = 0` for every wave packet `f_ψ` of a bounded continuous positive weight `u`. -/
theorem fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero
    [SFinite μG] [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hu : Continuous u) (hupos : ∀ ω, 0 < u ω) {b : ℝ} (hub : ∀ ω, u ω ≤ b)
    (hδU : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : π.obj) (ℓ : SmoothDual π.obj.representation),
      ∃ c : ℝ, 0 < c ∧ ∀ m, ‖ℓ.val (π.obj.representation m v)‖ ≤ c * xi hMK δ₀M m)
    (f : Space (xi hP₀K δ₀) σ)
    (hsm : fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof
      C hC μ (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f ∈
        productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    fourierOrbitSection h hU hP hr K hK (factorization_mem_of_subtype hPK) hG hδ ν π hcof C hC μ
        (unitaryOrbitRepresentative_isDiscreteSeries ν π C hC μ hsq) hwt hT hΞ hσ f = 0 ↔
      ∀ q : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK,
        pairing μG (inducedOrbitWavePacket h hU hP K hK hPK hG hδ ν π hν hr e C hC μ hsq ρ
          (fun ω => (u ω : ℂ)) q) f = 0 := by
  constructor
  · intro hf q
    exact pairing_inducedOrbitWavePacket_eq_zero h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq
      ρ (fun ω => (u ω : ℂ)) hP₀K hwt hT hΞ hσ hLaurent he
      (Complex.continuous_ofReal.comp hu).aestronglyMeasurable
      (fun ω => by rw [Complex.norm_real, Real.norm_of_nonneg (hupos ω).le]; exact hub ω)
      hδU hL hMK hδ₀ hcoeff q f hf
  · exact fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero h hU hP K
      hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ u hP₀K hwt hT hΞ hσ hLaurent he hu hupos hub hδU
      hL hMK hδ₀ hcoeff f hsm

end Corollary

end Orthogonality

end Langlands.HarishChandraSchwartz

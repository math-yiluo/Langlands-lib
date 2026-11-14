import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedOrbitWavePacketOrthogonality

/-! # Wave packets detect `f̂(ω, P)` for a weight positive on a dense set

Waldspurger, proof of Corollary VII.2.3 (printed p. 319), uses the positive definite product
`∫_O µ(ω) (ψ'_ω, ψ_ω) dω` on `C^∞(O, P)`, where `µ` is the Plancherel weight of V.2. By
Lemma V.2.1, `µ ≥ 0` on `O`, but `µ` may vanish where `j` has a unitary pole, so the Library's
`unitaryOrbitWeightedProductPairing_self_eq_zero_iff`, which assumes `0 < u` everywhere, does not
apply to `µ` as stated.

This module proves the same results for a bounded continuous weight `u ≥ 0` whose positivity set
`{ω | 0 < u ω}` is dense in the orbit:

* `unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense`: `∫_O u(ω) (r_ω, r_ω) dω = 0`
  only for `r = 0`. The integrand `u(ω) Re (r_ω, r_ω)` is continuous, nonnegative and of
  integral zero, so it vanishes; hence `Re (r_ω, r_ω) = 0` on the dense set `{u > 0}`, then on
  all of `O` by continuity, and the positive definite product at each representative gives
  `r = 0`;
* `unitaryOrbitWeightedProductCore_of_dense`: the positive definite hermitian product on
  `C^∞(O, P)`;
* `fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense` and
  `fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense`:
  wave packets of weight `u` detect `f̂(ω, P)`.

The everywhere-positive weights of `InducedOrbitWavePacketOrthogonality` are the special case
where `{u > 0}` is the whole orbit (`dense_pos_of_forall_pos`).
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel Langlands.Induction
open scoped NNReal ENNReal ComplexConjugate

namespace Langlands.HarishChandraSchwartz

universe uG uV uI uJ

/-- A function that is positive everywhere has a dense positivity set. -/
theorem dense_pos_of_forall_pos {X : Type*} [TopologicalSpace X] {u : X → ℝ}
    (hupos : ∀ x, 0 < u x) : Dense {x | 0 < u x} := by
  have hs : {x | 0 < u x} = Set.univ := Set.eq_univ_of_forall hupos
  rw [hs]
  exact dense_univ

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
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- **Definiteness of the weighted product on one orbit, for a weight positive on a dense set**:
for a finite measure `ρ` positive on nonempty open sets and a bounded continuous weight `u ≥ 0`
whose positivity set `{ω | 0 < u ω}` is dense, `∫_O u(ω) (r_ω, r_ω) dω = 0` only for `r = 0`. -/
theorem unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense [IsFiniteMeasure ρ]
    [ρ.IsOpenPosMeasure] (he : Continuous e) (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω)
    (hud : Dense {ω | 0 < u ω}) {b : ℝ} (hub : ∀ ω, u ω ≤ b)
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
      μ hsq ρ u he hu (fun ω => (abs_of_nonneg (hu0 ω)).symm ▸ hub ω) r r
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
      · exact mul_nonneg (hu0 ω)
          (re_unitaryOrbitProductPairing_self_nonneg h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC
            μ hsq r ω)
      · simpa only [RCLike.re_to_complex, Complex.re_ofReal_mul] using hpi.re
    have hre0 : (fun ω => (p ω).re) = fun _ => (0 : ℝ) := by
      refine Continuous.ext_on hud (Complex.continuous_re.comp hpc) continuous_const ?_
      intro ω hω
      have hA := congrFun hF0 ω
      rw [Pi.zero_apply, mul_eq_zero] at hA
      exact hA.resolve_left (ne_of_gt hω)
    refine Subtype.ext (funext fun A => ?_)
    have hre := congrFun hre0 (unitaryOrbitRepresentativeDiscreteSeriesOrbit ν π C hC μ hsq A)
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
/-- **The weighted product on `C^∞(O, P)` for a weight positive on a dense set** (Waldspurger,
VII.2, printed p. 319, for a single pair `(O, P)`): for a finite measure `ρ` positive on nonempty
open sets and a bounded continuous weight `u ≥ 0` with `{ω | 0 < u ω}` dense,
`(q, r) ↦ ∫_O u(ω) (q_ω, r_ω) dω` is a positive definite hermitian product on the smooth
sections over the orbit, conjugate-linear in its first argument. -/
@[instance_reducible]
def unitaryOrbitWeightedProductCore_of_dense [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (he : Continuous e) (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω})
    {b : ℝ} (hub : ∀ ω, u ω ≤ b) :
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
      e hcof C hC μ hsq ρ u he hu (fun ω => (abs_of_nonneg (hu0 ω)).symm ▸ hub ω) r r
    have h3 := integral_re hpi
    simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at h3
    change 0 ≤ RCLike.re (unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e
      hcof C hC μ hsq ρ (fun ω => (u ω : ℂ)) r r)
    rw [RCLike.re_to_complex, unitaryOrbitWeightedProductPairing, ← h3]
    exact integral_nonneg fun ω => mul_nonneg (hu0 ω)
      (re_unitaryOrbitProductPairing_self_nonneg h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ
        hsq r ω)
  add_left q q' r := by
    have hb : ∀ ω, |u ω| ≤ b := fun ω => (abs_of_nonneg (hu0 ω)).symm ▸ hub ω
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
  definite r hr0 := (unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense h hU hP K hK hPK
    hG hδ ν π hν hr e hcof C hC μ hsq ρ u he hu hu0 hud hub r).mp hr0

omit [T2Space G] [Nonempty (CompactOpenSubgroup G)] [CompactSpace (K : Subgroup G)]
  [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The inner product of `unitaryOrbitWeightedProductCore_of_dense` is the weighted orbit
product. -/
theorem unitaryOrbitWeightedProductCore_of_dense_inner [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (he : Continuous e) (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω})
    {b : ℝ} (hub : ∀ ω, u ω ≤ b)
    (q r : productInducedSmoothOrbitSections ν π e h hU K hP hK hν hr hPK) :
    (unitaryOrbitWeightedProductCore_of_dense h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        u he hu hu0 hud hub).inner q r =
      unitaryOrbitWeightedProductPairing h hU hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ
        (fun ω => (u ω : ℂ)) q r :=
  rfl

section Corollary

variable (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
  {μG : Measure G} [μG.IsMulLeftInvariant] [μG.IsMulRightInvariant] [MeasurableInv G]
  [μG.IsInvInvariant] {σ : G → ℝ} (hwt : L2Weights μG (xi hP₀K δ₀) σ)
  (hT : ∀ A : UnitaryOrbitRepresentative ν π, HasTemperedCoefficients (xi hP₀K δ₀) σ
    ((normalizedInductionFunctor h hU).obj A.val.obj).representation)
  (hΞ : ∀ g, xi hP₀K δ₀ g⁻¹ = xi hP₀K δ₀ g) (hσ : ∀ g, σ g⁻¹ = σ g)

include hwt in
/-- **Orthogonality to all wave packets on an orbit, for a weight positive on a dense set**
(Waldspurger, proof of Corollary VII.2.3, printed p. 319): if the section `ψ_f[O, P]` is smooth
(Proposition VII.1.3) and `(f_ψ, f)_G = 0` for every wave packet `f_ψ`, `ψ ∈ C^∞(O, P)`, of a
bounded continuous weight `u ≥ 0` with `{ω | 0 < u ω}` dense, then `f̂(ω, P) = 0` at every
representative of every class of the orbit. -/
theorem fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense
    [SFinite μG] [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b)
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
    (fun ω => by rw [Complex.norm_real, Real.norm_of_nonneg (hu0 ω)]; exact hub ω)
    hδU hL hMK hδ₀ hcoeff r r f rfl
  have hconj : (fun ω => conj ((u ω : ℂ))) = fun ω => (u ω : ℂ) :=
    funext fun ω => Complex.conj_ofReal _
  rw [h0 r, hconj] at h1
  exact congrArg Subtype.val ((unitaryOrbitWeightedProductPairing_self_eq_zero_iff_of_dense h hU hP
    K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ u he hu hu0 hud hub r).mp h1.symm)

include hwt in
/-- **Wave packets detect `f̂(ω, P)` on an orbit, for a weight positive on a dense set**: if
`ψ_f[O, P]` is smooth, then `f̂(ω, P) = 0` at every representative of every class of the orbit if
and only if `(f_ψ, f)_G = 0` for every wave packet `f_ψ` of a bounded continuous weight `u ≥ 0`
with `{ω | 0 < u ω}` dense. -/
theorem fourierOrbitSection_eq_zero_iff_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense
    [SFinite μG] [IsFiniteMeasure ρ] [ρ.IsOpenPosMeasure]
    (hLaurent : HasLaurentUnitaryCoordinates ν e) (he : Continuous e)
    (hu : Continuous u) (hu0 : ∀ ω, 0 ≤ u ω) (hud : Dense {ω | 0 < u ω}) {b : ℝ}
    (hub : ∀ ω, u ω ≤ b)
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
      (fun ω => by rw [Complex.norm_real, Real.norm_of_nonneg (hu0 ω)]; exact hub ω)
      hδU hL hMK hδ₀ hcoeff q f hf
  · exact fourierOrbitSection_eq_zero_of_forall_pairing_inducedOrbitWavePacket_eq_zero_of_dense h hU
      hP K hK hPK hG hδ ν π hν hr e hcof C hC μ hsq ρ u hP₀K hwt hT hΞ hσ hLaurent he hu hu0 hud
      hub hδU hL hMK hδ₀ hcoeff f hsm

end Corollary

end Orthogonality

end Langlands.HarishChandraSchwartz

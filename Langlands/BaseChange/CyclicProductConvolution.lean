import Langlands.BaseChange.CyclicProductQuotient
import Langlands.BaseChange.SplitMatchingConvolution

/-!
# Integration of compactly supported tensors in cyclic product coordinates

For a group `G` with a measure `μ`, the fibre integral `splitFiberIntegral μ Φ` of a function `Φ`
on `G^{m+1}` integrates `Φ` over the fibres of the ordered product `x ↦ x₀ ⋯ x_m`; for a tensor of
factor functions it is their ordered convolution `splitFiberConvolution μ ψ`
(`splitFiberIntegral_tensor`), which is the usual left-Haar convolution in the stated order
(`splitFiberConvolution_succ`). For a cyclic product `κ : H ≃ₜ* G^{m+1}` with a twist that shifts
the coordinates and acts by `τ` at the wrap, the twisted orbital integral of `Φ ∘ κ` at `δ` is the
`τ`-twisted orbital integral of the fibre integral of `Φ` at the ordered product of the coordinates
of `δ`, for every continuous compactly supported `Φ`
(`cyclicProductOrbitalIntegral_eq_splitFiberIntegral`); the case of tensors is
`cyclicProductConvolutionOrbitalIntegral_eq`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory _root_.Topology
open Langlands.QuotientIntegration Langlands.TraceFormula

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

section Convolution

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] {m : ℕ}

/-- The ordered convolution of factor functions, written as an integral over
the first `m` entries with the remaining entry fixed by the total product. -/
def splitFiberConvolution (μ : Measure G) (ψ : Fin (m + 1) → G → ℂ) (y : G) : ℂ :=
  ∫ w, ∏ i, ψ i (splitProductFiberChart m (y, w) i) ∂Measure.pi (fun _ : Fin m => μ)

/-- The fibre integral of `Φ` over the ordered product: `y ↦ ∫ Φ(w₀, …, w_{m-1},
(w₀ ⋯ w_{m-1})⁻¹ y) dμ^m(w)`, the integral over the first `m` coordinates with the last one fixed
by the total product. -/
def splitFiberIntegral (μ : Measure G) (Φ : (Fin (m + 1) → G) → ℂ) (y : G) : ℂ :=
  ∫ w, Φ (splitProductFiberChart m (y, w)) ∂Measure.pi (fun _ : Fin m => μ)

/-- For a tensor, the fibre integral is the ordered convolution of the factors. -/
theorem splitFiberIntegral_tensor (μ : Measure G) (ψ : Fin (m + 1) → G → ℂ) :
    splitFiberIntegral μ (fun x => ∏ i, ψ i (x i)) = splitFiberConvolution μ ψ :=
  rfl

omit [MeasurableSpace G] in
/-- The tensor `x ↦ ∏ i, ψ i (x i)` of continuous compactly supported factor functions is
continuous and compactly supported on `G^{m+1}`. -/
theorem splitTensor_continuous_hasCompactSupport
    (ψ : Fin (m + 1) → G → ℂ) (hc : ∀ i, Continuous (ψ i))
    (hs : ∀ i, HasCompactSupport (ψ i)) :
    Continuous (fun x : Fin (m + 1) → G => ∏ i, ψ i (x i)) ∧
      HasCompactSupport (fun x : Fin (m + 1) → G => ∏ i, ψ i (x i)) := by
  refine ⟨continuous_finsetProd _ (fun i _ => (hc i).comp (continuous_apply i)), ?_⟩
  exact HasCompactSupport.of_support_subset_isCompact (isCompact_univ_pi hs) (by
    intro x hx i _
    exact subset_tsupport (ψ i) (fun hz => hx (Finset.prod_eq_zero (Finset.mem_univ i) hz)))

omit [MeasurableSpace G] in
/-- A product test in continuous split coordinates is continuous and compactly supported. -/
theorem splitTensorInCoordinates_continuous_hasCompactSupport
    {H : Type u} [Group H] [TopologicalSpace H] (κ : H ≃ₜ* (Fin (m + 1) → G))
    (ψ : Fin (m + 1) → G → ℂ) (hc : ∀ i, Continuous (ψ i))
    (hs : ∀ i, HasCompactSupport (ψ i)) :
    Continuous (fun x => ∏ i, ψ i (κ x i)) ∧ HasCompactSupport (fun x => ∏ i, ψ i (κ x i)) := by
  obtain ⟨hT, hS⟩ := splitTensor_continuous_hasCompactSupport ψ hc hs
  exact ⟨hT.comp κ.continuous, hS.comp_homeomorph κ.toHomeomorph⟩

variable [BorelSpace G] [T2Space G] [SecondCountableTopology G] [LocallyCompactSpace G]

omit [LocallyCompactSpace G] [SecondCountableTopology G] in
@[simp] theorem splitFiberConvolution_zero (μ : Measure G) (ψ : Fin 1 → G → ℂ) (y : G) :
    splitFiberConvolution μ ψ y = ψ 0 y := by
  unfold splitFiberConvolution
  rw [Measure.pi_of_empty _ (Fin.elim0 : Fin 0 → G), integral_dirac]
  simp [splitProductFiberChart_apply, Fin.snoc_zero]

/-- Fiber integration uses the usual left-Haar convolution in the stated order. -/
theorem splitFiberConvolution_succ (μ : Measure G) [μ.IsHaarMeasure]
    (ψ : Fin (m + 2) → G → ℂ) (hc : ∀ i, Continuous (ψ i))
    (hs : ∀ i, HasCompactSupport (ψ i)) (y : G) :
    splitFiberConvolution μ ψ y =
      Hecke.convolutionIntegral μ (ψ 0) (splitFiberConvolution μ (Fin.tail ψ)) y := by
  let K (w : Fin (m + 1) → G) := ∏ i, ψ i (splitProductFiberChart (m + 1) (y, w) i)
  let e := (splitFinHead (G := G) m).toMeasurableEquiv
  have hy : IsClosedEmbedding (Prod.mk y : (Fin (m + 1) → G) → _) := by
    refine ⟨isEmbedding_prodMkRight y, ?_⟩
    rw [show Set.range (Prod.mk y : (Fin (m + 1) → G) → _) = Prod.fst ⁻¹' {y} by
      ext p
      rcases p with ⟨x, w⟩
      simp [eq_comm]]
    exact isClosed_singleton.preimage continuous_fst
  obtain ⟨hT, hS⟩ := splitTensor_continuous_hasCompactSupport ψ hc hs
  have hEmb := (splitProductFiberChart (m + 1)).isClosedEmbedding.comp hy
  have hK : Integrable K (Measure.pi fun _ => μ) :=
    (hT.comp hEmb.continuous).integrable_of_hasCompactSupport (hS.comp_isClosedEmbedding hEmb)
  have hm := (splitFinHead_measurePreserving μ m).symm e
  change (∫ w, K w ∂Measure.pi (fun _ : Fin (m + 1) => μ)) = _
  calc
    _ = ∫ p, K (e.symm p) ∂μ.prod (Measure.pi fun _ : Fin m => μ) :=
      (hm.integral_comp e.symm.measurableEmbedding K).symm
    _ = ∫ x, ∫ w, K (Fin.cons x w) ∂Measure.pi (fun _ : Fin m => μ) ∂μ :=
      integral_prod _ ((hm.integrable_comp_emb e.symm.measurableEmbedding).mpr hK)
    _ = Hecke.convolutionIntegral μ (ψ 0) (splitFiberConvolution μ (Fin.tail ψ)) y := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro x
      have hK' (w : Fin m → G) : K (Fin.cons x w) =
          ψ 0 x * ∏ i, Fin.tail ψ i (splitProductFiberChart m (x⁻¹ * y, w) i) := by
        have hchart : splitProductFiberChart (m + 1) (y, Fin.cons x w) =
            Fin.cons x (splitProductFiberChart m (x⁻¹ * y, w)) := by
          rw [splitProductFiberChart_apply, splitProductFiberChart_apply,
            Fin.cons_snoc_eq_snoc_cons, List.ofFn_succ]
          simp [mul_inv_rev, mul_assoc]
        simp only [K, hchart, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
      simp_rw [hK', integral_const_mul, splitFiberConvolution]

/-- Fiber integration gives a continuous compactly supported test. -/
theorem splitFiberConvolution_continuous_hasCompactSupport
    (μ : Measure G) [μ.IsHaarMeasure] (ψ : Fin (m + 1) → G → ℂ)
    (hc : ∀ i, Continuous (ψ i)) (hs : ∀ i, HasCompactSupport (ψ i)) :
    Continuous (splitFiberConvolution μ ψ) ∧ HasCompactSupport (splitFiberConvolution μ ψ) := by
  let K (p : G × (Fin m → G)) : ℂ := ∏ i, ψ i (splitProductFiberChart m p i)
  let ρ : Measure (Fin m → G) := Measure.pi fun _ => μ
  obtain ⟨hT, hS⟩ := splitTensor_continuous_hasCompactSupport ψ hc hs
  have hK : Continuous K := hT.comp (splitProductFiberChart m).continuous
  have hKS : HasCompactSupport K := hS.comp_homeomorph (splitProductFiberChart m)
  let Y := Prod.snd '' tsupport K
  have hY : IsCompact Y := hKS.image continuous_snd
  have hprop (x : G) (y : Fin m → G) (hy : y ∉ Y) : K (x, y) = 0 := by
    by_contra hz
    exact hy ⟨(x, y), subset_tsupport K hz, rfl⟩
  have hint (x : G) : (∫ w, K (x, w) ∂ρ) = ∫ w in Y, K (x, w) ∂ρ :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (hprop x)).symm
  constructor
  · change Continuous (fun x => ∫ w, K (x, w) ∂ρ)
    simp_rw [hint]
    exact continuous_parametric_integral_of_continuous (by simpa only [Function.uncurry_def] using hK) hY
  · refine HasCompactSupport.of_support_subset_isCompact (hKS.image continuous_fst) ?_
    intro x hx
    by_contra h
    apply hx
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun w => by
      change K (x, w) = 0
      by_contra hz
      exact h ⟨(x, w), subset_tsupport K hz, rfl⟩

end Convolution

section Comparison

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [MeasurableSpace H] [BorelSpace H]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G]
variable {m : ℕ} (κ : H ≃ₜ* (Fin (m + 1) → G)) (σ : H →* H) (τ : G →* G)
  (hshift : ∀ (x : H) (i : Fin m), κ (σ x) i.castSucc = κ x i.succ)
  (hwrap : ∀ x : H, κ (σ x) (Fin.last m) = τ (κ x 0)) (δ : H)

local notation "β" => List.prod (List.ofFn (κ δ))
local notation "C" => twistedCentralizer σ δ
local notation "Z" => twistedCentralizer τ β
local notation "Θ" => cyclicProductQuotientChart κ σ τ hshift hwrap δ

/-- **Orbital integrals in cyclic product coordinates.** For every continuous compactly supported
`Φ` on `G^{m+1}`, the twisted orbital integral of `Φ ∘ κ` at `δ` is the `τ`-twisted orbital
integral of the fibre integral of `Φ` at the ordered product of the coordinates of `δ`, for a
product Haar measure on `H`, corresponding centralizer measures, compatible quotient measures and a
closed `τ`-twisted orbit. -/
theorem cyclicProductOrbitalIntegral_eq_splitFiberIntegral
    (hσ : Continuous σ) (hτ : Continuous τ)
    {μ : Measure G} [μ.IsHaarMeasure] {μH : Measure H}
    (hκ : MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) => μ))
    {μC : Measure C} [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
    {μZ : Measure Z} [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
    {νC : Measure (LeftQuotient C)} {νZ : Measure (LeftQuotient Z)}
    (hνC : IsCompatible C μH μC νC) (hνZ : IsCompatible Z μ μZ νZ)
    (he : MeasurePreserving (cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ) μC μZ)
    (hOrbit : IsClosedEmbedding (twistedOrbitFunction τ β id))
    (Φ : (Fin (m + 1) → G) → ℂ) (hc : Continuous Φ) (hs : HasCompactSupport Φ) :
    twistedOrbitalIntegral σ δ νC (fun x => Φ (κ x)) =
      twistedOrbitalIntegral τ β νZ (splitFiberIntegral μ Φ) := by
  let ρ : Measure (Fin m → G) := Measure.pi fun _ => μ
  let U := twistedOrbitFunction τ β id
  let K (p : LeftQuotient Z × (Fin m → G)) : ℂ := Φ (splitProductFiberChart m (U p.1, p.2))
  let : SecondCountableTopology (LeftQuotient Z) :=
    (leftQuotient_isOpenQuotientMap Z).secondCountableTopology
  let : LocallyCompactSpace (LeftQuotient Z) := leftQuotient_locallyCompactSpace Z
  let : νZ.Regular := hνZ.regular
  have hΘ := cyclicProductQuotientChart_symm_measurePreserving
    κ σ τ hshift hwrap δ hσ hτ hκ hνC hνZ he
  have hEmb := (splitProductFiberChart m).isClosedEmbedding.comp
    (hOrbit.prodMap (IsClosedEmbedding.id (X := (Fin m → G))))
  have hK : Integrable K (νZ.prod ρ) :=
    (hc.comp hEmb.continuous).integrable_of_hasCompactSupport (hs.comp_isClosedEmbedding hEmb)
  let ΦH : H → ℂ := fun x => Φ (κ x)
  have hU (g : G) : U (leftQuotientMap Z g) = twistedConj τ g β := rfl
  have hEval (q : LeftQuotient C) : twistedOrbitFunction σ δ ΦH q = K (Θ q) := by
    induction q using Quotient.inductionOn with
    | h x =>
      change ΦH (twistedConj σ x δ) = K (Θ (leftQuotientMap C x))
      rw [cyclicProductQuotientChart_mk]
      simp only [ΦH, K, hU, splitProductFiberChart_apply,
        cyclicProductAmbientChart_twistedConj κ σ τ hshift hwrap]
  change (∫ q, twistedOrbitFunction σ δ ΦH q ∂νC) = _
  calc
    _ = ∫ p, twistedOrbitFunction σ δ ΦH ((Θ).symm p) ∂νZ.prod ρ :=
      (hΘ.integral_comp (Θ).symm.toMeasurableEquiv.measurableEmbedding _).symm
    _ = ∫ p, K p ∂νZ.prod ρ := by simp_rw [hEval, Homeomorph.apply_symm_apply]
    _ = ∫ q, ∫ w, K (q, w) ∂ρ ∂νZ := integral_prod K hK
    _ = twistedOrbitalIntegral τ β νZ (splitFiberIntegral μ Φ) := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro q
      induction q using Quotient.inductionOn with
      | h x => rfl

/-- The cyclic product tensor has the orbital integral of its ordered
convolution on the first factor: the case of tensors of
`cyclicProductOrbitalIntegral_eq_splitFiberIntegral` (`splitFiberIntegral_tensor`). -/
theorem cyclicProductConvolutionOrbitalIntegral_eq
    (hσ : Continuous σ) (hτ : Continuous τ)
    {μ : Measure G} [μ.IsHaarMeasure] {μH : Measure H}
    (hκ : MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) => μ))
    {μC : Measure C} [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
    {μZ : Measure Z} [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
    {νC : Measure (LeftQuotient C)} {νZ : Measure (LeftQuotient Z)}
    (hνC : IsCompatible C μH μC νC) (hνZ : IsCompatible Z μ μZ νZ)
    (he : MeasurePreserving (cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ) μC μZ)
    (hOrbit : IsClosedEmbedding (twistedOrbitFunction τ β id))
    (ψ : Fin (m + 1) → G → ℂ) (hc : ∀ i, Continuous (ψ i))
    (hs : ∀ i, HasCompactSupport (ψ i)) :
    twistedOrbitalIntegral σ δ νC (fun x => ∏ i, ψ i (κ x i)) =
      twistedOrbitalIntegral τ β νZ (splitFiberConvolution μ ψ) := by
  obtain ⟨hT, hS⟩ := splitTensor_continuous_hasCompactSupport ψ hc hs
  exact cyclicProductOrbitalIntegral_eq_splitFiberIntegral κ σ τ hshift hwrap δ hσ hτ hκ hνC hνZ he
    hOrbit (fun x => ∏ i, ψ i (x i)) hT hS

end Comparison

/-- Exact orbital and continuity statements for compactly supported continuous
factor tests in cyclic product coordinates. -/
def CyclicProductConvolutionStatement : Prop :=
  ∀ {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H]
    {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [T2Space G] [LocallyCompactSpace G]
    [SecondCountableTopology G] (m : ℕ) (κ : H ≃ₜ* (Fin (m + 1) → G))
    (σ : H →* H) (τ : G →* G),
    Continuous σ → Continuous τ →
    ∀ (hshift : ∀ (x : H) (i : Fin m), κ (σ x) i.castSucc = κ x i.succ)
      (hwrap : ∀ x : H, κ (σ x) (Fin.last m) = τ (κ x 0)) (δ : H),
    let y := (List.ofFn (κ δ)).prod
    let C := twistedCentralizer σ δ
    let Z := twistedCentralizer τ y
    IsClosedEmbedding (twistedOrbitFunction τ y id) →
    ∀ (μ : Measure G) [μ.IsHaarMeasure] (μH : Measure H),
      MeasurePreserving κ μH (Measure.pi fun _ : Fin (m + 1) => μ) →
    ∀ (μC : Measure C) [μC.IsHaarMeasure] [μC.IsMulRightInvariant]
      (μZ : Measure Z) [μZ.IsHaarMeasure] [μZ.IsMulRightInvariant]
      (νC : Measure (LeftQuotient C)) (νZ : Measure (LeftQuotient Z)),
      IsCompatible C μH μC νC → IsCompatible Z μ μZ νZ →
      MeasurePreserving (cyclicProductCentralizerEquiv κ σ τ hshift hwrap δ) μC μZ →
    ∀ (ψ : Fin (m + 1) → G → ℂ), (∀ i, Continuous (ψ i)) → (∀ i, HasCompactSupport (ψ i)) →
      let φ := fun x => ∏ i, ψ i (κ x i)
      let f := splitFiberConvolution μ ψ
      (Continuous φ ∧ HasCompactSupport φ) ∧
      (Continuous f ∧ HasCompactSupport f) ∧
      twistedOrbitalIntegral σ δ νC φ = twistedOrbitalIntegral τ y νZ f

theorem cyclicProductConvolution : CyclicProductConvolutionStatement.{u, v} := by
  intro H _ _ _ _ _ G _ _ _ _ _ _ _ _ m κ σ τ hσ hτ hshift hwrap δ y C Z hOrbit
    μ _ μH hκ μC _ _ μZ _ _ νC νZ hνC hνZ he ψ hc hs
  exact ⟨splitTensorInCoordinates_continuous_hasCompactSupport κ ψ hc hs,
    splitFiberConvolution_continuous_hasCompactSupport μ ψ hc hs, cyclicProductConvolutionOrbitalIntegral_eq
    κ σ τ hshift hwrap δ hσ hτ hκ hνC hνZ he hOrbit ψ hc hs⟩

end Langlands.BaseChange

import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedFourierTransform
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.ConstantTermInd
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.IwasawaIntegration
import Langlands.Representation.Plancherel.CompactProductIntegralFormula

/-! # The Fourier transform and the constant term (Waldspurger, Lemma VII.1.2)

Waldspurger VII.1 (printed p. 315): for `f ∈ C(G)` and `(ω, E)` square integrable on `M`, the
constant term `f^{(P)} ∈ C(M)` of III.6 gives `f̂^{(P),Ind}(ω) ∈ L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)`,
`f̂^{(P),Ind}(ω)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)`, where
`f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)}` and `φ ↦ φ̂(ω, M)` is the Fourier transform of `C(M)`
at `ω`. Lemma VII.1.2 states `f̂(ω, P) = f̂^{(P),Ind}(ω)`.

Here `f̂^{(P),Ind}(ω)` is `constantTermInducedFourierTransform`, built from the constant term
`Space.constantTermInd` of `ConstantTermInd` and the generic `coefficientFourierTransform` for
`M`; its covariance under `P × P` uses the modulus relation `IsConjModulus` and unimodularity of
`U`. Lemma VII.1.2 is `inducedFourierTransform_eq_constantTermInducedFourierTransform`. The proof
follows Waldspurger's: pair both sides with `ψ ∈ L(ω, P)`, apply Lemma VII.1.1 (ii) for `G` and
for `M`, and compute the integral over `G` in the coordinates `g = m u k` (the integration formula
of I.1 (2), in the Bochner form `integral_eq_integral_compact_levi_unipotent`), with the integral
over `P \ G` replaced by the integral over `K`. The absolute convergence of the double integral
over `G × K`, which Waldspurger deduces from the proof of Lemma VI.2.2 and from Lemma II.1.5, is
the hypothesis `hint`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate NNReal ENNReal TensorProduct

namespace Langlands.HarishChandraSchwartz

universe uG uV

section Iwasawa

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  {M U : Subgroup G} [SecondCountableTopology U]
  (hMU : M ≤ Subgroup.normalizer (U : Set G))
  {μ : Measure G} [SFinite μ] [μ.IsMulLeftInvariant]
  {μM : Measure M} [SFinite μM] [μM.IsMulLeftInvariant]
  {μU : Measure U} [SFinite μU] [μU.IsMulLeftInvariant]
  {K : Subgroup G} (hK : MeasurableSet (K : Set G))
  (hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ K, g = (m : G) * u * k)
  (hPK : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
  (hMK : μM {m : M | (m : G) ∈ K} = 1) (hUK : μU {u : U | (u : G) ∈ K} = 1)
  {κ : Measure K} [SFinite κ] (hκ : κ.map Subtype.val = μ.restrict K)

/-- The coordinates `(k, (m, u)) ↦ m u k` of `G = M U K`. -/
def compactLeviUnipotentMul (x : K × (M × U)) : G :=
  (x.2.1 : G) * x.2.2 * x.1

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology U] in
theorem compactLeviUnipotentMul_apply (k : K) (m : M) (u : U) :
    compactLeviUnipotentMul (k, (m, u)) = (m : G) * u * k :=
  rfl

omit [SecondCountableTopology U] in
theorem measurable_compactLeviUnipotentMul :
    Measurable (compactLeviUnipotentMul (K := K) (M := M) (U := U)) := by
  unfold compactLeviUnipotentMul
  exact ((measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)).mul
    (measurable_subtype_coe.comp (measurable_snd.comp measurable_snd))).mul
    (measurable_subtype_coe.comp measurable_fst)

omit [SFinite κ] in
include hMU hK hfac hPK hMK hUK hκ in
/-- The integration formula of Waldspurger I.1 (2) in the coordinates `g = m u k`, as an image of
measures: the map `(k, (m, u)) ↦ m u k` sends `dk × dm × du` to `dg`, where `dk = κ` is a
measure on `K` whose image in `G` is the restriction of `dg` to `K`. -/
theorem map_compactLeviUnipotentMul :
    (κ.prod (μM.prod μU)).map compactLeviUnipotentMul = μ := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hΦ := measurable_compactLeviUnipotentMul (K := K) (M := M) (U := U)
  rw [lintegral_map hF hΦ, lintegral_eq_lintegral_levi_unipotent hMU hK hfac hPK hMK hUK F hF,
    lintegral_prod (fun x => F (compactLeviUnipotentMul x)) (hF.comp hΦ).aemeasurable]
  rw [← hκ]
  refine Eq.trans ?_ ((MeasurableEmbedding.subtype_coe hK).lintegral_map
    (fun k : G => ∫⁻ m, ∫⁻ u, F ((m : G) * u * k) ∂μU ∂μM)).symm
  refine lintegral_congr fun k => ?_
  have hm : Measurable fun x : M × U => F ((x.1 : G) * x.2 * k) :=
    hF.comp (((measurable_subtype_coe.comp measurable_fst).mul
      (measurable_subtype_coe.comp measurable_snd)).mul_const _)
  exact lintegral_prod _ hm.aemeasurable

omit [SFinite κ] in
include hMU hK hfac hPK hMK hUK hκ in
/-- Integrability transfers along `(k, (m, u)) ↦ m u k`. -/
theorem integrable_comp_compactLeviUnipotentMul_iff {E : Type*} [NormedAddCommGroup E]
    {F : G → E} (hF : AEStronglyMeasurable F μ) :
    Integrable (fun x => F (compactLeviUnipotentMul x)) (κ.prod (μM.prod μU)) ↔
      Integrable F μ := by
  have h := map_compactLeviUnipotentMul hMU hK hfac hPK hMK hUK hκ
  rw [← h] at hF ⊢
  exact (integrable_map_measure hF measurable_compactLeviUnipotentMul.aemeasurable).symm

include hMU hK hfac hPK hMK hUK hκ in
/-- The integration formula of Waldspurger I.1 (2) in the coordinates `g = m u k`, for Bochner
integrals: `∫_G F dg = ∫_K ∫_M ∫_U F(m u k) du dm dk` for integrable `F`. -/
theorem integral_eq_integral_compact_levi_unipotent {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {F : G → E} (hF : Integrable F μ) :
    ∫ g, F g ∂μ = ∫ k, ∫ m, ∫ u, F ((m : G) * u * k) ∂μU ∂μM ∂κ := by
  have h := map_compactLeviUnipotentMul hMU hK hfac hPK hMK hUK hκ
  have hc := (integrable_comp_compactLeviUnipotentMul_iff hMU hK hfac hPK hMK hUK hκ
    hF.aestronglyMeasurable).mpr hF
  have hF' : AEStronglyMeasurable F ((κ.prod (μM.prod μU)).map compactLeviUnipotentMul) := by
    rw [h]; exact hF.aestronglyMeasurable
  conv_lhs => rw [← h]
  rw [integral_map measurable_compactLeviUnipotentMul.aemeasurable hF', integral_prod _ hc]
  refine integral_congr_ae ?_
  filter_upwards [hc.prod_right_ae] with k hk
  exact integral_prod _ hk

end Iwasawa

section Pairing

variable {H : Type uG} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  (B : SmoothRep.{0, uG, uV} ℂ H)

/-- The pairing `v ⊗ ℓ ↦ ℓ(v)` of a coefficient tensor is its coefficient at `1`. -/
theorem lift_smoothDualPairing_flip_eq (t : CoefficientTensor B) :
    TensorProduct.lift (smoothDualPairing B.representation).flip t =
      coefficientTensorMap B t 1 := by
  induction t using TensorProduct.inductionOn with
  | tmul v ℓ =>
    rw [coefficientTensorMap_tmul, map_one]
    rfl
  | add x y hx hy => rw [map_add, hx, hy, map_add, LocallyConstant.add_apply]

end Pairing

section Inducing

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M)

/-- The inducing representation of `L(ω, P)` at `(p₁, p₂) ∈ P × P` is
`δ_P(p₁)^{1/2} δ_P(p₂)^{1/2} (ω(m(p₁)) ⊗ ω̌(m(p₂)))`, where `m : P → M` is the Levi projection. -/
theorem inducingRepresentation_productLeviObject_apply (p : P.prod P) (t : CoefficientTensor A) :
    inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient) p t =
      (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨p.1.1, p.2.1⟩ : ℂˣ) : ℂ) *
        ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨p.1.2, p.2.2⟩ : ℂˣ) : ℂ)) •
      coefficientTensorAction A (h.projection ⟨p.1.1, p.2.1⟩, h.projection ⟨p.1.2, p.2.2⟩) t := by
  refine (congrArg (fun ρ : Representation ℂ (P.prod P) (A ⊗[ℂ] A.contragredient) => ρ p t)
    (product_inducingRepresentation h h hU hU A A.contragredient)).trans ?_
  change TensorProduct.map
      (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨p.1.1, p.2.1⟩ : ℂˣ) : ℂ) •
        A.representation (h.projection ⟨p.1.1, p.2.1⟩))
      (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨p.1.2, p.2.2⟩ : ℂˣ) : ℂ) •
        smoothContragredient A.representation (h.projection ⟨p.1.2, p.2.2⟩)) t = _
  rw [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul, LinearMap.smul_apply]
  rfl

variable (hδU : IsUnimodularModulus U hU)

omit [SecondCountableTopology G] in
include hδU in
/-- With `U` unimodular, `δ_P(p)^{1/2} = δ_P(m(p))^{1/2}` for `p ∈ P`. -/
theorem closedHalfCharacter_eq_sqrt (q : P) :
    ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer q : ℂˣ) : ℂ) =
      ((NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
        (h.projection q)) : ℝ) : ℂ) := by
  rw [closedHalfCharacter_eq_comp_projection h hU hδU]
  rfl

include hδU in
/-- The coefficient pairing of `ψ ∈ L(ω, P)` at `(m u k, l)` is
`δ_P(m)^{1/2} E^M_M(ψ(k, l))(m)`. -/
theorem lift_eval_levi_mul (ψ : productInducedCoefficientObject h hU A) (m : M) (u : U)
    (k l : G) :
    TensorProduct.lift (smoothDualPairing A.representation).flip
        (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) ψ ((m : G) * u * k, l)) =
      ((NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m) : ℝ) :
          ℂ) *
        coefficientTensorMap A (Induction.eval (P.prod P) (inducingRepresentation (h.prod h)
          (hU.prod hU) (productLeviObject A A.contragredient)) ψ (k, l)) m := by
  let p₁ : P := ⟨m, h.levi_le m.2⟩ * ⟨u, h.unipotent_le u.2⟩
  let p : P.prod P := ⟨((p₁ : G), 1), p₁.2, P.one_mem⟩
  have hx : ((m : G) * u * k, l) = (p : G × G) * (k, l) := by
    simp only [p, p₁, Prod.mk_mul_mk, one_mul, Subgroup.coe_mul]
  have hcov : Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
      (productLeviObject A A.contragredient)) ψ ((p : G × G) * (k, l)) =
      inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient) p
        (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) ψ (k, l)) :=
    ψ.1.2 p (k, l)
  have h₁ : h.projection ⟨(p : G × G).1, p.2.1⟩ = m := h.projection_mul m u
  have h₂ : h.projection ⟨(p : G × G).2, p.2.2⟩ = 1 := map_one h.projection
  have hc₂ : ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer
      ⟨(p : G × G).2, p.2.2⟩ : ℂˣ) : ℂ) = 1 := by
    rw [closedHalfCharacter_eq_sqrt h hU hδU, h₂, map_one, Units.val_one, NNReal.sqrt_one,
      NNReal.coe_one, Complex.ofReal_one]
  have key : ∀ t₁ t₂ : CoefficientTensor A,
      t₁ = (((HaarModulus.closedHalfCharacter U hU P h.le_normalizer
          ⟨(p : G × G).1, p.2.1⟩ : ℂˣ) : ℂ) *
        ((HaarModulus.closedHalfCharacter U hU P h.le_normalizer ⟨(p : G × G).2, p.2.2⟩ : ℂˣ) :
          ℂ)) • coefficientTensorAction A
            (h.projection ⟨(p : G × G).1, p.2.1⟩, h.projection ⟨(p : G × G).2, p.2.2⟩) t₂ →
      TensorProduct.lift (smoothDualPairing A.representation).flip t₁ =
        ((NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m) :
          ℝ) : ℂ) * coefficientTensorMap A t₂ m := by
    intro t₁ t₂ ht
    rw [ht, map_smul, smul_eq_mul, lift_smoothDualPairing_flip_eq, coefficientTensorMap_action,
      hc₂, closedHalfCharacter_eq_sqrt h hU hδU, h₁, h₂, mul_one, inv_one, one_mul, one_mul]
  refine key _ _ ?_
  rw [hx]
  exact hcov.trans (inducingRepresentation_productLeviObject_apply h hU A p _)

end Inducing

section ConstantTermSpace

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)] {M U : Subgroup G}
  {ν : Measure U} {δ : M →* ℝ≥0ˣ} {Ξ σ : G → ℝ} {ΞM σM : M → ℝ}
  (hD : ConstantTermData ν δ) (hE : ConstantTermEstimate ν δ Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

/-- Waldspurger III.6: `f^{(P),Ind}(g₁, g₂) = (ρ(g₁)λ(g₂)f)^{(P)} ∈ C(M)` for `f ∈ C(G)`. -/
def Space.constantTermInd (f : Space Ξ σ) (g : G × G) : Space ΞM σM :=
  Space.constantTerm hD hE ht.pos ht.nonneg htM.pos htM.nonneg (Space.translate ht g.1 g.2 f)

@[simp] theorem Space.coe_constantTermInd (f : Space Ξ σ) (g : G × G) :
    ((Space.constantTermInd hD hE ht htM f g : Space ΞM σM) : M → ℂ) =
      HarishChandraSchwartz.constantTermInd ν δ f g :=
  rfl

omit [MeasurableSpace G] [BorelSpace G] in
/-- Every `f ∈ C(G)` is bi-invariant under some compact open subgroup. -/
theorem Space.exists_isBiInvariant (f : Space Ξ σ) :
    ∃ H : CompactOpenSubgroup G, IsBiInvariant H.toSubgroup f := by
  obtain ⟨H, hH⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem f)
  exact ⟨H, hH.1⟩

variable {hMU : M ≤ Subgroup.normalizer (U : Set G)}

/-- Waldspurger III.6 on `C(M)`: `f^{(P),Ind}(m₁ u₁ g₁, m₂ u₂ g₂) =
δ(m₁)^{1/2} δ(m₂)^{1/2} ρ(m₁)λ(m₂) f^{(P),Ind}(g₁, g₂)`. -/
theorem Space.constantTermInd_mul [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
    (hν : IsConjModulus hMU ν δ) (f : Space Ξ σ) (m₁ m₂ : M) (u₁ u₂ : U) (g₁ g₂ : G) :
    Space.constantTermInd hD hE ht htM f ((m₁ : G) * u₁ * g₁, (m₂ : G) * u₂ * g₂) =
      (((NNReal.sqrt (δ m₁) : ℝ) : ℂ) * ((NNReal.sqrt (δ m₂) : ℝ) : ℂ)) •
        Space.translate htM m₁ m₂ (Space.constantTermInd hD hE ht htM f (g₁, g₂)) :=
  Space.ext fun m => hν.constantTermInd_mul (f : G → ℂ) m₁ m₂ u₁ u₂ g₁ g₂ m

end ConstantTermSpace

section Definition

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδU : IsUnimodularModulus U hU) (A : SmoothRep.{0, uG, uV} ℂ M)
  [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM) (hA : IsAdmissible A.representation)
  (hTM : HasTemperedCoefficients ΞM σM A.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m) (d : ℝ)
  {ν : Measure U} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hD : ConstantTermData ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hν : IsConjModulus h.levi_le_normalizer ν
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

include hδU hν in
/-- `x ↦ [f^{(P),Ind}(x)]^(ω, M)` satisfies the covariance law of `L(ω, P)` under `P × P`. -/
theorem constantTermInducedFourierTransform_covariant (f : Space Ξ σ) (p : P.prod P)
    (x : G × G) :
    coefficientFourierTransform A hwM hA hTM hΞM hσM d
        (Space.constantTermInd hD hE ht htM f ((p : G × G) * x)) =
      inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient) p
        (coefficientFourierTransform A hwM hA hTM hΞM hσM d
          (Space.constantTermInd hD hE ht htM f x)) := by
  let u : P → U := fun q => ⟨((h.projection q : M) : G)⁻¹ * q, h.projection_inv_mul_mem q⟩
  have hq : ∀ q : P, (q : G) = (h.projection q : G) * (u q : G) := fun q => by
    simp only [u, mul_inv_cancel_left]
  have hx : (p : G × G) * x =
      ((h.projection ⟨(p : G × G).1, p.2.1⟩ : G) * (u ⟨(p : G × G).1, p.2.1⟩ : G) * x.1,
        (h.projection ⟨(p : G × G).2, p.2.2⟩ : G) * (u ⟨(p : G × G).2, p.2.2⟩ : G) * x.2) := by
    rw [← hq, ← hq]
    rfl
  rw [hx, Space.constantTermInd_mul hD hE ht htM hν, map_smul,
    coefficientFourierTransform_translate A hwM hA hTM hΞM hσM htM d,
    inducingRepresentation_productLeviObject_apply h hU A, closedHalfCharacter_eq_sqrt h hU hδU,
    closedHalfCharacter_eq_sqrt h hU hδU]

omit [SecondCountableTopology G] [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] in
/-- `x ↦ [f^{(P),Ind}(x)]^(ω, M)` is right invariant under `H × H` when `f` is bi-invariant
under `H`. -/
theorem constantTermInducedFourierTransform_mul_right (f : Space Ξ σ)
    {H : CompactOpenSubgroup G} (hH : IsBiInvariant H.toSubgroup f) (k : H.1.prod H.1)
    (x : G × G) :
    coefficientFourierTransform A hwM hA hTM hΞM hσM d
        (Space.constantTermInd hD hE ht htM f (x * (k : G × G))) =
      coefficientFourierTransform A hwM hA hTM hΞM hσM d
        (Space.constantTermInd hD hE ht htM f x) := by
  have hk : (k : G × G) ∈ ((H.1.prod H.1 : OpenSubgroup (G × G)) : Set (G × G)) := k.2
  rw [OpenSubgroup.coe_prod] at hk
  congr 1
  exact Space.ext fun m => congrFun (hH.constantTermInd_mul ν _ hk.1 hk.2 x) m

/-- **Waldspurger's `f̂^{(P),Ind}(ω)`** (VII.1, before Lemma VII.1.2): the element of
`L(ω, P) = I_{P×P}^{G×G}(E ⊗ Ě)` given by
`f̂^{(P),Ind}(ω)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)`, where `f^{(P),Ind}(g₁, g₂) ∈ C(M)` is the
constant term of `ρ(g₁)λ(g₂)f` (III.6) and `φ ↦ φ^(ω, M) = d · ω(φ̌)` is the Fourier transform of
`C(M)` at `ω`, for `d = d(ω)`. -/
def constantTermInducedFourierTransform (f : Space Ξ σ) : productInducedCoefficientObject h hU A :=
  Induction.smoothFunctionOf (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient))
    (fun x => coefficientFourierTransform A hwM hA hTM hΞM hσM d
      (Space.constantTermInd hD hE ht htM f x))
    (constantTermInducedFourierTransform_covariant h hU hδU A hwM hA hTM hΞM hσM d hD hν hE ht
      htM f)
    ((Classical.choose (Space.exists_isBiInvariant f)).1.prod
      (Classical.choose (Space.exists_isBiInvariant f)).1)
    (constantTermInducedFourierTransform_mul_right h hU A hwM hA hTM hΞM hσM d hD hE ht htM f
      (Classical.choose_spec (Space.exists_isBiInvariant f)))

/-- The value of `f̂^{(P),Ind}(ω)` at `(g₁, g₂)` is `[f^{(P),Ind}(g₁, g₂)]^(ω, M)`. -/
theorem eval_constantTermInducedFourierTransform (f : Space Ξ σ) (x : G × G) :
    Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject A A.contragredient))
        (constantTermInducedFourierTransform h hU hδU A hwM hA hTM hΞM hσM d hD hν hE ht htM f) x =
      coefficientFourierTransform A hwM hA hTM hΞM hσM d (Space.constantTermInd hD hE ht htM f x) :=
  rfl

end Definition

section Unipotent

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [MeasurableSpace G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hδU : IsUnimodularModulus U hU) (A : SmoothRep.{0, uG, uV} ℂ M) (ν : Measure U)

include hδU in
/-- The integral over `U` in the proof of Lemma VII.1.2: for `ψ ∈ L(ω, P)`,
`∫_U conj⟨ψ(m u k, l)⟩ f(l⁻¹ m u k) du = conj(E^M_M(ψ(k, l))(m)) f^{(P),Ind}(k, l)(m)`, where
`⟨ , ⟩` is the pairing `E ⊗ Ě → ℂ`. -/
theorem integral_conj_lift_eval_mul (ψ : productInducedCoefficientObject h hU A) (f : G → ℂ)
    (k l : G) (m : M) :
    ∫ u : U, conj (TensorProduct.lift (smoothDualPairing A.representation).flip
        (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) ψ ((m : G) * u * k, l))) *
        f (l⁻¹ * ((m : G) * u * k)) ∂ν =
      conj (coefficientTensorMap A (Induction.eval (P.prod P) (inducingRepresentation (h.prod h)
          (hU.prod hU) (productLeviObject A A.contragredient)) ψ (k, l)) m) *
        constantTermInd ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) f
          (k, l) m := by
  have e : ∀ u : U, conj (TensorProduct.lift (smoothDualPairing A.representation).flip
        (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
          (productLeviObject A A.contragredient)) ψ ((m : G) * u * k, l))) *
        f (l⁻¹ * ((m : G) * u * k)) =
      conj (coefficientTensorMap A (Induction.eval (P.prod P) (inducingRepresentation (h.prod h)
          (hU.prod hU) (productLeviObject A A.contragredient)) ψ (k, l)) m) *
        (((NNReal.sqrt (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer m) :
          ℝ) : ℂ) * f (l⁻¹ * ((m : G) * u) * k)) := by
    intro u
    rw [lift_eval_levi_mul h hU A hδU ψ m u k l, map_mul, Complex.conj_ofReal,
      ← mul_assoc l⁻¹ ((m : G) * u) k]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall e), integral_const_mul, integral_const_mul]
  rfl

end Unipotent

section Main

variable {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] [SecondCountableTopology G] [T2Space G]
  [MeasurableSpace G] [BorelSpace G] [Nonempty (CompactOpenSubgroup G)]
  {P M U : Subgroup G} [LocallyCompactSpace P]
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (hP : IsClosed (P : Set G)) (hm : Continuous h.projection)
  (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
  (hPK : ∀ g : G, ∃ q ∈ P, ∃ k ∈ K, g = q * k)
  (hG : ∀ g : G, Measure.modularCharacter g = 1)
  (hδ : ∀ q : P, Measure.modularCharacter q =
    (HaarModulus.closedRestrictCharacter U hU P h.le_normalizer q : ℝ≥0))
  (A : SmoothRep.{0, uG, uV} ℂ M) (hcof : CompactOpenCofinal M)
  (C : Subgroup M) [C.Normal] (hC : C ≤ Subgroup.center M)
  [MeasurableSpace (M ⧸ C)] [BorelSpace (M ⧸ C)]
  (μM : Measure (M ⧸ C)) [μM.IsHaarMeasure] [μM.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation μM)
  (hi : A.representation.IsIrreducible)
  {μ : Measure G} [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {Ξ σ : G → ℝ}
  (hw : L2Weights μ Ξ σ)
  (hT : HasTemperedCoefficients Ξ σ ((normalizedInductionFunctor h hU).obj A).representation)
  (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
  (hδU : IsUnimodularModulus U hU) [Nonempty (CompactOpenSubgroup M)]
  {μL : Measure M} [μL.IsMulLeftInvariant] [μL.IsMulRightInvariant] {ΞM σM : M → ℝ}
  (hwM : L2Weights μL ΞM σM) (hTM : HasTemperedCoefficients ΞM σM A.representation)
  (hΞM : ∀ m, ΞM m⁻¹ = ΞM m) (hσM : ∀ m, σM m⁻¹ = σM m)
  {ν : Measure U} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant]
  (hD : ConstantTermData ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hν : IsConjModulus h.levi_le_normalizer ν
    (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer))
  (hE : ConstantTermEstimate ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer)
    Ξ σ ΞM σM)
  (ht : TranslationWeights Ξ σ) (htM : TranslationWeights ΞM σM)

/-- **Lemma VII.1.2** (Waldspurger, printed p. 315): `f̂(ω, P) = f̂^{(P),Ind}(ω)` for
`f ∈ C(G)`. The double integral `∫_G ∫_K conj⟨ψ(k g, k)⟩ f(g) dk dg` is assumed absolutely
convergent (hypothesis `hint`; in the source this follows from the proof of Lemma VI.2.2 and
Lemma II.1.5). The measures satisfy `mes(K) = mes(M ∩ K) = mes(U ∩ K) = 1` (I.1) and
`P ∩ K = (M ∩ K)(U ∩ K)` (hypothesis `hPKiw`). -/
theorem inducedFourierTransform_eq_constantTermInducedFourierTransform
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL] [SFinite ν]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : ν {u : U | (u : G) ∈ K} = 1)
    (f : Space Ξ σ)
    (hint : ∀ ψ : productInducedCoefficientObject h hU A,
      Integrable (fun x : G × K => conj (CompactInduction.integrand h hU A K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) :
    inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f =
      constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
        (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f := by
  obtain ⟨b⟩ := isUnitarizable_of_isSquareIntegrableModCentralSubgroup C hC μM hcof hsq
  have hd := representationFormalDegree_pos C hC μM hcof hsq hi
  have : SecondCountableTopology U := TopologicalSpace.Subtype.secondCountableTopology _
  have hμ : RankinSelberg.normalizedCompactOpenHaar K hK = μ := by
    have h1 := Measure.haarMeasure_unique μ (RankinSelberg.compactOpenPositive K hK)
    have h2 : μ (RankinSelberg.compactOpenPositive K hK) = 1 := hμK
    rw [h2, one_smul] at h1
    exact h1.symm
  have hκ : (CompactInduction.measure K hK).map Subtype.val = μ.restrict (K : Set G) := by
    have e := map_comap_subtype_coe (s := (K : Set G)) K.isOpen.measurableSet
      (RankinSelberg.normalizedCompactOpenHaar K hK)
    exact e.trans (by rw [hμ])
  have hfac : ∀ g : G, ∃ m : M, ∃ u : U, ∃ k ∈ (K : Subgroup G), g = (m : G) * u * k := by
    intro g
    obtain ⟨q, hq, k, hk, rfl⟩ := hPK g
    exact ⟨h.projection ⟨q, hq⟩, ⟨_, h.projection_inv_mul_mem ⟨q, hq⟩⟩, k, hk, by simp⟩
  refine inducedFourierTransform_eq_of_forall_integral h hU hP hm K hK hPK hG hδ A hcof C hC μM
    hsq hi hw hT hΞ hσ f _ fun ψ => ?_
  rw [CompactInduction.formalDegreeProductForm_eq h hU hP K hK hPK hG hδ A hcof C hC μM hsq hi b,
    InvariantPositiveForm.rescale_inner,
    CompactInduction.productForm_inner_integral_integral h hU hP K hK hPK hG hδ A hcof hsq.1 b]
  have hM : ∀ k l : G,
      ∫ m, conj (coefficientTensorMap A (Induction.eval (P.prod P) (inducingRepresentation
          (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient)) ψ (k, l)) m) *
        constantTermInd ν (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) f
          (k, l) m ∂μL =
      (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ) *
        (coefficientTensorInvariantForm A hcof hsq.1 b).inner
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ (k, l))
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient))
            (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
              (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f) (k, l)) :=
    fun k l => integral_conj_coefficientTensorMap_mul_eq_inner A hwM hsq.1 hTM hΞM hσM _ hd b _
      (Space.constantTermInd hD hE ht htM f (k, l))
  have hl : ∀ᵐ l ∂CompactInduction.measure K hK,
      ∫ g, conj (CompactInduction.integrand h hU A K g ψ l) * f g ∂μ =
        ∫ k, (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ) *
          (coefficientTensorInvariantForm A hcof hsq.1 b).inner
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient)) ψ ((k : G), (l : G)))
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient))
              (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
                (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f)
              ((k : G), (l : G))) ∂CompactInduction.measure K hK := by
    filter_upwards [(hint ψ).prod_left_ae] with l hl
    have hFl : Integrable (fun g => conj (TensorProduct.lift
        (smoothDualPairing A.representation).flip (Induction.eval (P.prod P)
          (inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient))
          ψ (g, (l : G)))) * f ((l : G)⁻¹ * g)) μ := by
      refine (hl.comp_mul_left (l : G)⁻¹).congr (Filter.Eventually.of_forall fun t => ?_)
      change conj (TensorProduct.lift (smoothDualPairing A.representation).flip
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ ((l : G) * ((l : G)⁻¹ * t), (l : G)))) *
          f ((l : G)⁻¹ * t) = _
      rw [mul_inv_cancel_left]
    have h1 : ∫ g, conj (CompactInduction.integrand h hU A K g ψ l) * f g ∂μ =
        ∫ g, conj (TensorProduct.lift (smoothDualPairing A.representation).flip
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ (g, (l : G)))) * f ((l : G)⁻¹ * g) ∂μ := by
      refine Eq.trans ?_ (integral_mul_left_eq_self (fun g => conj (TensorProduct.lift
        (smoothDualPairing A.representation).flip (Induction.eval (P.prod P)
          (inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient))
          ψ (g, (l : G)))) * f ((l : G)⁻¹ * g)) (l : G))
      refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
      change conj (TensorProduct.lift (smoothDualPairing A.representation).flip
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ ((l : G) * g, (l : G)))) * f g =
        conj (TensorProduct.lift (smoothDualPairing A.representation).flip
          (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
            (productLeviObject A A.contragredient)) ψ ((l : G) * g, (l : G)))) *
          f ((l : G)⁻¹ * ((l : G) * g))
      rw [inv_mul_cancel_left]
    have : @SFinite (↥(K : Subgroup G)) _ (CompactInduction.measure K hK) :=
      inferInstanceAs (SFinite (CompactInduction.measure K hK))
    refine h1.trans ((integral_eq_integral_compact_levi_unipotent h.levi_le_normalizer
      (K := (K : Subgroup G)) K.isOpen.measurableSet hfac hPKiw hMK hUK hκ hFl).trans ?_)
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    refine Eq.trans ?_ (hM (k : G) (l : G))
    refine integral_congr_ae (Filter.Eventually.of_forall fun m => ?_)
    exact integral_conj_lift_eval_mul h hU hδU A ν ψ f (k : G) (l : G) m
  have hP2 := (CompactInduction.integrable_productForm_pairing h hU K hK A hcof hsq.1 b ψ
    (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
      (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f)).const_mul
    (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ)
  calc ∫ g, conj (CompactInduction.coefficientMap h hU A K hK hP hm hPK hG hδ hsq.1 ψ g) * f g ∂μ
      = ∫ g, ∫ l, conj (CompactInduction.integrand h hU A K g ψ l) * f g
          ∂CompactInduction.measure K hK ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        beta_reduce
        rw [CompactInduction.coefficientMap_integral h hU A K hK hP hm hPK hG hδ hsq.1,
          ← integral_conj, ← integral_mul_const]
    _ = ∫ l, ∫ g, conj (CompactInduction.integrand h hU A K g ψ l) * f g
          ∂μ ∂CompactInduction.measure K hK :=
        integral_integral_swap (hint ψ)
    _ = ∫ l, ∫ k, (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ) *
          (coefficientTensorInvariantForm A hcof hsq.1 b).inner
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient)) ψ ((k : G), (l : G)))
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient))
              (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
                (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f)
              ((k : G), (l : G))) ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK :=
        integral_congr_ae hl
    _ = ∫ k, ∫ l, (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ) *
          (coefficientTensorInvariantForm A hcof hsq.1 b).inner
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient)) ψ ((k : G), (l : G)))
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient))
              (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
                (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f)
              ((k : G), (l : G))) ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK :=
        (integral_integral_swap hP2).symm
    _ = (((representationFormalDegree C hC μM hcof hsq hi)⁻¹ : ℝ) : ℂ) * ∫ k, ∫ l,
          (coefficientTensorInvariantForm A hcof hsq.1 b).inner
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient)) ψ ((k : G), (l : G)))
            (Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
              (productLeviObject A A.contragredient))
              (constantTermInducedFourierTransform h hU hδU A hwM hsq.1 hTM hΞM hσM
                (representationFormalDegree C hC μM hcof hsq hi) hD hν hE ht htM f)
              ((k : G), (l : G))) ∂CompactInduction.measure K hK ∂CompactInduction.measure K hK := by
        rw [← integral_const_mul]
        exact integral_congr_ae (Filter.Eventually.of_forall fun k => integral_const_mul _ _)

include hδU hν in
/-- **Lemma VII.1.2** pointwise: `f̂(ω, P)(g₁, g₂) = [f^{(P),Ind}(g₁, g₂)]^(ω, M)`. -/
theorem eval_inducedFourierTransform
    [MeasurableInv G] [μ.IsInvInvariant] [SigmaFinite μ] (hμK : μ (K : Set G) = 1)
    [MeasurableInv M] [μL.IsInvInvariant] [SFinite μL] [SFinite ν]
    (hPKiw : ∀ (m : M) (u : U), (m : G) * u ∈ K ↔ (m : G) ∈ K ∧ (u : G) ∈ K)
    (hMK : μL {m : M | (m : G) ∈ K} = 1) (hUK : ν {u : U | (u : G) ∈ K} = 1)
    (f : Space Ξ σ)
    (hint : ∀ ψ : productInducedCoefficientObject h hU A,
      Integrable (fun x : G × K => conj (CompactInduction.integrand h hU A K x.1 ψ x.2) * f x.1)
        (μ.prod (CompactInduction.measure K hK))) (x : G × G) :
    Induction.eval (P.prod P) (inducingRepresentation (h.prod h) (hU.prod hU)
        (productLeviObject A A.contragredient))
        (inducedFourierTransform h hU hP hm K hK hPK hG hδ A hcof C hC μM hsq hi hw hT hΞ hσ f) x =
      coefficientFourierTransform A hwM hsq.1 hTM hΞM hσM
        (representationFormalDegree C hC μM hcof hsq hi)
        (Space.constantTermInd hD hE ht htM f x) := by
  rw [inducedFourierTransform_eq_constantTermInducedFourierTransform h hU hP hm K hK hPK hG hδ A
    hcof C hC μM hsq hi hw hT hΞ hσ hδU hwM hTM hΞM hσM hD hν hE ht htM hμK hPKiw hMK hUK f hint]
  rfl

end Main

end Langlands.HarishChandraSchwartz

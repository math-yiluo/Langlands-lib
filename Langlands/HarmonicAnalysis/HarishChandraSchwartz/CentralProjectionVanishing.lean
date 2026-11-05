import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteCoefficientSpace
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.KernelQuotient
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.SchwartzAction
import Langlands.Analysis.Local.QuotientMass

/-! # Vanishing of `p_χ φ` (Waldspurger, end of the proof of Theorem VIII.1.1)

Waldspurger, VIII.5 (printed p. 332): for `φ ∈ °C(G)` with `ω(ˇφ) = 0` for every
`ω ∈ E₂(G)`, if `p_χ φ ≠ 0` then Theorem VIII.4.2 gives `(ω, E) ∈ E₂(G)_χ` with a
`G`-invariant positive hermitian product and `v₁, v₂ ∈ E` such that
`∫_{A_G\G} conj((v₁, ω(g) v₂)) p_χ φ(g) dg ≠ 0`; but this integral is
`∫_G conj((v₁, ω(g) v₂)) φ(g) dg = ∫_G (v₂, ω(g) v₁) φ(g⁻¹) dg = (v₂, ω(ˇφ) v₁) = 0`.

This module proves that argument for abstract data:

* `∫_G conj(b(e, ρ(g) v)) φ(g) dμ = b(v, π(ˇφ) e)` for an admissible representation with
  tempered coefficients and an invariant positive form `b`;
* if `π_S(ˇφ) = 0` for every subrepresentation `S` in a class `p`, then every function in the
  span `Σ_S A(S)` of `DiscreteCoefficientSpace` is orthogonal to `φ` on `G`;
* through the Weil formula of `KernelQuotient`, a continuous `p_χ φ` orthogonal to `φ` on `G`
  has `∫_{A\G} |p_χ φ|² = 0`, hence vanishes (a compatible quotient measure charges nonempty
  open sets, `IsCompatible.isOpenPosMeasure`);
* hence `p_χ φ = 0` when `p_χ φ ∈ Σ_S A(S)` (Theorem VIII.4.2) and `π_S(ˇφ) = 0` for all `S`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Langlands.QuotientIntegration
open scoped ComplexConjugate

namespace Langlands.HarishChandraSchwartz

open Langlands.Plancherel

universe u v

section Annihilator

variable {G : Type u} [MeasurableSpace G]

/-- The functions `c` on `G` with `g ↦ conj(c(g)) φ(g)` integrable and
`(c, φ)_G = ∫_G conj(c(g)) φ(g) dμ(g) = 0`. -/
def pairingAnnihilator (μ : Measure G) (φ : G → ℂ) : Submodule ℂ (G → ℂ) where
  carrier := {c | Integrable (fun g => conj (c g) * φ g) μ ∧ pairing μ c φ = 0}
  add_mem' {c₁ c₂} h₁ h₂ := by
    refine ⟨(h₁.1.add h₂.1).congr (Filter.Eventually.of_forall fun g => ?_), ?_⟩
    · simp only [Pi.add_apply, map_add, add_mul]
    · rw [pairing_apply]
      simp only [Pi.add_apply, map_add, add_mul]
      rw [integral_add h₁.1 h₂.1, ← pairing_apply, ← pairing_apply, h₁.2, h₂.2, add_zero]
  zero_mem' := by
    refine ⟨?_, ?_⟩
    · simp only [Pi.zero_apply, map_zero, zero_mul]
      exact integrable_zero _ _ _
    · simp [pairing_apply]
  smul_mem' a c h := by
    refine ⟨(h.1.const_mul (conj a)).congr (Filter.Eventually.of_forall fun g => ?_), ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul, map_mul]
      ring
    · rw [pairing_apply]
      simp only [Pi.smul_apply, smul_eq_mul, map_mul, mul_assoc]
      rw [integral_const_mul, ← pairing_apply, h.2, mul_zero]

theorem mem_pairingAnnihilator {μ : Measure G} {φ c : G → ℂ} :
    c ∈ pairingAnnihilator μ φ ↔
      Integrable (fun g => conj (c g) * φ g) μ ∧ pairing μ c φ = 0 :=
  Iff.rfl

end Annihilator

section FormCoefficient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [OpensMeasurableSpace G] [Nonempty (CompactOpenSubgroup G)]
  {μ : Measure G} {Ξ σ : G → ℝ}
  {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [OpensMeasurableSpace G]
  [Nonempty (CompactOpenSubgroup G)] in
/-- For an invariant positive form, `conj(b(e, ρ(g) v)) = b(v, ρ(g⁻¹) e)`. -/
theorem conj_inner_apply (b : InvariantPositiveForm ρ) (e v : V) (g : G) :
    conj (b.inner e (ρ g v)) = b.inner v (ρ g⁻¹ e) := by
  rw [b.conj_inner_symm, ← b.invariant g⁻¹ (ρ g v) e, Representation.inv_self_apply]

/-- For `φ ∈ C(G)`, `g ↦ conj(b(e, ρ(g) v)) φ(g)` is integrable. -/
theorem integrable_conj_inner_mul [MeasurableInv G] [μ.IsInvInvariant] (hw : L2Weights μ Ξ σ)
    (hρ : IsSmooth ρ) (hT : HasTemperedCoefficients Ξ σ ρ) (hΞ : ∀ g, Ξ g⁻¹ = Ξ g)
    (hσ : ∀ g, σ g⁻¹ = σ g) (b : InvariantPositiveForm ρ) (φ : Space Ξ σ) (e v : V) :
    Integrable (fun g => conj (b.inner e (ρ g v)) * φ g) μ := by
  have h := (integrable_coefficient hw hρ hT (Space.check hΞ hσ φ) e
    (b.toSmoothDual hρ v)).comp_inv
  refine h.congr (Filter.Eventually.of_forall fun g => ?_)
  change φ g⁻¹⁻¹ * b.inner v (ρ g⁻¹ e) = conj (b.inner e (ρ g v)) * φ g
  rw [inv_inv, conj_inner_apply, mul_comm]

/-- **The pairing of VIII.5**: for an admissible representation with tempered coefficients and
an invariant positive form `b`,
`∫_G conj(b(e, ρ(g) v)) φ(g) dμ(g) = b(v, π(ˇφ) e)`, where `π(ˇφ) e = ∫_G φ(g⁻¹) ρ(g) e dμ(g)`. -/
theorem integral_conj_inner_mul [MeasurableMul G] [MeasurableInv G] [μ.IsMulLeftInvariant]
    [μ.IsInvInvariant]
    (hw : L2Weights μ Ξ σ) (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ)
    (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g) (b : InvariantPositiveForm ρ)
    (φ : Space Ξ σ) (e v : V) :
    ∫ g, conj (b.inner e (ρ g v)) * φ g ∂μ =
      b.inner v (schwartzAction hw hρ hT (Space.check hΞ hσ φ) e) := by
  have h := schwartzAction_eval hw hρ hT (Space.check hΞ hσ φ) e (b.toSmoothDual hρ.1 v)
  change b.inner v _ = _ at h
  rw [h, ← integral_inv_eq_self (fun g => conj (b.inner e (ρ g v)) * φ g) μ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
  change conj (b.inner e (ρ g⁻¹ v)) * φ g⁻¹ = φ g⁻¹ * b.inner v (ρ g e)
  rw [conj_inner_apply, inv_inv, mul_comm]

/-- If `π(ˇφ) = 0`, every coefficient `g ↦ ℓ(ρ(g) v)` of an admissible unitary representation
with tempered coefficients is orthogonal to `φ` on `G`. -/
theorem coefficient_mem_pairingAnnihilator [MeasurableMul G] [MeasurableInv G]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (hw : L2Weights μ Ξ σ)
    (hρ : IsAdmissible ρ) (hT : HasTemperedCoefficients Ξ σ ρ) (hΞ : ∀ g, Ξ g⁻¹ = Ξ g)
    (hσ : ∀ g, σ g⁻¹ = σ g) (b : InvariantPositiveForm ρ) {φ : Space Ξ σ}
    (hφ : schwartzAction hw hρ hT (Space.check hΞ hσ φ) = 0) (v : V) (ℓ : SmoothDual ρ) :
    (fun g => ℓ.val (ρ g v)) ∈ pairingAnnihilator μ φ := by
  obtain ⟨e, rfl⟩ := (b.smoothDualEquiv CompactOpenSubgroup.cofinal hρ).surjective ℓ
  refine ⟨integrable_conj_inner_mul hw hρ.1 hT hΞ hσ b φ e v, ?_⟩
  rw [pairing_apply]
  change ∫ g, conj (b.inner e (ρ g v)) * φ g ∂μ = 0
  rw [integral_conj_inner_mul hw hρ hT hΞ hσ b φ e v, hφ, LinearMap.zero_apply]
  exact (b.rightFunctional v).map_zero

/-- **Orthogonality of `Σ_S A(S)` to `φ`**: if every subrepresentation `S` of `ρ` satisfying
`p` is admissible, has tempered coefficients and satisfies `π_S(ˇφ) = 0`, then every function
in the span `Σ_S A(S)` of their coefficient spaces is orthogonal to `φ` on `G`. -/
theorem subrepresentationCoefficientSpace_le [MeasurableMul G] [MeasurableInv G]
    [μ.IsMulLeftInvariant] [μ.IsInvInvariant] (hw : L2Weights μ Ξ σ)
    (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
    (b : InvariantPositiveForm ρ) (hs : IsSmooth ρ) {p : Subrepresentation ρ → Prop}
    {φ : Space Ξ σ}
    (hS : ∀ S, p S → ∃ (hSa : IsAdmissible S.toRepresentation)
      (hT : HasTemperedCoefficients Ξ σ S.toRepresentation),
      schwartzAction hw hSa hT (Space.check hΞ hσ φ) = 0) :
    (subrepresentationCoefficientSpace hs p).map (LocallyConstant.coeFnₗ ℂ) ≤
      pairingAnnihilator μ φ := by
  rw [Submodule.map_le_iff_le_comap]
  refine iSup₂_le fun S hpS => ?_
  obtain ⟨hSa, hT, hφ⟩ := hS S hpS
  let bS := b.comap (ScalarSubReduction.inclusion ρ S) (ScalarSubReduction.inclusion_injective ρ S)
  rintro _ ⟨t, rfl⟩
  induction t using TensorProduct.inductionOn with
  | tmul w ℓ =>
    exact coefficient_mem_pairingAnnihilator (ρ := S.toRepresentation) hw hSa hT hΞ hσ bS hφ w ℓ
  | add t₁ t₂ h₁ h₂ =>
    rw [map_add]
    exact add_mem h₁ h₂

end FormCoefficient

section Quotient

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G]
  {A : Subgroup G} (hA : IsClosed (A : Set G))
  [MeasurableSpace A] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)]
  {μA : Measure A} [SFinite μA] [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA]
  {μG : Measure G} [IsFiniteMeasureOnCompacts μG] {ν : Measure (LeftQuotient A)}
  {χ : A →* ℂˣ}

include hA in
/-- Integrability in the **Weil formula**: for integrable `F` on `G`,
`q ↦ ∫_A F(a q̇) dμ_A(a)` is integrable on `A \ G`, where `q̇ = Quotient.out q`. -/
theorem integrable_integral_out [MeasurableMul A] (hν : IsCompatible A μG μA ν) {F : G → ℂ}
    (hF : Integrable F μG) :
    Integrable (fun q => ∫ a, F ((a : G) * q.out) ∂μA) ν := by
  have hcomp := orbitKernel_comp A hA μA μG ν hν
  rw [← hcomp] at hF
  have hF' := hF
  rw [Measure.comp_eq_comp_const_apply] at hF'
  have h1 := hF'.integral_comp
  rw [Kernel.const_apply] at h1
  have hae := Measure.ae_integrable_of_integrable_comp hF
  refine h1.congr (hae.mono fun q hq => ?_)
  have hq' : orbitKernel A hA μA q = Measure.map (fun a : A => (a : G) * q.out) μA := by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  dsimp only
  rw [hq'] at hq ⊢
  exact integral_map ((continuous_subtype_val.mul continuous_const).measurable.aemeasurable)
    hq.aestronglyMeasurable

omit [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [BorelSpace A]
  [MeasurableSpace (LeftQuotient A)] [BorelSpace (LeftQuotient A)] [SFinite μA]
  [μA.IsMulRightInvariant] [IsFiniteMeasureOnCompacts μA] in
/-- For `χ`-covariant `K` and unitary `χ`,
`∫_A conj(K(a g)) φ(a g) dμ_A(a) = (p_χ φ)(g) conj(K(g))`. -/
theorem integral_conj_mul_mul_left (hχ : IsUnitaryCharacter χ) {K φ : G → ℂ}
    (hK : ∀ (a : A) (g : G), K ((a : G) * g) = χ a * K g) (g : G) :
    ∫ a, conj (K ((a : G) * g)) * φ ((a : G) * g) ∂μA =
      centralProjection μA χ φ g * conj (K g) := by
  unfold centralProjection
  rw [← integral_mul_const]
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [hK, map_mul]
  rw [Units.val_inv_eq_inv_val, Complex.inv_eq_conj (hχ.norm_eq_one a)]
  ring

include hA in
/-- For `χ`-covariant `K` and unitary `χ`, the integrand
`q ↦ (p_χ φ)(q̇) conj(K(q̇))` of `KernelQuotient.integral_centralProjection_mul_conj` is
integrable on `A \ G`. -/
theorem integrable_centralProjection_mul_conj [MeasurableMul A] (hν : IsCompatible A μG μA ν)
    (hχ : IsUnitaryCharacter χ) {K φ : G → ℂ}
    (hK : ∀ (a : A) (g : G), K ((a : G) * g) = χ a * K g)
    (hint : Integrable (fun g => conj (K g) * φ g) μG) :
    Integrable (fun q => centralProjection μA χ φ q.out * conj (K q.out)) ν :=
  (integrable_integral_out hA hν hint).congr
    (Filter.Eventually.of_forall fun q => integral_conj_mul_mul_left hχ hK q.out)

include hA in
/-- **Positivity of `(p_χ φ, p_χ φ)_{A\G}`**: if `p_χ φ` is continuous and orthogonal to `φ`
on `G`, then `p_χ φ = 0`. -/
theorem centralProjection_eq_zero_of_mem_pairingAnnihilator [MeasurableMul A]
    (hν : IsCompatible A μG μA ν) (hχ : IsUnitaryCharacter χ)
    {φ : G → ℂ} (hcont : Continuous (centralProjection μA χ φ))
    (hmem : centralProjection μA χ φ ∈ pairingAnnihilator μG φ) :
    centralProjection μA χ φ = 0 := by
  have : ν.IsOpenPosMeasure := hν.isOpenPosMeasure
  set P := centralProjection μA χ φ with hP
  have hK : ∀ (a : A) (g : G), P ((a : G) * g) = χ a * P g := centralProjection_mul_left φ
  have hinv : ∀ (a : A) (g : G), ‖P ((a : G) * g)‖ ^ 2 = ‖P g‖ ^ 2 := fun a g => by
    rw [hK, norm_mul, hχ.norm_eq_one, one_mul]
  let F : LeftQuotient A → ℝ := descend A (fun g => ‖P g‖ ^ 2) hinv
  have hFc : Continuous F := (hcont.norm.pow 2).quotient_lift _
  have hFout : ∀ q, F q = ‖P q.out‖ ^ 2 := fun q => by
    conv_lhs => rw [← Quotient.out_eq q]
    rfl
  have hint := integrable_centralProjection_mul_conj hA hν hχ hK hmem.1
  have hFint : Integrable F ν := hint.norm.congr (Filter.Eventually.of_forall fun q => by
    simp only [hFout, norm_mul, Complex.norm_conj, sq]
    rfl)
  have hI : ∫ q, F q ∂ν = 0 := by
    have h1 := integral_centralProjection_mul_conj hA hν hχ hK hmem.1
    have h3 : ((∫ q, F q ∂ν : ℝ) : ℂ) = ∫ q, P q.out * conj (P q.out) ∂ν := by
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
      simp only [hFout, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    exact_mod_cast h3.trans (h1.trans hmem.2)
  have hae : F =ᵐ[ν] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun q => by rw [Pi.zero_apply, hFout]; positivity)
      hFint).mp hI
  have hF0 : F = 0 := (hFc.ae_eq_iff_eq ν continuous_const).mp hae
  funext g
  have h := congrFun hF0 (Quotient.mk _ g)
  change ‖P g‖ ^ 2 = 0 at h
  simpa using h

include hA in
/-- **End of the proof of Theorem VIII.1.1** (Waldspurger, VIII.5), abstract form: let `ρ` be a
smooth representation with an invariant positive form `b` and `p` a class of subrepresentations
`S`, each admissible with tempered coefficients and with `π_S(ˇφ) = 0`. If `p_χ φ` lies in the
span `Σ_S A(S)` of their coefficient spaces (for Waldspurger, Theorem VIII.4.2 with
`p = irreducible, square integrable modulo A_G, with central character χ`), then `p_χ φ = 0`. -/
theorem centralProjection_eq_zero_of_schwartzAction_eq_zero [MeasurableMul A]
    [Nonempty (CompactOpenSubgroup G)] [μG.IsMulLeftInvariant] [μG.IsInvInvariant]
    (hAc : A ≤ Subgroup.center G) (hν : IsCompatible A μG μA ν)
    (hχ : IsUnitaryCharacter χ) {Ξ σ : G → ℝ} (hw : L2Weights μG Ξ σ)
    (hΞ : ∀ g, Ξ g⁻¹ = Ξ g) (hσ : ∀ g, σ g⁻¹ = σ g)
    {V : Type v} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (b : InvariantPositiveForm ρ) (hs : IsSmooth ρ) {p : Subrepresentation ρ → Prop}
    (φ : Space Ξ σ)
    (hS : ∀ S, p S → ∃ (hSa : IsAdmissible S.toRepresentation)
      (hT : HasTemperedCoefficients Ξ σ S.toRepresentation),
      schwartzAction hw hSa hT (Space.check hΞ hσ φ) = 0)
    (hmem : ∃ c ∈ subrepresentationCoefficientSpace hs p, ⇑c = centralProjection μA χ φ) :
    centralProjection μA χ φ = 0 := by
  obtain ⟨c, hc, hcφ⟩ := hmem
  have hmem' : centralProjection μA χ φ ∈ pairingAnnihilator μG φ := by
    rw [← hcφ]
    exact subrepresentationCoefficientSpace_le hw hΞ hσ b hs hS ⟨c, hc, rfl⟩
  have hcont : Continuous (centralProjection μA χ φ) := by
    obtain ⟨K, hK⟩ := (mem_schwartzSubmodule_iff Ξ σ).mp (Space.coe_mem φ)
    exact (IsBiInvariant.isLocallyConstant
      (hK.1.centralProjection (μA := μA) hAc χ)).continuous
  exact centralProjection_eq_zero_of_mem_pairingAnnihilator hA hν hχ hcont hmem'

end Quotient

end Langlands.HarishChandraSchwartz

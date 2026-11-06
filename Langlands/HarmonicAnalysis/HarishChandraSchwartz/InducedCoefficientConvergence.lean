import Langlands.HarmonicAnalysis.HarishChandraSchwartz.InducedCoefficientXi
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.TemperedPairing

/-! # Absolute convergence in the proof of Waldspurger's Lemma VII.1.2

Waldspurger, proof of Lemma VII.1.2 (printed p. 315): for `v ∈ I_P^G E`, `v̌ ∈ I_P^G Ě` and
`f ∈ C(G)`, "Il résulte de la preuve du Lemme VI.2.2 et du Lemme II.1.5 que cette dernière
intégrale est absolument convergente", for the integral
`∫_G ∫_{P\G} conj⟨v(hg), v̌(h)⟩ f(g) dh dg`.

Here the integral over `P\G` is the integral over `K` with its Haar probability, as in
`CompactInduction.coefficientMap`, and `v ⊗ v̌` is any `ψ ∈ L(ω, P)`. The integrand is
`coefficientPairingIntegrand`. Its integrability, `integrable_coefficientPairingIntegrand`,
follows the indicated route: the pointwise bound `norm_inducedIntegrandKernel_le` of the proof of
Lemma VI.2.2, `∫_K δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g)) dk = Ξ(g)` (Lemma II.1.6,
`LeviData.xi_eq_integral`), and `∫_G Ξ |f| < ∞` (Lemma II.1.5, as `L2Weights`). This is the
hypothesis `hint` of `inducedFourierTransform_eq_constantTermInducedFourierTransform` for
`Ξ = xi`.
-/

noncomputable section

open MeasureTheory Langlands.Aubert.General Langlands.Plancherel
open scoped ComplexConjugate NNReal ENNReal

namespace Langlands.HarishChandraSchwartz

universe uG uV

section Weight

/-- `ν_0(Ξ) ≤ 1`: the weight `Ξ` itself has finite seminorm `ν_0`. -/
theorem nu_zero_ofReal_le_one {X : Type*} {Ξ σ : X → ℝ} (hΞ : ∀ g, 0 < Ξ g) :
    nu Ξ σ (-0) (fun g => ((Ξ g : ℝ) : ℂ)) ≤ 1 := by
  refine iSup_le fun g => ?_
  rw [weight, neg_zero, Real.rpow_zero, mul_one, ← ofReal_norm,
    Complex.norm_of_nonneg (hΞ g).le, ← ENNReal.ofReal_mul (hΞ g).le,
    mul_inv_cancel₀ (hΞ g).ne', ENNReal.ofReal_one]

end Weight

section Convergence

variable {G : Type uG} [Group G] [TopologicalSpace G]
  [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  (A : SmoothRep.{0, uG, uV} ℂ M) (K : OpenSubgroup G)
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (hK : IsCompact (K : Set G))
  {P₀ : Subgroup G} {δ₀ : P₀ →* ℝ≥0ˣ} {δ₀M : P₀.subgroupOf M →* ℝ≥0ˣ}
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)]

omit [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The integrand `(g, k) ↦ ⟨ψ(k g, k)⟩` of the coefficient map is continuous on `G × K`. -/
theorem continuous_integrand_uncurry (F : productInducedCoefficientObject h hU A) :
    Continuous (fun x : G × K => CompactInduction.integrand h hU A K x.1 F x.2) :=
  (((Induction.eval_isLocallyConstant (P.prod P)
    (inducingRepresentation (h.prod h) (hU.prod hU) (productLeviObject A A.contragredient)) F).comp
      (TensorProduct.lift (smoothDualPairing A.representation).flip)).comp_continuous
    (((continuous_subtype_val.comp continuous_snd).mul continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd))).continuous

omit [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  [CompactSpace (K : Subgroup G)] [CompactSpace ((K : Subgroup G).subgroupOf M)] in
/-- The integrand `(g, k) ↦ conj⟨ψ(k g, k)⟩ f(g)` of the double integral
`∫_G ∫_K conj⟨ψ(k g, k)⟩ f(g) dk dg` in the proof of Waldspurger's Lemma VII.1.2, where
`⟨ψ(k g, k)⟩ = CompactInduction.integrand h hU A K g ψ k` is the pairing of the value of
`ψ ∈ L(ω, P)` at `(k g, k)`. -/
def coefficientPairingIntegrand (ψ : productInducedCoefficientObject h hU A) (f : G → ℂ)
    (x : G × K) : ℂ :=
  conj (CompactInduction.integrand h hU A K x.1 ψ x.2) * f x.1

include hK in
omit [T2Space G] in
/-- `∫_K δ_P(m_P(k g))^{1/2} Ξ^M(m_P(k g)) dk = Ξ(g)` (Lemma II.1.6), as a lower integral against
the Haar probability `CompactInduction.measure K hK`. -/
theorem lintegral_leviXiWeight_mul
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1) {C : ℝ} (hC : 0 < C) (g : G) :
    ∫⁻ k, ENNReal.ofReal (C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M ((k : G) * g))
        ∂CompactInduction.measure K hK =
      ENNReal.ofReal (C * xi hP₀K δ₀ g) := by
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hxi := hL.xi_eq_integral K.isOpen hP₀K hMK hδ₀ g
  have hint : Integrable (fun k : (K : Subgroup G) =>
      leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M ((k : G) * g))
      (normalizedHaar (K : Subgroup G)) := by
    apply Integrable.of_integral_ne_zero
    change (∫ k : (K : Subgroup G), NNReal.sqrt
        (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer
          (leviComponent (hP₀K.mono hL.le_P₀) h.projection ((k : G) * g)) : ℝ≥0) *
        xi hMK δ₀M (leviComponent (hP₀K.mono hL.le_P₀) h.projection ((k : G) * g))
          ∂(normalizedHaar (K : Subgroup G))) ≠ 0
    rw [← hxi]
    exact (xi_pos hδ₀ K.isOpen g).ne'
  have hnn : ∀ x : G, 0 ≤ C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M x := fun x =>
    mul_nonneg hC.le (mul_nonneg (NNReal.coe_nonneg _)
      (integral_nonneg fun _ => iwasawaWeight_nonneg _))
  rw [CompactInduction.measure_eq_normalizedHaar K hK]
  refine (ofReal_integral_eq_lintegral_ofReal (hint.const_mul C)
    (Filter.Eventually.of_forall fun k => hnn _)).symm.trans ?_
  rw [integral_const_mul]
  congr 2
  exact hxi.symm

include hK in
omit [T2Space G] in
/-- **Absolute convergence in the proof of Lemma VII.1.2** (from the proof of Lemma VI.2.2 and
Lemma II.1.5): for `ψ ∈ L(ω, P)` and `f ∈ C(G)`, with `Ξ` the spherical function `xi hP₀K δ₀`
and Corollary III.1.2 for `M` (hypothesis `hcoeff`), the function
`(g, k) ↦ conj⟨ψ(k g, k)⟩ f(g)` is integrable on `G × K`. -/
theorem integrable_coefficientPairingIntegrand [Nonempty (CompactOpenSubgroup G)]
    (hδ : IsUnimodularModulus U hU)
    (hL : LeviData (K : Subgroup G) P₀ P M δ₀
      (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) δ₀M h.projection)
    (hP₀K : IsIwasawaPair P₀ (K : Subgroup G))
    (hMK : IsIwasawaPair (P₀.subgroupOf M) ((K : Subgroup G).subgroupOf M))
    (hδ₀ : ∀ p : P₀, (p : G) ∈ K → δ₀ p = 1)
    (hcoeff : ∀ (v : A) (ℓ : SmoothDual A.representation),
      ∃ C : ℝ, 0 < C ∧ ∀ m, ‖ℓ.val (A.representation m v)‖ ≤ C * xi hMK δ₀M m)
    {μ : Measure G} [SFinite μ] {σ : G → ℝ} (hw : L2Weights μ (xi hP₀K δ₀) σ)
    (F : productInducedCoefficientObject h hU A) (f : Space (xi hP₀K δ₀) σ) :
    Integrable (coefficientPairingIntegrand h hU A K F f)
      (μ.prod (CompactInduction.measure K hK)) := by
  obtain ⟨C, hC, hb⟩ := norm_inducedIntegrandKernel_le h hU A K hK hδ hL hP₀K hMK hcoeff F
  have : SecondCountableTopology K := TopologicalSpace.Subtype.secondCountableTopology _
  refine ⟨((Complex.continuous_conj.comp (continuous_integrand_uncurry h hU A K F)).mul
    ((Space.continuous f).comp continuous_fst)).aestronglyMeasurable, ?_⟩
  have hpt : ∀ x : G × K,
      ‖coefficientPairingIntegrand h hU A K F f x‖ₑ ≤
        ENNReal.ofReal (C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
          (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M
            ((x.2 : G) * x.1)) * ‖f x.1‖ₑ := by
    intro x
    rw [coefficientPairingIntegrand, enorm_mul, RCLike.enorm_conj,
      ← inducedIntegrandKernel_mul h hU A K F x.2 x.1, ← ofReal_norm]
    gcongr
    exact hb x.2 _
  have hfin : ∫⁻ g, ‖f g * ((xi hP₀K δ₀ g : ℝ) : ℂ)‖ₑ ∂μ < ⊤ :=
    (Space.integrable_mul hw (Complex.continuous_ofReal.comp (continuous_xi hδ₀ K.isOpen))
      (r := 0) ((nu_zero_ofReal_le_one hw.pos).trans_lt ENNReal.one_lt_top).ne f).2
  calc ∫⁻ x, ‖coefficientPairingIntegrand h hU A K F f x‖ₑ
        ∂μ.prod (CompactInduction.measure K hK)
      ≤ ∫⁻ x, ENNReal.ofReal (C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
          (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M
            ((x.2 : G) * x.1)) * ‖f x.1‖ₑ ∂μ.prod (CompactInduction.measure K hK) :=
        lintegral_mono hpt
    _ ≤ ∫⁻ g, ∫⁻ k, ENNReal.ofReal (C * leviXiWeight (hP₀K.mono hL.le_P₀) h.projection
          (HaarModulus.closedRestrictCharacter U hU M h.levi_le_normalizer) hMK δ₀M
            ((k : G) * g)) * ‖f g‖ₑ ∂CompactInduction.measure K hK ∂μ :=
        lintegral_prod_le _
    _ = ∫⁻ g, ENNReal.ofReal C * ‖f g * ((xi hP₀K δ₀ g : ℝ) : ℂ)‖ₑ ∂μ := by
        refine lintegral_congr fun g => ?_
        rw [lintegral_mul_const' _ _ enorm_ne_top,
          lintegral_leviXiWeight_mul h hU K hK hL hP₀K hMK hδ₀ hC g, enorm_mul,
          ← ofReal_norm (((xi hP₀K δ₀ g : ℝ) : ℂ)),
          Complex.norm_of_nonneg (xi_pos hδ₀ K.isOpen g).le, ENNReal.ofReal_mul hC.le]
        ring
    _ < ⊤ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end Convergence

end Langlands.HarishChandraSchwartz
